from dsl import *
import itertools

PRINT_HISTORIES = False

ps = list(players('A', 'I', 'B'))
S_H, U, J, I_L, I_U, I_S = actions('S_H', 'U', 'J', 'I_L', 'I_U', 'I_S')
epsilon, rho = infinitesimals('epsilon', 'rho')
m, f = constants('m', 'f')

initial_constraints(
    rho > 0,
    epsilon > 0,
    f > 0,
    m > 0
)

weak_immunity_constraints()
collusion_resilience_constraints()
practicality_constraints()

recursion_depth = 0

actions_for_sharing_secrets = set()
actions_for_locking = set()
constants_for_wrong_amounts = set()


def secret_sharing_sets(secrets_to_share: Dict[Player, List[Player]]):
    powersets = []
    for key in secrets_to_share:
        powerset = [subset
                    for length in range(len(secrets_to_share[key]) + 1)
                    for subset in itertools.combinations(secrets_to_share[key], length)]
        powersets.append(powerset)
    for ll in itertools.product(*powersets):
        yield ll


def prev_player(player):
    i = ps.index(player)
    return ps[i-1]


def player_plus_one(player):
    i = ps.index(player)
    ii = (i + 1) % len(ps)
    return ps[ii]


def next_players(player, state):
    i = state["time_orderings"].index(player)
    return state["time_orderings"][:i]


def final(state):
    for p in ps:
        if state[p]["contract"] == "locked":
            return False
    for p in ps:
        if state[p]["contract"] == "kaput":
            state[p]["contract"] = "expired"
    return True


def utility_leaf(state):
    ut = {player: 0 for player in ps}
    for player in ps:
        if player == ps[-1]:
            if state[player]["contract"] == "unlocked":
                ut[player] = ut[player] + rho
                ut[prev_player(player)] = ut[prev_player(player)] - state[player]["amount_to_unlock"]
                ut[ps[0]] = ut[ps[0]] + rho + state[ps[1]]["amount_to_unlock"]
            elif state[player]["contract"] == "expired":
                ut[prev_player(player)] = ut[prev_player(player)] - epsilon

        else:
            if state[player]["contract"] == "unlocked":
                ut[player] = ut[player] + state[player]["amount_to_unlock"]
                ut[prev_player(player)] = ut[prev_player(player)] - state[player]["amount_to_unlock"]
            elif state[player]["contract"] == "expired":
                ut[prev_player(player)] = ut[prev_player(player)] - epsilon
    return ut


def copy_state(state):
    state1 = {}
    state1["time_orderings"] = state["time_orderings"][:]
    state1["eq_secrets"] = [[p for p in s] for s in state["eq_secrets"]]
    for player in ps:
        state1[player] = {}
        state1[player]["contract"] = state[player]["contract"]
        state1[player]["amount_to_unlock"] = state[player]["amount_to_unlock"]
        state1[player]["secrets"] = {p: state[player]["secrets"][p] for p in ps}
        state1[player]["ignoreshare"] = {p: state[player]["ignoreshare"][p] for p in ps}
    return state1


def players_who_can_unlock(state):
    knowers = set()
    for p in ps:
        if state[p]["secrets"][prev_player(p)]:
            if state[p]["contract"] == "locked":
                knowers.add(p)
    return knowers


def next_player(state):
    next_p = None
    state2 = copy_state(state)
    candidates = players_who_can_unlock(state)
    if candidates:
        for p in state["time_orderings"]:
            if p in candidates:
                next_p = p
                break
        return next_p, state2
    for p in state["time_orderings"]:
        secrets_p_knows = {pl for pl in ps if state[p]["secrets"][pl]}
        secrets_to_share = secrets_p_knows - {pl for pl in ps if state[p]["ignoreshare"][pl]}
        secrets_to_share = remove_pointless_sharing(state, list(secrets_to_share))
        sharing_dict = {s: [] for s in secrets_to_share}
        for secret in secrets_to_share:
            for player in set(ps) - {p}:
                if not state[player]["secrets"][secret]:
                    sharing_dict[secret].append(player)
                    next_p = p
        if next_p is not None:
            break
    if next_p is None:
        for p in ps:
            if state2[p]["contract"] == "locked":
                state2[p]["contract"] = "expired"
    return next_p, state2


def share_secret_action(sharing_instance):
    # Actions for sharing secrets: S_S_[[],[],[A, B], [], [E1]]
    return Action(f"S_S{sharing_instance}")


def align_secret_knowledge(state):
    def update_dict(d, eq_classes):
        for eq_class in eq_classes:
            tmp = [d[p] for p in d if p in eq_class]
            if any(tmp):
                for p in eq_class:
                    d[p] = True
    for player in ps:
        update_dict(state[player]["secrets"], state["eq_secrets"])
        update_dict(state[player]["ignoreshare"], state["eq_secrets"])


def recognise_kaput(state):
    # recognise which contracts are kaput
    for i in range(len(ps)-1):
        player = ps[i]
        flag = False
        for p in ps:
            if state[p]["secrets"][player]:
                flag = True
                break
        if not flag:
            state[ps[i+1]]["contract"] = "kaput"


def remove_pointless_sharing(state, secrets_to_share_representatives):
    # secrets of contracts that are unlocked or expired are pointless to share
    useful = []
    for eq_class in state["eq_secrets"]:
        if eq_class[0] in secrets_to_share_representatives:
            for secret in eq_class:
                i = ps.index(secret)
                if not i == len(ps)-1 and state[ps[i+1]]["contract"] == "locked":
                    useful.append(eq_class[0])
                    break
    return useful


def generate_routing_unlocking(player: Player, state, history):
    if PRINT_HISTORIES:
        print(history)
    # print(player)
    # print(state)
    # we can assume that current player p knows the secret.
    # initially B knows and always next player knows.
    global recursion_depth
    depth = len(history.split(";"))
    if depth > recursion_depth:
        recursion_depth = depth
    if final(state):
        return leaf(utility_leaf(state))
    else:
        # if all(state[player]["ignoreshare"].values()):
        #     raise Exception(f"It should not be player {player}'s turn, because they have ignored sharing secrets.")
        branch_actions = {}
        # Sharing is caring
        secrets_player_knows = {pl for pl in ps if state[player]["secrets"][pl]}
        secrets_to_share = secrets_player_knows - {pl for pl in ps if state[player]["ignoreshare"][pl]}
        secrets_to_share_representatives = []
        for eq_class in state["eq_secrets"]:
            if eq_class[0] in secrets_to_share:
                secrets_to_share_representatives.append(eq_class[0])
        secrets_to_share_representatives = remove_pointless_sharing(state, secrets_to_share_representatives)
        if history:
            pprev_player, prev_action = history[:-1].split(";")[-1].split(".")
        else:
            pprev_player = None
            prev_action = None
        if pprev_player != str(player) or "S_S" not in prev_action:
            sharing_dict = {s: [] for s in ps}
            for secret in secrets_to_share_representatives:
                for p in set(ps) - {player}:
                    if not state[p]["secrets"][secret]:
                        sharing_dict[secret].append(p)
            for sharing_instance in secret_sharing_sets(sharing_dict):
                state1 = copy_state(state)
                for i in range(len(ps)):
                    for person in sharing_instance[i]:
                            state1[person]["secrets"][ps[i]] = True
                    if state1[player]["secrets"][ps[i]]:
                            state1[player]["ignoreshare"][ps[i]] = True
                align_secret_knowledge(state1)
                next_p, state2 = next_player(state1)
                actions_for_sharing_secrets.add(f"S_S{sharing_instance}")
                branch_actions[share_secret_action(sharing_instance)] = generate_routing_unlocking(next_p, state2, history + str(player) + "." + str(share_secret_action(sharing_instance)) + ";")
        if state[player]["contract"] == "locked" and state[player]["secrets"][prev_player(player)]:
            # Action unlock
            state1 = copy_state(state)
            state1[player]["contract"] = "unlocked"
            state1[prev_player(player)]["secrets"][prev_player(player)] = True
            align_secret_knowledge(state1)
            next_p, state2 = next_player(state1)
            branch_actions[U] = generate_routing_unlocking(next_p, state2, history + str(player) + ".U;")
            # Ignoring unlock
            state3 = copy_state(state)
            state3[player]["contract"] = "expired"
            for p in next_players(player, state):
                if state[p]["contract"] == "locked":
                    state3[p]["contract"] = "expired"
            # the next player is the rightmost one who knows the secret and has not ignored sharing with everyone who doesn't know
            next_p, state4 = next_player(state3)
            branch_actions[I_U] = generate_routing_unlocking(next_p, state4, history + str(player) + ".I_U;")

        #imlpied by empty sharing_instance
        # else:
        #     # Ignoring sharing
        #     state1 = copy_state(state)
        #     for secret in secrets_to_share:
        #         state1[player]["ignoreshare"][secret] = True
        #     next_p, state2 = next_player(state1)
        #     branch_actions[I_S] = generate_routing_unlocking(next_p, state2, history + str(player) + ".I_S;")
        if not branch_actions:
            raise Exception("Empty branch, next player chosen wrong")
        return branch(player, branch_actions)

# state[p] = [<state of the contract>,<knowledge of secrets>,<igoresharing secrets>,<equivalence classes of secrets>]
# secrets are represented by players who wrote the HTCL contract with this hash
# ignoresharing with key p, means not sharing the secret that p used to lock their contract with anyone


def locking_action(deviator, slot, eq_class):
    return f"L_({deviator},{slot},{eq_class})"


def generate_routing_locking(player, state, deviator, history):
    if PRINT_HISTORIES:
        print(history)
    branch_actions = {}

    def aux_locking(player, new_state, deviator, history):
        # time orderings
        positions = [i for i in range(len(ps)) if state["time_orderings"][i] is None]
        for i in positions:
            new_state1 = copy_state(new_state)
            new_state1["time_orderings"][i] = player
            # eq classes of secrets
            for j in range(len(state["eq_secrets"])):
                new_state2 = copy_state(new_state1)
                new_state2["eq_secrets"][j].append(player)
                new_state2[player_plus_one(player)]["contract"] = "locked"
                action = locking_action(deviator, i, new_state2["eq_secrets"][j])
                actions_for_locking.add(action)
                if player == ps[-2]:
                    align_secret_knowledge(new_state2)
                    if new_state2["time_orderings"].count(None) != 1:
                        raise Exception("Locking phase went wrong, there are several or zero positions unspecified in time orderings")
                    else:
                        position = new_state2["time_orderings"].index(None)
                        new_state2["time_orderings"][position] = ps[-1]
                    branch_actions[Action(action)] = generate_routing_unlocking(ps[-1], new_state2, history + str(player) + f".{action};")
                else:
                    branch_actions[Action(action)] = generate_routing_locking(player_plus_one(player), new_state2, deviator, history + str(player) + f".{action};")
            # I am my own eq class therefore I know my own secret
            new_state1["eq_secrets"].append([player])
            new_state1[player]["secrets"][player] = True
            new_state1[player_plus_one(player)]["contract"] = "locked"
            action = locking_action(deviator, i, new_state1["eq_secrets"][-1])
            actions_for_locking.add(action)
            if player == ps[-2]:
                align_secret_knowledge(new_state1)
                # print(history + str(player) + f".{action};")
                if new_state1["time_orderings"].count(None) != 1:
                    raise Exception("Locking phase went wrong, there are several or zero positions unspecified in time orderings")
                else:
                    position = new_state1["time_orderings"].index(None)
                    new_state1["time_orderings"][position] = ps[-1]
                branch_actions[Action(action)] = generate_routing_unlocking(ps[-1], new_state1, history + str(player) + f".{action};")
            else:
                branch_actions[Action(action)] = generate_routing_locking(player_plus_one(player), new_state1, deviator, history + str(player) + f".{action};")

    if deviator is None:
        # case honest amount
        state1 = copy_state(state)
        i = ps.index(player)
        state1[ps[i+1]]["amount_to_unlock"] = m + (len(ps) - 2 - i) * f
        aux_locking(player, state1, deviator, history)
        deviator = player
    # case dishonest amount
    state2 = copy_state(state)
    i = ps.index(player)
    state2[ps[i+1]]["amount_to_unlock"] = NameExpr(f"a_{deviator}_{player}")
    constants_for_wrong_amounts.add(f"a_{deviator}_{player}")
    aux_locking(player, state2, deviator, history)
    # case ignore locking
    ut = {}
    for j in range(len(ps)):
        if j < i:
            ut[ps[j]] = - epsilon
        else:
            ut[ps[j]] = 0
    branch_actions[I_L] = leaf(ut)
    if PRINT_HISTORIES:
        print(history + str(player) + f".I_L;")
    return branch(player, branch_actions)


initial_state = {
    "eq_secrets": [[ps[-1]]],
    "time_orderings": [None for _ in ps]
    }
for player in ps:
    initial_state[player] = {}
    initial_state[player]["contract"] = "null"
    initial_state[player]["amount_to_unlock"] = None
    initial_state[player]["secrets"] = {p: False for p in ps}
    initial_state[player]["ignoreshare"] = {p: False for p in ps}
initial_state[ps[-1]]["secrets"][ps[-1]] = True

honest = ["S_H"]
eq_cl = [ps[-1]]
for i in range(len(ps)-1):
    eq_cl.append(ps[i])
    honest.append(f"L_(None,{len(ps)-1-i},{eq_cl})")
for i in range(len(ps)-1):
    honest.append("U")

honest_histories(tuple([Action(a) for a in honest]))

locking_tree = generate_routing_locking(ps[0], initial_state, None, "")

routing_tree = branch(ps[-1], {
    J: leaf({p: 0 for p in ps}),
    S_H: locking_tree
})

for act in actions_for_sharing_secrets:
    ACTIONS.append(Action(act))

for act in actions_for_locking:
    ACTIONS.append(Action(act))

for const in constants_for_wrong_amounts:
    CONSTANTS.append(NameExpr(const))

### This part here is for debugging
intermediate_state = {
    "eq_secrets": [[p for p in ps]],
    "time_orderings": [ps[2], ps[1], ps[0]]
    }
for player in ps:
    intermediate_state[player] = {}
    intermediate_state[player]["contract"] = "null"
    intermediate_state[player]["amount_to_unlock"] = None
    intermediate_state[player]["secrets"] = {p: False for p in ps}
    intermediate_state[player]["ignoreshare"] = {p: False for p in ps}
intermediate_state[ps[2]]["secrets"][ps[-1]] = True
intermediate_state[ps[2]]["amount_to_unlock"] = m
intermediate_state[ps[2]]["contract"] = "locked"
intermediate_state[ps[1]]["amount_to_unlock"] = m + f
intermediate_state[ps[1]]["contract"] = "locked"
align_secret_knowledge(intermediate_state)

unlocking_tree = generate_routing_unlocking(ps[-1], intermediate_state, "")
### Debugging part finished

tree(routing_tree)

finish()
