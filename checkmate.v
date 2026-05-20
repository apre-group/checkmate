Require Import Reals.
Open Scope R_scope.

Module Type Player.
Parameter player : Set.
Parameter eqp : player -> player -> bool.
End Player.

Module CheckMate (P : Player).
Import P.

Definition utility : Set := R.

(* a finite, finitely-branching tree with utilities at leaves and players at branches *)
Inductive efg :=
  leaf : (player -> utility) -> efg
| branch : forall (A : Type), player -> (A -> efg) -> efg.

(* a joint strategy (assignment of choices to branches) for a given EFG *)
Inductive strategy : efg -> Type :=
  (* nil for leaves *)
  sleaf : forall {us}, strategy (leaf us)
  (* a choice and a strategy for each child at branches *)
| sbranch : forall {A p acts}, A -> (forall c, strategy (acts c)) -> strategy (branch A p acts).

(* merely the choice of action a given strategy takes at any branch in the tree *)
Definition choice {A p acts} (s : strategy (branch A p acts)) : A :=
match s with
| sbranch c substrategy => c
end. 

(* merely the rest of the strategy, a function from choices to a strategy for that choice *)
Definition substrategy {A p acts} (s : strategy (branch A p acts)) : forall c, strategy (acts c) :=
match s in strategy (branch n p acts) with
| sbranch _ substrategy => substrategy
end.

(* replace the choices of `from` with `to` where it is `p`'s turn *)
Fixpoint deviate {e : efg} (from : strategy e) (p : player) (to : strategy e) : strategy e :=
match e, from, to with
  leaf _, _, _ => sleaf
| branch _ q acts, _, _ => sbranch (if eqp p q then choice to else choice from)
    (fun chosen => deviate (substrategy from chosen) p (substrategy to chosen))
end.

(* the utility of a player under a given strategy *)
Fixpoint player_utility {e : efg} (p : player) (s : strategy e) : utility :=
match e, s with
  leaf us, _ => us p
| branch _ _ ts, _ => player_utility p (substrategy s (choice s))
end.

Definition weak_immune {e : efg} (s : strategy e) : Prop :=
  forall p s', player_utility p (deviate s p s') >= 0.

Arguments branch {A}.
End CheckMate.

(*************************************************************************************************)

Inductive MEplayer := N | E.

Module MEPlayer <: Player.
Definition player := MEplayer.
Definition eqp (p1 p2 : player) : bool := match p1, p2 with
| N, N => true
| E, E => true
| _, _ => false
end.
End MEPlayer.

Module CheckMateME := CheckMate MEPlayer.
Import CheckMateME.


Inductive Nactions := o | e.
Inductive Eactions := i | s.

Notation "{ a => t }" :=
  (fun x => match x with a => t end)
  (a pattern).
Notation "{ a => t | b => s }" :=
  (fun x => match x with a => t | b => s end)
  (a pattern, b pattern).

Definition market_entry (a p : utility) : efg := branch N {
  o => leaf { N => 0 | E => p * p }
| e => branch E { i => leaf { _ => -p } | s => leaf { _ => -a }}}.

