import { test } from 'node:test';
import assert from 'node:assert/strict';
import { genGame, makeRng } from '../../html/src/gen_game.ts';
import type { TreeNode } from '../../html/src/game.ts';

test('the same seed gives the same game', () => {
    for (const seed of [0, 1, 42, 123456789])
        assert.deepEqual(genGame(seed), genGame(seed));
    assert.notDeepEqual(genGame(1), genGame(2));
});

test('the random numbers are in range', () => {
    const rng = makeRng(7);
    for (let i = 0; i < 1000; i++) {
        const r = rng.random(), n = rng.int(-3, 5);
        assert.ok(r >= 0 && r < 1);
        assert.ok(Number.isInteger(n) && n >= -3 && n <= 5);
    }
    assert.equal(new Set(rng.sample([1, 2, 3, 4], 3)).size, 3);
});

test('games are well-formed', () => {
    for (let seed = 0; seed < 300; seed++) {
        const g = genGame(seed);
        const used = new Set<string>();
        (function check(node: TreeNode) {
            if (node.utility) {
                assert.deepEqual(node.utility.map(u => u.player), g.players, `seed ${seed}`);
                return;
            }
            assert.ok(g.players.includes(node.player!), `seed ${seed}`);
            const actions = node.children!.map(c => c.action);
            assert.equal(new Set(actions).size, actions.length, `seed ${seed}: an action twice`);
            node.children!.forEach(c => { used.add(c.action); check(c.child); });
        })(g.tree);
        assert.ok([...used].every(a => g.actions!.includes(a)), `seed ${seed}`);
        assert.ok(g.honest_histories!.length > 0, `seed ${seed}`);
        for (const h of g.honest_histories!) {
            let node = g.tree;
            for (const a of h) node = node.children!.find(c => c.action === a)!.child;
            assert.ok(node.utility, `seed ${seed}: honest history ${h} does not end at a leaf`);
        }
    }
});
