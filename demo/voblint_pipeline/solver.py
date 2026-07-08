"""A naive post-fixpoint solver + result read-back.

The real analyzer rides the vendored, verified top-down side solver TD.TD_side
(td_cfg_side_solver_eff, TD_Side_Eff_Interface.thy:20).  Here we compute a
post-fixpoint by plain ascending Kleene iteration: sigma is a post-solution iff
traverse_rhs(T v, sigma) <= sigma(Inl v) and sides_of_rhs(T v, sigma) <= sigma
everywhere (Constraint_System / Basics_side).  ANY post-fixpoint is sound; TD_side
is just an efficient way to reach one (it follows dep_aux to re-evaluate only what
changed).

side_env / glob_env : src/.../TD_Side_CFG.thy:93, Constraint_System.thy:525
"""
from __future__ import annotations
from .strategy_tree import L, R, traverse_rhs, sides_of_rhs
from .state import AbsState, bot_state


def glob_env(sigma: dict, global_keys, dom, vars) -> AbsState:
    """Constraint_System.thy:525 — join of all global slots."""
    acc = bot_state(dom, vars)
    for g in global_keys:
        acc = acc.join(sigma[R(g)])
    return acc


def side_env(sigma: dict, v, global_keys, dom, vars) -> AbsState:
    """TD_Side_CFG.thy:93 — local slot joined with the global environment."""
    return sigma[L(v)].join(glob_env(sigma, global_keys, dom, vars))


def solve(T, points, global_keys, dom, vars, verbose: bool = False, max_rounds: int = 1000):
    """Kleene-iterate T to a post-fixpoint.  Returns (sigma, iterations).

    Plain ascending join: on an *infinite-height* domain (Interval) a climbing
    value never stabilises, so `max_rounds` bounds the loop; a returned iteration
    count == max_rounds means it did not converge (use `solve_widening`)."""
    sigma = {L(v): bot_state(dom, vars) for v in points}
    sigma |= {R(g): bot_state(dom, vars) for g in global_keys}

    it = 0
    while it < max_rounds:
        it += 1
        new = dict(sigma)
        for v in sorted(points):
            t = T(v)
            new[L(v)] = new[L(v)].join(traverse_rhs(t, sigma, dom, vars))
            for key, d in sides_of_rhs(t, sigma, dom, vars).items():
                new[key] = new.get(key, bot_state(dom, vars)).join(d)
        if verbose:
            print(f"  round {it}: " +
                  " ".join(f"{k[1]}={new[k].show()}" for k in new if k[0] == 'L'))
        if all(new[k] == sigma[k] for k in new):
            return new, it
        sigma = new
    return sigma, it


def _widen_step(old, joined, bot):
    """Establish-then-widen: a slot's first (bottom -> non-bottom) value is taken by
    join; widening applies only once a value is established.  This is how the vendored
    TD Apinis solver behaves -- it never calls widen with a bottom left argument (a
    point is widened only on re-visits), and matters because widen(bot, b) = top for the
    exact `widen_ivl_core`."""
    return joined if old == bot else old.widen(joined)


def solve_widening(T, points, global_keys, dom, vars, verbose: bool = False,
                   max_rounds: int = 1000):
    """Post-fixpoint by ascending iteration with *widening* --- a naive monovariant
    stand-in for the vendored Apinis warrowing rule (it widens but, unlike warrowing,
    does not narrow; see the module note on the solver being a stand-in).  The domain
    `widen` is exact (`widen_ivl_core`); the *strategy* is what is simplified.  Returns
    (sigma, iterations)."""
    bot = bot_state(dom, vars)
    sigma = {L(v): bot for v in points}
    sigma |= {R(g): bot for g in global_keys}

    it = 0
    while it < max_rounds:
        it += 1
        new = dict(sigma)
        for v in sorted(points):
            t = T(v)
            cur = new[L(v)]
            new[L(v)] = _widen_step(cur, cur.join(traverse_rhs(t, sigma, dom, vars)), bot)
            for key, d in sides_of_rhs(t, sigma, dom, vars).items():
                base = new.get(key, bot)
                new[key] = _widen_step(base, base.join(d), bot)
        if verbose:
            print(f"  round {it}: " +
                  " ".join(f"{k[1]}={new[k].show()}" for k in new if k[0] == 'L'))
        if all(new[k] == sigma[k] for k in new):
            return new, it
        sigma = new
    return sigma, it
