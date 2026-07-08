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


def solve_widening(T, points, global_keys, dom, vars, verbose: bool = False,
                   max_rounds: int = 1000):
    """Post-fixpoint by ascending iteration with *widening* on every slot --- the
    monovariant analogue of the vendored Apinis warrowing rule.  `new = old widen
    (old join rhs)` climbs and then jumps unstable interval ends to +/-inf, so it
    terminates even on an infinite-height domain.  Returns (sigma, iterations)."""
    sigma = {L(v): bot_state(dom, vars) for v in points}
    sigma |= {R(g): bot_state(dom, vars) for g in global_keys}

    it = 0
    while it < max_rounds:
        it += 1
        new = dict(sigma)
        for v in sorted(points):
            t = T(v)
            cur = new[L(v)]
            new[L(v)] = cur.widen(cur.join(traverse_rhs(t, sigma, dom, vars)))
            for key, d in sides_of_rhs(t, sigma, dom, vars).items():
                base = new.get(key, bot_state(dom, vars))
                new[key] = base.widen(base.join(d))
        if verbose:
            print(f"  round {it}: " +
                  " ".join(f"{k[1]}={new[k].show()}" for k in new if k[0] == 'L'))
        if all(new[k] == sigma[k] for k in new):
            return new, it
        sigma = new
    return sigma, it
