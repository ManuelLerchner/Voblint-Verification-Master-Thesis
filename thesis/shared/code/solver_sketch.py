INF = float("inf")
Interval = tuple[float, float] | None  # bounds (l, u); None is the empty interval


def join(a: Interval, b: Interval) -> Interval:
    if a is None or b is None:
        return b if a is None else a
    return (min(a[0], b[0]), max(a[1], b[1]))


def meet(a: Interval, b: Interval) -> Interval:
    if a is None or b is None or max(a[0], b[0]) > min(a[1], b[1]):
        return None
    return (max(a[0], b[0]), min(a[1], b[1]))


def add(a: Interval, c: float) -> Interval:
    return None if a is None else (a[0] + c, a[1] + c)


def leq(a: Interval, b: Interval) -> bool:  # a lies inside b
    return a is None or (b is not None and b[0] <= a[0] and a[1] <= b[1])


def widen(a: Interval, b: Interval) -> Interval:  # an unstable bound jumps to ∞
    if a is None or b is None:
        return join(a, b)
    return (a[0] if a[0] <= b[0] else -INF, a[1] if b[1] <= a[1] else INF)


def narrow(a: Interval, b: Interval) -> Interval:  # refines only infinite bounds
    if a is None or b is None:
        return b
    return (b[0] if a[0] == -INF else a[0], b[1] if a[1] == INF else a[1])


def warrow(a: Interval, b: Interval) -> Interval:  # narrow if b lies below a
    return narrow(a, b) if leq(b, a) else widen(a, b)


def solve(rhs: dict, update, sigma: dict[str, Interval]) -> dict[str, Interval]:
    """Round robin: update every unknown with its right-hand side until stable."""
    changed = True
    while changed:
        changed = False
        for x, f in rhs.items():
            new = update(sigma[x], f(sigma))
            if new != sigma[x]:
                sigma[x], changed = new, True
    return sigma


rhs = {
    "x": lambda s: join((0, 0), meet(s["y"], (-INF, 5))),
    "y": lambda s: join(meet(s["x"], (-INF, 9)), add(meet(s["y"], (-INF, 5)), 2)),
}
bottom = {"x": None, "y": None}
phased = solve(rhs, narrow, solve(rhs, widen, dict(bottom)))
warrowed = solve(rhs, warrow, dict(bottom))
print(phased)    # {'x': (0, 5), 'y': (0, 7)} the least solution
print(warrowed)  # {'x': (0, 5), 'y': (0, 9)}
