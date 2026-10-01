"""The solver sketch the Background chapter prints must compute what the text claims."""

import runpy
from pathlib import Path

SKETCH = (
    Path(__file__).resolve().parents[1]
    / "thesis"
    / "shared"
    / "code"
    / "solver_sketch.py"
)


def test_phased_and_warrowed_results(capsys):
    env = runpy.run_path(str(SKETCH))
    capsys.readouterr()
    assert env["phased"] == {"x": (0, 5), "y": (0, 7)}
    assert env["warrowed"] == {"x": (0, 5), "y": (0, 9)}


def test_warrowing_can_be_more_precise(capsys):
    """The second system the chapter states in prose, where warrowing wins."""
    env = runpy.run_path(str(SKETCH))
    capsys.readouterr()
    join, meet, add, inf = env["join"], env["meet"], env["add"], env["INF"]
    solve, widen, narrow, warrow = (
        env["solve"],
        env["widen"],
        env["narrow"],
        env["warrow"],
    )
    rhs = {
        "x": lambda s: add(meet(s["y"], (-inf, 10)), 2),
        "y": lambda s: join((0, 0), add(meet(s["y"], (0, 7)), 2)),
    }
    bottom = {"x": None, "y": None}
    phased = solve(rhs, narrow, solve(rhs, widen, dict(bottom)))
    warrowed = solve(rhs, warrow, dict(bottom))
    assert phased["x"] == (2, 12)
    assert warrowed["x"] == (2, 11)
