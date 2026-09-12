"""Read arithmetic table rows and compiler-style graph diagnostics."""

import re


def diagnostic_lines(output):
    path = analysis = None
    arithmetic = False
    for line in output.splitlines():
        heading = re.fullmatch(r"(.+) \[([^\]]+)\]", line)
        if heading:
            path, analysis = heading.groups()
        if line == "Arithmetic diagnostics":
            arithmetic = True
            continue
        if line == "Assertion checks":
            arithmetic = False
        row = re.fullmatch(r"(\d+):(\d+)\s+\S+\s+(ERROR|WARNING)\s+(.+)", line)
        if arithmetic and row and path:
            ln, col, severity, message = row.groups()
            yield f"{path}:{ln}:{col}: {severity.lower()}: {message} [{analysis}]"
        elif " by zero" in line:
            yield line
