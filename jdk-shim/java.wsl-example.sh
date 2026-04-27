#!/usr/bin/env bash
# Example: WSL delegating to Windows JDK bundled with Isabelle (edit JAVA_EXE).

set -euo pipefail

# Example paths — replace with your install:
# JAVA_EXE=/mnt/c/Users/YOU/AppData/.../Isabelle2025-2/contrib/jdk-*/bin/java.exe
JAVA_EXE="/mnt/c/Users/YOU/Isabelle2025-2/contrib/jdk-21.0.3+x86_64-windows/bin/java.exe"

exec "$JAVA_EXE" "$@"
