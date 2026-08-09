import subprocess
from pathlib import Path

import pytest

PROPERTY_DIR = Path(__file__).resolve().parent
REPO_ROOT = PROPERTY_DIR.parent.parent
CLI_DIR = REPO_ROOT / "cli"

AST_DRIVER = PROPERTY_DIR / "ast_driver"
VOBLINT = CLI_DIR / "voblint"


@pytest.fixture(scope="session", autouse=True)
def built_binaries():
    subprocess.run(["make", "-C", str(PROPERTY_DIR)], check=True, capture_output=True)
    subprocess.run(["make", "-C", str(CLI_DIR)], check=True, capture_output=True)
