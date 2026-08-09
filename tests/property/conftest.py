import subprocess
from pathlib import Path

import pytest

PROPERTY_DIR = Path(__file__).resolve().parent
REPO_ROOT = PROPERTY_DIR.parent.parent
CLI_DIR = REPO_ROOT / "cli"
MK_DIR = REPO_ROOT / "scripts" / "mk"

AST_DRIVER = PROPERTY_DIR / "ast_driver"
VOBLINT = CLI_DIR / "voblint"


@pytest.fixture(scope="session", autouse=True)
def built_binaries():
    subprocess.run(["bash", str(MK_DIR / "cli-build.sh")], check=True, capture_output=True)
    subprocess.run(["bash", str(MK_DIR / "property-build.sh")], check=True, capture_output=True)
