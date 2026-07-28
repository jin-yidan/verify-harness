"""Enable `python3 -m harness <cmd>` (verify / doctor). See harness/cli.py."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from harness.cli import main  # noqa: E402

if __name__ == "__main__":
    sys.exit(main())
