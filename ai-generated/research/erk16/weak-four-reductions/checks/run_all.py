from pathlib import Path
from runpy import run_path

here = Path(__file__).resolve().parent
for name in ("check_crossing.py", "check_first_root_count.py", "check_exterior_secondary.py"):
    run_path(str(here / name), run_name="__main__")
