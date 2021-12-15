from pathlib import Path
import sys

if __name__ == "__main__":
    for f in sys.argv:
        p = Path(f)
        if p.stat().st_size == 0:
            print(f"empty file {p}; remove before committing.")
            exit(1)
