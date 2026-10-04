#!/usr/bin/env python3
"""Create a Lean problem draft without overwriting an existing file."""

import argparse
from pathlib import Path


# First competition years and the usual number of problems in each paper.
COMPETITIONS = {"IMO": (1959, 6), "APMO": (1989, 5),
                "BMO": (1984, 4), "JBMO": (1997, 4)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("competition", choices=COMPETITIONS)
    parser.add_argument("year", type=int)
    parser.add_argument("problem", type=int)
    args = parser.parse_args()
    first_year, count = COMPETITIONS[args.competition]
    if not first_year <= args.year <= 9999:
        parser.error(f"year must be between {first_year} and 9999")
    if not 1 <= args.problem <= count:
        parser.error(f"problem must be between 1 and {count}")

    root = Path(__file__).resolve().parent.parent
    content = (root / "templates" / "Problem.lean").read_text(encoding="utf-8")
    for key, value in {"COMPETITION": args.competition, "YEAR": args.year,
                       "PROBLEM": args.problem}.items():
        content = content.replace("{{" + key + "}}", str(value))
    destination = (root / "Olympiad" / "Problems" / args.competition
                   / f"Y{args.year}" / f"P{args.problem}.lean")
    try:
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open("x", encoding="utf-8") as output:
            output.write(content)
    except FileExistsError:
        parser.error(f"refusing to overwrite {destination}")
    except OSError as error:
        parser.error(str(error))
    print(destination)


if __name__ == "__main__":
    main()
