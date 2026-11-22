#!/usr/bin/env python3
"""Copy the shared definitions of the library into the Challenges, or check the copies.

Comparator requires every constant that a Challenge statement uses to be the same in the Challenge
and in the Solution's environment. A Challenge may not import the library, so the definitions that
the Challenges need are marked blocks of a few modules of the library, each between

    -- BEGIN SHARED DEFINITIONS: <name>
    -- END SHARED DEFINITIONS: <name>

(without `: <name>` in a module with a single block), and this script copies the blocks of each
Challenge verbatim from those modules. A Challenge and the modules of its blocks must also import
exactly the same modules of Mathlib (so that the definitions elaborate in the same way in both),
which the script checks; with it, every Challenge declares the same definitions as the library.

Run from anywhere in the repository:

    python3 scripts/sync_challenge_defs.py           # rewrite the blocks in the Challenges
    python3 scripts/sync_challenge_defs.py --check   # exit 1 if a copy differs (for CI)
"""

import re
import sys
from pathlib import Path

# ---- configuration -------------------------------------------------------------------------
# The library modules that hold the shared definitions.
SCALAR = 'HarmonicAnalysis/Defs.lean'
VECTOR = 'HarmonicAnalysis/VectorValued/Defs.lean'
HARDY = 'HarmonicAnalysis/Hardy/Defs.lean'
# The blocks of each Challenge, in order, with their modules; `None` is the block without a name.
CHALLENGES = {
    'palomar/FourierMultipliers/Challenge.lean': [(SCALAR, None)],
    'palomar/VectorValuedLittlewoodPaley/Challenge.lean': [
        (VECTOR, 'umd'), (VECTOR, 'circle'), (VECTOR, 'rademacher'), (VECTOR, 'dyadic')],
    'palomar/HardyFactorization/Challenge.lean': [
        (VECTOR, 'circle'), (HARDY, 'hardyOne'), (HARDY, 'hardyTwo'), (HARDY, 'outer'),
        (HARDY, 'szego'), (HARDY, 'range'), (HARDY, 'schatten')],
    'palomar/PaleySchatten/Challenge.lean': [(HARDY, 'hardyOne'), (HARDY, 'schatten')],
}
# The root of the library: its modules are not counted among the imports of a module of definitions.
LIBRARY = 'HarmonicAnalysis'
BEGIN, END = '-- BEGIN SHARED DEFINITIONS', '-- END SHARED DEFINITIONS'
# ---------------------------------------------------------------------------------------------

ROOT = Path(__file__).resolve().parent.parent


def span(text: str, name: str, block: str | None) -> tuple[int, int]:
    """The span of a block in `text`, markers included."""
    suffix = '\n' if block is None else f': {block}\n'
    begin, end = BEGIN + suffix, END + suffix
    i, j = text.find(begin), text.find(end)
    if i < 0 or j < i or text.count(begin) != 1 or text.count(end) != 1:
        sys.exit(f'{name}: expected exactly one pair of markers for the block "{block}"')
    return i, j + len(end)


def imports(text: str) -> set[str]:
    """The modules outside the library that a file imports."""
    found = re.findall(r'^(?:public )?import (?:all )?(\S+)', text, re.M)
    return {m for m in found if m != LIBRARY and not m.startswith(LIBRARY + '.')}


def sync(chal_name: str, blocks: list[tuple[str, str | None]], check: bool) -> bool:
    """Copy (or, with `check`, compare) the blocks of one Challenge; return whether it was current."""
    path = ROOT / chal_name
    chal, current = path.read_text(), True
    found = re.findall(rf'^{BEGIN}(?:: (.*))?$', chal, re.M)
    if found != [block or '' for _, block in blocks]:
        sys.exit(f'{chal_name}: expected the blocks {blocks}, found {found}')
    for defs_name in dict.fromkeys(name for name, _ in blocks):
        defs = (ROOT / defs_name).read_text()
        if imports(chal) != imports(defs):
            print(f'{chal_name}: the imports differ from those of {defs_name}: '
                  f'{sorted(imports(chal) ^ imports(defs))}')
            current = False
    for defs_name, block in blocks:
        defs = (ROOT / defs_name).read_text()
        di, dj = span(defs, defs_name, block)
        ci, cj = span(chal, chal_name, block)
        if chal[ci:cj] != defs[di:dj]:
            current = False
            if check:
                print(f'{chal_name}: the block "{block}" differs from {defs_name}; '
                      f'run python3 scripts/sync_challenge_defs.py')
            chal = chal[:ci] + defs[di:dj] + chal[cj:]
    if not check:
        path.write_text(chal)
        print(f'{chal_name}: the shared definitions are copied')
    elif current:
        print(f'{chal_name}: the shared definitions and the imports match the library')
    return current


def main() -> None:
    args = sys.argv[1:]
    if args and args[0] in ('-h', '--help') or any(a != '--check' for a in args):
        print(__doc__.strip())
        sys.exit(0 if args and args[0] in ('-h', '--help') else 2)
    check = '--check' in args
    current = [sync(c, blocks, check) for c, blocks in CHALLENGES.items()]
    if check and not all(current):
        sys.exit(1)


if __name__ == '__main__':
    main()
