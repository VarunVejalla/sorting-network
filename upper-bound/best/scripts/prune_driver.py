#!/usr/bin/env python3
"""Iteratively delete declarations that the headline theorems do not depend on.

Run from `upper-bound/best/` after `lake env lean scripts/usage.lean` (which writes
`scripts/data/decls.txt` and `edges.txt`) and with a clean, committed `AKS/` tree:

    python scripts/prune_driver.py

Each round: restore `AKS/` from git, delete every declaration marked `N` that is not in the keep
set, run `lake build`, and read the errors.
  * `Unknown identifier/constant X` or `Invalid field X`: some kept text mentions a declaration the
    proof graph did not see (typically a `simp only [X]` argument that acts by `rfl`); every
    declaration with that short name is added to the keep set.
  * any other error in a module (e.g. a parse error from a bad deletion range): the whole module is
    kept unpruned.
Stops when `lake build` succeeds; the working tree then holds the pruned sources (review with
`git diff`, then commit). `scripts/data/keep.txt` records the final keep set.
"""
import collections
import glob
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
NL = chr(10)
DATA = 'scripts/data'
STOP = re.compile(r'^\s*(variable|open|namespace|section|end|universe|set_option|'
                  r'noncomputable section|local |attribute|/-!|--|public section|@\[expose\])')


def short(n):
    n = re.sub(r'^_private\.[^0-9]*\.0\.', '', n)
    return n.split('.')[-1]


def load():
    rows = [l.split('|') for l in open(f'{DATA}/decls.txt', encoding='utf-8').read().split(NL) if l]
    return [[m, n, int(a), int(b), k] for m, n, a, b, k in rows]


def read(m):
    return open(m.replace('.', '/') + '.lean', encoding='utf-8').read().split(NL)


def textual_margin(D, minlen=3):
    """Mark `N` declarations whose short name occurs in the text of any kept declaration."""
    texts = {}

    def src(d):
        if d[0] not in texts:
            texts[d[0]] = read(d[0])
        return NL.join(texts[d[0]][d[2] - 1:d[3]])

    def words(s):
        ws = set()
        for w in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", s):
            ws.add(w)
            ws.update(w.split('.'))
        return ws

    uw = words(NL.join(src(d) for d in D if d[4] == 'U'))
    changed = True
    while changed:
        changed = False
        new = []
        for d in D:
            if d[4] == 'N' and len(short(d[1])) >= minlen and short(d[1]) in uw:
                d[4] = 'U'
                new.append(d)
                changed = True
        if new:
            uw |= words(NL.join(src(d) for d in new))


def prune(D, keep_names, keep_modules):
    by = collections.defaultdict(list)
    for d in D:
        by[d[0]].append(d)
    removed = 0
    for m, ds in by.items():
        if m in keep_modules:
            continue
        kept = [(d[2], d[3]) for d in ds if d[4] == 'U' or d[1] in keep_names]
        dead = {(d[2], d[3]) for d in ds if d[4] == 'N' and d[1] not in keep_names}
        dead = [r for r in dead if not any(not (b2 < r[0] or a2 > r[1]) for a2, b2 in kept)]
        if not dead:
            continue
        L = read(m)
        allr = [(d[2], d[3]) for d in ds]

        def start0(a, b):
            prev_end = max([b2 for a2, b2 in allr if b2 < a and (a2, b2) != (a, b)] + [0])
            i = a - 1
            while i > prev_end and L[i - 1].strip() != '' and not STOP.match(L[i - 1]):
                i -= 1
            return i

        dele = set()
        for a, b in dead:
            dele.update(range(start0(a, b), b))
        removed += len(dele)
        open(m.replace('.', '/') + '.lean', 'w', encoding='utf-8', newline=NL).write(
            NL.join(l for i, l in enumerate(L) if i not in dele))
    return removed


def main():
    D0 = load()
    textual_margin(D0)
    keep_names, keep_modules = set(), set()
    shorts = collections.defaultdict(list)
    for d in D0:
        shorts[short(d[1])].append(d[1])
    for rnd in range(40):
        subprocess.run(['git', 'checkout', '-q', '--', 'AKS'], check=True)
        removed = prune(D0, keep_names, keep_modules)
        r = subprocess.run(['lake', 'build'], capture_output=True, text=True, encoding='utf-8')
        out = r.stdout + r.stderr
        print(f'round {rnd}: removed {removed} lines, keep_names {len(keep_names)}, '
              f'keep_modules {len(keep_modules)}, rc {r.returncode}', flush=True)
        if r.returncode == 0:
            break
        progress = False
        for f, msg in re.findall(r'^error: (AKS/[^:]+\.lean):\d+:\d+: (.*)$', out, re.M):
            m = f[:-5].replace('/', '.')
            u = re.search(r'Unknown (?:identifier|constant) `([^`]+)`', msg) or \
                re.search(r'Invalid field `([^`]+)`', msg)
            if u:
                for nm in shorts.get(u.group(1).split('.')[-1], []):
                    if nm not in keep_names:
                        keep_names.add(nm)
                        progress = True
            elif m not in keep_modules:
                keep_modules.add(m)
                progress = True
        if not progress:
            print('no progress; stopping', flush=True)
            sys.exit(1)
    with open(f'{DATA}/keep.txt', 'w', encoding='utf-8') as fh:
        fh.write(NL.join(sorted(keep_names)) + NL + NL.join('MODULE ' + m for m in sorted(keep_modules)))


if __name__ == '__main__':
    main()
