"""Tabulate rd731 outputs: per-n sweeps (worst esc/allowed over j > J intervals, FAIL list) and iv covers."""
import glob, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
os.chdir(HERE)
pat = re.compile(r"j in \[\s*([0-9.e+-]+),\s*([0-9.e+-]+)\] J f=\s*([0-9.]+): worst\s+([-0-9.e+]+) at s2 <=\s+(\d+)\s+allowed\s+([0-9.e+]+)\s+(OK|FAIL)")
for d in ("sweeps", "sweeps_fine", "sweeps_gap"):
    print(f"== {d}")
    for fn in sorted(glob.glob(f"{d}/*.out"), key=lambda s: float(re.findall(r"s([0-9.]+)", s)[0].rstrip('.'))):
        rows = [pat.search(l) for l in open(fn)]
        rows = [r for r in rows if r]
        head = open(fn).readline().strip()
        done = any(l.startswith("DONE") for l in open(fn))
        fails = [r for r in rows if r.group(7) == "FAIL"]
        big = [r for r in rows if float(r.group(2)) > 1.0001]
        w = max(big, key=lambda r: float(r.group(4)) / float(r.group(6))) if big else None
        jr = f"[{rows[0].group(1)}, {rows[-1].group(2)}] J" if rows else "-"
        ws = f"worst {float(w.group(4)) / float(w.group(6)):.4f} at j/J in [{w.group(1)}, {w.group(2)}] f={w.group(3)} s2<={w.group(5)}" if w else ""
        print(f"{fn}: {len(rows)} intervals {jr} {'DONE' if done else 'RUNNING'}; {len(fails)} FAIL "
              f"{[(r.group(1), r.group(2)) for r in fails]}; {ws}")
for d in ("coverB", "coverB25", "coverA", "coverA_ladder"):
    ok = fail = 0
    for fn in glob.glob(f"{d}/*.out"):
        for l in open(fn):
            if l.startswith(("b in", "j in")):
                ok += "CERT-OK" in l
                fail += "CERT-FAIL" in l
    print(f"== {d}: {ok} CERT-OK, {fail} CERT-FAIL")
