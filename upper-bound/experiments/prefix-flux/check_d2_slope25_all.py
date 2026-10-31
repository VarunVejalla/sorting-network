#!/usr/bin/env python3
"""Generate and Lean-check each slope-25 dual certificate separately."""
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
from pathlib import Path
import subprocess
import sys

here = Path(__file__).resolve().parent
repo = here.parents[2]
env = os.environ.copy()
env["LEAN_PATH"] = str(here) + os.pathsep + env.get("LEAN_PATH", "")


def check(delta: int) -> tuple[int, str, str]:
    subprocess.run(
        [sys.executable, str(here / "d2_slope25_emit_lean.py"), str(delta)],
        cwd=repo,
        check=True,
        stdout=subprocess.DEVNULL,
    )
    result = subprocess.run(
        ["lake", "env", "lean", str(here / f"D2Slope25Certificate{delta:02}.lean"),
         "-o", str(here / f"D2Slope25Certificate{delta:02}.olean")],
        cwd=repo,
        text=True,
        capture_output=True,
        env=env,
    )
    if result.returncode != 0:
        return delta, "FAIL", result.stdout + result.stderr
    return delta, "PASS", ""


failed = False
with ThreadPoolExecutor(max_workers=4) as pool:
    futures = [pool.submit(check, delta) for delta in range(64)]
    for future in as_completed(futures):
        delta, status, detail = future.result()
        print(f"delta {delta:02}: {status}", flush=True)
        if status != "PASS":
            failed = True
            print(detail, flush=True)
if failed:
    raise SystemExit(1)
