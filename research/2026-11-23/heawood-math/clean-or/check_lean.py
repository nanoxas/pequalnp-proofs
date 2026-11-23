"""Check a local Lean file with the pinned toolchain and existing package cache.

This avoids Lake configuration work and limits Lean to one worker. It performs
no dependency builds, downloads, or changes to the project repository.
"""
from pathlib import Path
import argparse
import os
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument("source", type=Path)
parser.add_argument("--object", action="store_true")
args = parser.parse_args()
root = Path(__file__).resolve().parents[2]
lean_root = root / "pequalnp-proofs/lean"
source = args.source.resolve()
env = os.environ.copy()
package_paths = [str(p / ".lake/build/lib/lean")
                 for p in (lean_root / ".lake/packages").iterdir() if p.is_dir()]
package_paths += [str(lean_root / ".lake/build/lib/lean"), str(source.parent)]
env["LEAN_PATH"] = ":".join(package_paths)
command = [str(root / ".pnp-tools/lean-4.36.0-linux/bin/lean"), "-j", "1"]
if args.object:
    command += ["--root=" + str(source.parent), "-o", str(source.with_suffix(".olean"))]
command += [str(source)]
log_path = source.with_suffix(".check.log")
started = time.monotonic()
with log_path.open("w") as log:
    result = subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT)
print(log_path.read_text(), end="")
print(f"Lean exit {result.returncode}; elapsed {time.monotonic() - started:.2f}s")
raise SystemExit(result.returncode)
