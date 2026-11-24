"""One bounded Lean diagnostic with telemetry from its own process namespace."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
REPO = BASE / "pequalnp-proofs/lean"
TOOLCHAIN = BASE / ".pnp-tools/lean-4.36.0-linux"


def read(path: str) -> str | None:
    try:
        return Path(path).read_text()
    except (OSError, ValueError):
        return None


def mapping_summary(pid: int) -> dict:
    text = read(f"/proc/{pid}/smaps")
    if text is None:
        return {}
    maps = []
    current = None
    for line in text.splitlines():
        fields = line.split()
        if fields and "-" in fields[0] and len(fields) >= 5:
            current = {"path": " ".join(fields[5:]), "address": fields[0], "permissions": fields[1]}
            maps.append(current)
        elif current is not None and fields and fields[0] in {
            "Size:", "Rss:", "Pss:", "Private_Dirty:", "Anonymous:", "Referenced:"}:
            current[fields[0][:-1] + "_kib"] = int(fields[1])
    groups = {}
    for mapping in maps:
        path = mapping["path"]
        if ".olean" in path:
            kind = "olean_private" if path.endswith(".private") else "olean_server" if path.endswith(".server") else "olean_main"
        elif path.endswith((".ir", ".ir.sig")):
            kind = "ir"
        elif ".so" in path:
            kind = "shared_libraries"
        elif not path or path.startswith("["):
            kind = "anonymous"
        else:
            kind = "other_files"
        group = groups.setdefault(kind, {"mappings": 0, "size_kib": 0, "rss_kib": 0, "private_dirty_kib": 0})
        group["mappings"] += 1
        group["size_kib"] += mapping.get("Size_kib", 0)
        group["rss_kib"] += mapping.get("Rss_kib", 0)
        group["private_dirty_kib"] += mapping.get("Private_Dirty_kib", 0)
    return {"mapping_groups": groups,
            "largest_resident_mappings": sorted(maps, key=lambda x: x.get("Rss_kib", 0), reverse=True)[:10]}


def sample(pid: int, elapsed: float) -> dict:
    result = {"elapsed_seconds": round(elapsed, 3), "utc": datetime.now(timezone.utc).isoformat()}
    status = read(f"/proc/{pid}/status")
    if status is not None:
        for line in status.splitlines():
            if line.startswith(("State:", "Vm", "Rss", "Threads:")):
                name, value = line.split(":", 1)
                result[name] = value.strip()
    stat = read(f"/proc/{pid}/stat")
    if stat is not None:
        fields = stat.rsplit(")", 1)[1].split()
        result.update({"minor_faults": int(fields[7]), "major_faults": int(fields[9]),
                       "cpu_user_seconds": int(fields[11]) / os.sysconf("SC_CLK_TCK"),
                       "cpu_system_seconds": int(fields[12]) / os.sysconf("SC_CLK_TCK")})
    io = read(f"/proc/{pid}/io")
    if io is not None:
        result["io"] = {name: int(value) for name, value in
                        (line.split(":", 1) for line in io.splitlines())}
    result["wchan"] = read(f"/proc/{pid}/wchan")
    result["smaps_rollup"] = read(f"/proc/{pid}/smaps_rollup")
    result.update(mapping_summary(pid))
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--seconds", type=float, default=45)
    parser.add_argument("--label")
    parser.add_argument("--stop-file", type=Path)
    parser.add_argument("--object", action="store_true")
    parser.add_argument("--incr-header-save", type=Path)
    parser.add_argument("--incr-load", type=Path)
    parser.add_argument("--import-workers", type=int)
    args = parser.parse_args()
    # Extended intentionally for the authorized, single-compiler header-cache experiment.
    # Its coordinator keeps all stages within one 600-second total deadline.
    assert 0 < args.seconds <= 600
    source = args.source.resolve()
    label = args.label or source.stem
    stop_file = args.stop_file.resolve() if args.stop_file else HERE / f"{label}.stop"
    paths = [source.parent, REPO / ".lake/build/lib/lean"] + list(
        (REPO / ".lake/packages").glob("*/.lake/build/lib/lean"))
    environment = dict(os.environ)
    environment["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    if args.import_workers is not None:
        assert args.import_workers >= 1
        environment["LEAN_IMPORT_WORKERS"] = str(args.import_workers)
    command = [str(TOOLCHAIN / "bin/lean"), "-j", "1", "--profile"]
    if args.incr_header_save:
        command += ["--incr-header-save=" + str(args.incr_header_save.resolve())]
    if args.incr_load:
        assert args.incr_load.is_file()
        assert Path(str(args.incr_load) + ".deps").is_file()
        command += ["--incr-load=" + str(args.incr_load.resolve())]
    if args.object:
        command += ["--root=" + str(source.parent), "-o", str(source.with_suffix(".olean"))]
    command += [str(source)]
    record = {"command": command, "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
              "bound_seconds": args.seconds, "started_utc": datetime.now(timezone.utc).isoformat(),
              "wrapper_max_bound_seconds": 600,
              "lean_import_workers": environment.get("LEAN_IMPORT_WORKERS"),
              "stop_file": str(stop_file),
              "parent_cgroup": read("/proc/self/cgroup"), "parent_limits": read("/proc/self/limits"),
              "samples": [], "status": "running"}
    record_path = HERE / f"{label}.diagnostic.json"
    log_path = HERE / f"{label}.lean.log"
    record_path.write_text(json.dumps(record, indent=2) + "\n")
    started = time.monotonic()
    killed = False
    interrupted = False
    stop_requested = False
    def interrupt_handler(_signal, _frame):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupt_handler)
    with log_path.open("w") as log:
        process = subprocess.Popen(command, cwd=BASE, env=environment, stdout=log,
                                   stderr=subprocess.STDOUT)
        record["pid"] = process.pid
        record["child_limits"] = read(f"/proc/{process.pid}/limits")
        try:
            while process.poll() is None:
                if stop_file.exists():
                    stop_requested = True
                    break
                elapsed = time.monotonic() - started
                row = sample(process.pid, elapsed)
                record["samples"].append(row)
                record_path.write_text(json.dumps(record, indent=2) + "\n")
                print(json.dumps({key: row.get(key) for key in (
                    "elapsed_seconds", "State", "VmRSS", "VmHWM", "major_faults",
                    "minor_faults", "cpu_user_seconds", "cpu_system_seconds", "io", "wchan")}), flush=True)
                remaining = args.seconds - (time.monotonic() - started)
                if remaining <= 0:
                    killed = True
                    break
                try:
                    process.wait(timeout=min(5, remaining))
                except subprocess.TimeoutExpired:
                    pass
        except KeyboardInterrupt:
            interrupted = True
        finally:
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait(timeout=3)
            record["exit_code"] = process.returncode
            record["elapsed_seconds"] = round(time.monotonic() - started, 3)
            record["stopped_utc"] = datetime.now(timezone.utc).isoformat()
            record["status"] = ("stop_requested" if stop_requested else "interrupted" if interrupted
                                else "deadline_terminated" if killed else "exited")
            record["log_bytes"] = log_path.stat().st_size
            record["child_reaped"] = process.poll() is not None
            record["final_source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
            record["source_unchanged"] = record["final_source_sha256"] == record["source_sha256"]
            if args.object and source.with_suffix(".olean").exists():
                record["object_sha256"] = hashlib.sha256(source.with_suffix(".olean").read_bytes()).hexdigest()
            if args.incr_header_save:
                record["snapshot_artifacts"] = {}
                for artifact in (args.incr_header_save, Path(str(args.incr_header_save) + ".deps")):
                    if artifact.is_file():
                        record["snapshot_artifacts"][str(artifact.resolve())] = {
                            "bytes": artifact.stat().st_size,
                            "sha256": hashlib.sha256(artifact.read_bytes()).hexdigest()}
            record_path.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({key: record[key] for key in (
        "status", "exit_code", "elapsed_seconds", "child_reaped", "log_bytes")}), flush=True)
    print(log_path.read_text(), flush=True)
    return 0 if record["status"] == "exited" and process.returncode == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
