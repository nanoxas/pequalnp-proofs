"""One authorized header-cache experiment with a shared 600-second deadline."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
BASE = HERE.parent.parent
STATE = HERE / "experiment.json"
STOP = HERE / "STOP"
WRAPPER = BASE / "infra-lean/bounded_check.py"
SNAPSHOT = HERE / "six-imports.snap"
CORE = BASE / "finite-circuit-certificates/GenericCore.lean"
SMOKE = BASE / "finite-circuit-certificates/GenericSmoke.lean"


def main() -> int:
    record = json.loads(STATE.read_text())
    assert record["status"] == "PREPARED"
    assert not STOP.exists()
    assert not SNAPSHOT.exists()
    for source, key in ((CORE, "source_core_sha256"), (SMOKE, "source_smoke_sha256")):
        assert hashlib.sha256(source.read_bytes()).hexdigest() == record[key]
        assert not source.with_suffix(".olean").exists()
    started = time.monotonic()
    record.update(status="RUNNING", started_utc=datetime.now(timezone.utc).isoformat(), stages=[])
    STATE.write_text(json.dumps(record, indent=2) + "\n")

    def interrupted(_signal, _frame):
        STOP.touch()

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    stages = [
        ("HeaderSave", HERE / "ImportHeader.lean", ["--incr-header-save", str(SNAPSHOT)]),
        ("GenericCoreCached", CORE, ["--incr-load", str(SNAPSHOT), "--object"]),
        ("GenericSmokeCachedExperiment", SMOKE, ["--object"]),
    ]
    for label, source, extra in stages:
        remaining = 600 - (time.monotonic() - started)
        if remaining <= 1 or STOP.exists():
            record["status"] = "INCOMPLETE_TOTAL_DEADLINE" if remaining <= 1 else "STOP_REQUESTED"
            break
        command = [sys.executable, str(WRAPPER), str(source), "--seconds", str(remaining),
                   "--label", label, "--stop-file", str(STOP), "--import-workers", "1", *extra]
        stage = {"label": label, "source": str(source), "command": command,
                 "budget_seconds": remaining, "status": "RUNNING"}
        record["stages"].append(stage)
        STATE.write_text(json.dumps(record, indent=2) + "\n")
        print(json.dumps({"starting_stage": label, "remaining_seconds": round(remaining, 3)}), flush=True)
        process = subprocess.Popen(command, cwd=BASE)
        while process.poll() is None:
            try:
                process.wait(timeout=1)
            except subprocess.TimeoutExpired:
                if time.monotonic() - started >= 600:
                    STOP.touch()
        stage["wrapper_exit_code"] = process.returncode
        diagnostic = BASE / "infra-lean" / f"{label}.diagnostic.json"
        stage["diagnostic"] = str(diagnostic)
        if diagnostic.is_file():
            detail = json.loads(diagnostic.read_text())
            stage.update({key: detail.get(key) for key in (
                "status", "exit_code", "elapsed_seconds", "child_reaped", "log_bytes", "object_sha256")})
        if process.returncode != 0:
            record["status"] = "STOPPED_AT_" + label
            STATE.write_text(json.dumps(record, indent=2) + "\n")
            break
        stage["status"] = "PASS"
        STATE.write_text(json.dumps(record, indent=2) + "\n")
    else:
        record["status"] = "ALL_STAGES_PASS"

    record["elapsed_seconds"] = round(time.monotonic() - started, 3)
    record["stopped_utc"] = datetime.now(timezone.utc).isoformat()
    record["source_core_unchanged"] = hashlib.sha256(CORE.read_bytes()).hexdigest() == record["source_core_sha256"]
    record["source_smoke_unchanged"] = hashlib.sha256(SMOKE.read_bytes()).hexdigest() == record["source_smoke_sha256"]
    STATE.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record, indent=2), flush=True)
    return 0 if record["status"] == "ALL_STAGES_PASS" else 2


if __name__ == "__main__":
    raise SystemExit(main())
