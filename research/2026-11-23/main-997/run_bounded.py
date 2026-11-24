#!/usr/bin/env python3
"""Bound one local CEGIS process and stop promptly if the task closes."""
import argparse
from datetime import datetime,timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import traceback

from search import check_live,InactiveTask

HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--case-file',type=Path,required=True)
parser.add_argument('--seconds',type=float,default=300)
parser.add_argument('--stop-file',type=Path)
parser.add_argument('--label')
parser.add_argument('--dummy-seconds',type=float)
parser.add_argument('--dummy-runner-error-after',type=float)
args=parser.parse_args()
assert 0<args.seconds<=300
if args.dummy_seconds is not None:
    assert args.dummy_seconds>=0
else:
    assert args.dummy_runner_error_after is None
    check_live()
case_path=args.case_file.resolve()
command=[sys.executable,str(HERE/'search.py'),'--case-file',str(case_path),'--cegis','--seconds',str(args.seconds)]
if args.dummy_seconds is not None:
    command=[sys.executable,'-c',f'import time; print("dummy started",flush=True); time.sleep({args.dummy_seconds!r})']
label=args.label or case_path.stem
stop_file=args.stop_file.resolve() if args.stop_file else HERE/f'{label}.stop'
if stop_file.exists():raise SystemExit('Stop file already exists; refusing to launch a child.')
record={'case':case_path.name,'case_sha256':hashlib.sha256(case_path.read_bytes()).hexdigest(),
        'source_sha256':hashlib.sha256((HERE/'search.py').read_bytes()).hexdigest(),
        'bound_seconds':args.seconds,'started_utc':datetime.now(timezone.utc).isoformat(),
        'status':'RUNNING','samples':[],'stop_file':str(stop_file),
        'mode':'lifecycle_dummy' if args.dummy_seconds is not None else 'cegis'}
record_path=HERE/f'{label}-bounded.json'
log_path=HERE/f'{label}-solver.log'
record_path.write_text(json.dumps(record,indent=2)+'\n')
started=time.monotonic()
stop=None
requested_signal=None
def interrupted(sig,_frame):
    global requested_signal
    requested_signal=sig
signal.signal(signal.SIGINT,interrupted)
signal.signal(signal.SIGTERM,interrupted)
with log_path.open('w') as log:
    process=subprocess.Popen(command,cwd=HERE.parent,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
    record['pid']=process.pid
    try:
        while process.poll() is None:
            if requested_signal is not None:
                stop='INTERRUPTED';break
            if stop_file.exists():
                stop='STOP_REQUESTED';break
            if args.dummy_seconds is None:
                try:check_live()
                except InactiveTask:
                    stop='STOPPED_INACTIVE_TASK';break
            elapsed=time.monotonic()-started
            if args.dummy_runner_error_after is not None and elapsed>=args.dummy_runner_error_after:
                raise RuntimeError('intentional lifecycle-test runner exception')
            if elapsed>=args.seconds+5:
                stop='UNKNOWN_TIME_LIMIT';break
            info={'elapsed_seconds':round(elapsed,3)}
            try:
                for line in Path(f'/proc/{process.pid}/status').read_text().splitlines():
                    if line.startswith(('VmRSS:','VmHWM:','VmSize:')):
                        key,value=line.split(':',1);info[key]=value.strip()
            except OSError:pass
            record['samples'].append(info)
            record_path.write_text(json.dumps(record,indent=2)+'\n')
            if len(record['samples'])%4==1:print(json.dumps(info),flush=True)
            try:process.wait(timeout=min(0.1 if args.dummy_seconds is not None else 5,args.seconds+5-elapsed))
            except subprocess.TimeoutExpired:pass
    except BaseException:
        stop='RUNNER_EXCEPTION'
        error=traceback.format_exc()
        record['runner_exception']=error
        (HERE/f'{label}-runner-error.log').write_text(error)
    finally:
        signal.signal(signal.SIGINT,signal.SIG_IGN)
        signal.signal(signal.SIGTERM,signal.SIG_IGN)
        try:
            if process.poll() is None:
                try:os.killpg(process.pid,signal.SIGTERM)
                except ProcessLookupError:pass
                try:process.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    try:os.killpg(process.pid,signal.SIGKILL)
                    except ProcessLookupError:pass
                    process.wait(timeout=3)
        except BaseException:
            record['cleanup_exception']=traceback.format_exc()
            stop='CLEANUP_FAILED'
        record.update({'status':stop or ('FINISHED' if process.returncode==0 else 'PROCESS_ERROR'),
                       'exit_code':process.returncode,'child_reaped':process.poll() is not None,
                       'elapsed_seconds':time.monotonic()-started,'log_bytes':log_path.stat().st_size,
                       'stopped_utc':datetime.now(timezone.utc).isoformat()})
        record_path.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='samples'},indent=2),flush=True)
print(log_path.read_text()[-5000:],flush=True)
raise SystemExit(0 if record['status']=='FINISHED' else 2)
