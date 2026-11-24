#!/usr/bin/env python3
"""Bound one local CEGIS process and stop promptly if the task closes."""
import argparse
from datetime import datetime,timezone
import hashlib
import json
from pathlib import Path
import signal
import subprocess
import sys
import time

from search import check_live,InactiveTask

HERE=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--case-file',type=Path,required=True)
parser.add_argument('--seconds',type=float,default=300)
args=parser.parse_args()
assert 0<args.seconds<=300
check_live()
case_path=args.case_file.resolve()
command=[sys.executable,str(HERE/'search.py'),'--case-file',str(case_path),'--cegis','--seconds',str(args.seconds)]
record={'case':case_path.name,'case_sha256':hashlib.sha256(case_path.read_bytes()).hexdigest(),
        'source_sha256':hashlib.sha256((HERE/'search.py').read_bytes()).hexdigest(),
        'bound_seconds':args.seconds,'started_utc':datetime.now(timezone.utc).isoformat(),
        'status':'RUNNING','samples':[]}
record_path=HERE/f'{case_path.stem}-bounded.json'
log_path=HERE/f'{case_path.stem}-solver.log'
record_path.write_text(json.dumps(record,indent=2)+'\n')
started=time.monotonic()
stop=None
def interrupted(_sig,_frame):raise KeyboardInterrupt
signal.signal(signal.SIGTERM,interrupted)
with log_path.open('w') as log:
    process=subprocess.Popen(command,cwd=HERE.parent,stdout=log,stderr=subprocess.STDOUT)
    record['pid']=process.pid
    try:
        while process.poll() is None:
            try:check_live()
            except InactiveTask:
                stop='STOPPED_INACTIVE_TASK';break
            elapsed=time.monotonic()-started
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
            try:process.wait(timeout=min(5,args.seconds+5-elapsed))
            except subprocess.TimeoutExpired:pass
    except KeyboardInterrupt:stop='INTERRUPTED'
    finally:
        if process.poll() is None:
            process.terminate()
            try:process.wait(timeout=3)
            except subprocess.TimeoutExpired:
                process.kill();process.wait(timeout=3)
        record.update({'status':stop or ('FINISHED' if process.returncode==0 else 'PROCESS_ERROR'),
                       'exit_code':process.returncode,'child_reaped':process.poll() is not None,
                       'elapsed_seconds':time.monotonic()-started,'log_bytes':log_path.stat().st_size,
                       'stopped_utc':datetime.now(timezone.utc).isoformat()})
        record_path.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='samples'},indent=2),flush=True)
print(log_path.read_text()[-5000:],flush=True)
raise SystemExit(0 if record['status']=='FINISHED' else 2)
