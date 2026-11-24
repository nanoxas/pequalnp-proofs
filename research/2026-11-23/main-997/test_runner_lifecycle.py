#!/usr/bin/env python3
"""Exercise bounded-runner cleanup with sleeping dummy children only."""
import hashlib
import json
from pathlib import Path
import signal
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent


def run_one(mode, expected_status):
    label=f'lifecycle-{mode}'
    stop_file=HERE/f'{label}.stop'
    stop_file.unlink(missing_ok=True)
    record_file=HERE/f'{label}-bounded.json'
    record_file.unlink(missing_ok=True)
    command=[sys.executable,str(HERE/'run_bounded.py'),
             '--case-file',str(HERE/'pg4-case.json'),
             '--label',label,'--stop-file',str(stop_file),
             '--dummy-seconds','0.05' if mode=='natural' else '60',
             '--seconds','0.2' if mode=='deadline' else '20']
    if mode=='exception':
        command+=['--dummy-runner-error-after','0.2']
    runner=subprocess.Popen(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                            text=True,start_new_session=True)
    try:
        ready_deadline=time.monotonic()+5
        while mode in ('stopfile','signal'):
            if runner.poll() is not None:
                raise AssertionError('runner ended before interruption')
            try:
                record=json.loads(record_file.read_text())
                ready='pid' in record
            except (OSError,json.JSONDecodeError):
                ready=False
            if ready:
                if mode=='stopfile':stop_file.write_text('test stop request\n')
                else:runner.send_signal(signal.SIGINT)
                break
            if time.monotonic()>ready_deadline:
                raise TimeoutError('dummy runner did not start')
            time.sleep(0.02)
        stdout,stderr=runner.communicate(timeout=12)
    finally:
        if runner.poll() is None:
            runner.terminate()
            try:runner.wait(timeout=3)
            except subprocess.TimeoutExpired:
                runner.kill();runner.wait(timeout=3)
    record=json.loads(record_file.read_text())
    assert record['mode']=='lifecycle_dummy'
    assert record['status']==expected_status,(mode,record)
    assert record['child_reaped'] is True,(mode,record)
    assert record['exit_code']==(0 if mode=='natural' else -signal.SIGTERM),(mode,record)
    assert runner.returncode==(0 if mode=='natural' else 2),(mode,runner.returncode,stderr)
    assert not stderr,(mode,stderr)
    if mode=='exception':
        assert 'intentional lifecycle-test runner exception' in record['runner_exception']
        assert 'Traceback' in (HERE/f'{label}-runner-error.log').read_text()
    return {'case':mode,'status':record['status'],'runner_exit_code':runner.returncode,
            'child_exit_code':record['exit_code'],'child_reaped':record['child_reaped'],
            'elapsed_seconds':record['elapsed_seconds'],'record_file':record_file.name}


def main():
    cases=[('natural','FINISHED'),('stopfile','STOP_REQUESTED'),
           ('signal','INTERRUPTED'),('exception','RUNNER_EXCEPTION'),
           ('deadline','UNKNOWN_TIME_LIMIT')]
    results=[run_one(*case) for case in cases]
    record={'status':'PASS','scope':'Dummy sleeping children only; no SAT query or lease action.',
            'old_pg4_cleanup':'reaping_unconfirmed; these tests do not retroactively establish cleanup.',
            'runner_sha256':hashlib.sha256((HERE/'run_bounded.py').read_bytes()).hexdigest(),
            'test_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'cases':results}
    (HERE/'wrapper-lifecycle-tests.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))


if __name__=='__main__':main()
