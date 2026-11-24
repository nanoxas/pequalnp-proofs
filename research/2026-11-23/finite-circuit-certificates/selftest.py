#!/usr/bin/env python3
"""Target-neutral Python tests. No Lean, network, or real desk row is used."""
from __future__ import annotations

import contextlib
import copy
import hashlib
import io
import itertools
import json
from pathlib import Path
import random
import tempfile

import formula_upper
from live_checker import Evaluator, ONE, TOP, ZERO, coverage, make_raw, sep, take_one, take_two, union_sep
import pipeline

HERE = Path(__file__).resolve().parent


def run():
    rng = random.Random(5191445)
    comparisons = 0
    for _ in range(240):
        lift = lambda x:sum(x << j for j in range(0,256,4))
        raw = tuple(dict.fromkeys((lift(rng.randrange(16)),lift(rng.randrange(16))) for _ in range(rng.randrange(1,5))))
        raw = tuple(a for a in raw if a not in (ZERO,ONE))
        for d in (False,True):
            c = coverage(d,raw)
            assert c[0] == union_sep(d,raw)
            for a in raw:
                assert take_one(c,sep(d,a)) == union_sep(d,tuple(x for x in raw if x != a))
            for a,b in itertools.combinations(raw,2):
                assert take_two(c,sep(d,a),sep(d,b)) == union_sep(d,tuple(x for x in raw if x != a and x != b))
        for t in (0,1):
            k = rng.randrange(4)
            fast = Evaluator().run(k,t,raw)
            slow = Evaluator(reference=True).run(k,t,raw)
            assert fast["status"] == slow["status"] == "COMPLETE"
            assert fast["result"] == slow["result"]
            comparisons += 1
    for table,n,k,t,want in [(8,2,0,0,False),(8,2,1,0,True),(14,2,1,0,True),(1,1,0,1,False),(1,1,1,1,True)]:
        for reference in (False,True):
            got = Evaluator(reference=reference).run(k,t,make_raw(table,n))
            assert got["status"] == "COMPLETE" and got["result"] == want

    # Synthetic AND-of-five / OR-of-five family, outside the project desk.
    tables = [0x80000000,0xfffffffe]
    row_data = {"id":"L-meta-0","module":"PEqualNP.Outside.L_meta_0","statement":pipeline.statement_for(tables),"imports":["PEqualNP.Defs"]}
    row = pipeline.parse_row(row_data)
    generated = formula_upper.generate(tables,max_cost=4,seconds=10)
    records = [{"index":i,**record,"lower_s":len(record["gates"])-1} for i,record in enumerate(generated["tables"])]
    normalized = pipeline.normalize_records(row,records)
    assert [len(r["gates"]) for r in normalized] == [4,4]
    audit = pipeline.audit_records(normalized,seconds=10)
    assert len(audit) == 2
    source = pipeline.lean_source(row,normalized)
    body,imports = pipeline.generic_engine()
    assert source.startswith(imports)
    assert source.count(body) == 1
    assert f"theorem {row['module']} : {row_data['statement']} := by" in source
    assert source.count("namespace PEqualNP.Outside.L_meta_0_aux") == 1

    # Formula generator supports constants and stops with a verified baseline.
    random_tables = [0,formula_upper.ALL,*formula_upper.VARIABLES]
    for _ in range(12):
        seeds = [rng.randrange(32) for _ in range(5)]
        random_tables.append(sum(any(row & s == s for s in seeds) << row for row in range(32)))
    uppers = formula_upper.generate(random_tables,max_cost=3,seconds=10)
    assert all(formula_upper.evaluate(w)==table for w,table in zip(uppers["tables"],random_tables))

    failures = []
    def expect(code, action):
        try:
            action()
        except pipeline.PrerequisiteError as exc:
            assert exc.code == code,(code,exc.record())
            failures.append(code)
        else:
            raise AssertionError(f"Expected {code}")

    nonessential = {**row_data,"statement":pipeline.statement_for([formula_upper.VARIABLES[0]])}
    expect("NONESSENTIAL_VARIABLES",lambda:pipeline.normalize_records(pipeline.parse_row(nonessential),[{"index":0,"truth_table":hex(formula_upper.VARIABLES[0]),"gates":[],"output":0}]))
    bad = copy.deepcopy(normalized)
    bad[0]["raw"][0][0] = hex(int(bad[0]["raw"][0][0],16)^1)
    expect("BAD_SAMPLE_LABEL",lambda:pipeline.normalize_records(row,bad))
    bad = copy.deepcopy(normalized)
    bad[0]["search_results"] = [{"status":"UNKNOWN"}]
    expect("UNKNOWN_SEARCH_STATUS",lambda:pipeline.normalize_records(row,bad))
    bad = copy.deepcopy(normalized)
    bad[0]["gates"][0]["op"] = "or"
    expect("WRONG_WITNESS_TABLE",lambda:pipeline.normalize_records(row,bad))
    bad = copy.deepcopy(normalized)
    out = bad[0]["output"]
    bad[0]["gates"].append({"op":"and","inputs":[out,out]})
    bad[0]["output"] = 5+len(bad[0]["gates"])-1
    bad[0]["lower_s"] += 1
    padded = pipeline.normalize_records(row,bad)
    expect("SEARCH_RETURNED_TRUE",lambda:pipeline.audit_records(padded,seconds=10))
    expect("UNKNOWN_SEARCH_STATUS",lambda:pipeline.audit_records(normalized,max_states=0))
    expect("UNKNOWN_SEARCH_STATUS",lambda:pipeline.audit_records(normalized,seconds=0))
    expect("CLOSED_ROW",lambda:pipeline.parse_row({**row_data,"checked":True}))
    expect("UNSUPPORTED_STATEMENT",lambda:pipeline.parse_row({**row_data,"statement":row_data["statement"].replace("Fin 5","Fin 4")}))
    bad = copy.deepcopy(normalized)
    bad[0]["index"] = -1
    expect("BAD_TABLE_INDEX",lambda:pipeline.normalize_records(row,bad))

    # Exercise the real CLI success and failure paths in disposable directories.
    with tempfile.TemporaryDirectory(prefix="finite-cert-selftest-") as temporary:
        folder = Path(temporary)
        row_path,witness_path = folder/"synthetic-row.json",folder/"witnesses.json"
        row_path.write_text(json.dumps(row_data))
        witness_path.write_text(json.dumps(records))
        with contextlib.redirect_stdout(io.StringIO()),contextlib.redirect_stderr(io.StringIO()):
            rc = pipeline.main(["build","--row",str(row_path),"--certificates",str(witness_path),"--out",str(folder/"good")])
            assert rc == 0
            manifest = json.loads((folder/"good/manifest.json").read_text())
            assert manifest["status"] == "GENERATED_UNCHECKED" and manifest["kernel_check_status"] == "not_run"
            assert (folder/"good/L_meta_0.lean").read_text() == source
            rc = pipeline.main(["build","--row",str(row_path),"--certificates",str(witness_path),"--out",str(folder/"unknown"),"--max-states","0"])
            assert rc == 2 and not list((folder/"unknown").glob("*.lean"))
            failed = json.loads((folder/"unknown/failed-status.json").read_text())
            assert failed["code"] == "UNKNOWN_SEARCH_STATUS"
    return {"status":"PASS","scope":"Synthetic Python tests only; no Lean or real desk assignment was used.",
            "random_evaluator_comparisons":comparisons,"coverage_formula_frontiers":240,
            "known_semantic_cases":10,"synthetic_target_rejections":4,
            "formula_witness_tables":len(random_tables),"expected_failures":failures,
            "exact_engine_body_sha256":hashlib.sha256(body.encode()).hexdigest(),
            "minimal_header_status":"not Lean-checked","kernel_check_status":"not_run"}


if __name__ == "__main__":
    result = run()
    (HERE/"selftest-results.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
