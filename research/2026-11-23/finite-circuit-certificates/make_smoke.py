#!/usr/bin/env python3
"""Emit a synthetic AND-of-five standalone check; never submits or runs Lean."""
import hashlib
import json
from pathlib import Path

import pipeline

HERE = Path(__file__).resolve().parent
output = HERE/"smoke"
output.mkdir(exist_ok=True)
table = 0x80000000

# The public-row parser is exercised on an explicitly synthetic fixture.
# Its generated theorem then receives a descriptive namespace outside the
# project's numbered contribution names. This is not a posted desk row.
fixture = {"id":"L-meta-0","module":"PEqualNP.Outside.L_meta_0",
           "statement":pipeline.statement_for([table]),"imports":["PEqualNP.Defs"]}
row = pipeline.parse_row(fixture)
witness = {"index":0,"truth_table":hex(table),"lower_s":3,
           "gates":[{"op":"and","inputs":[0,1]},
                    {"op":"and","inputs":[5,2]},
                    {"op":"and","inputs":[6,3]},
                    {"op":"and","inputs":[7,4]}],"output":8}
records = pipeline.normalize_records(row,[witness])
audit = pipeline.audit_records(records,seconds=10)
row["module"] = "PEqualNP.Outside.FiniteCertificateSmoke"
source = pipeline.lean_source(row,records)
source = "-- Synthetic AND-of-five smoke test; not a desk contribution.\n"+source
path = output/"Smoke.lean"
path.write_text(source)
pipeline.write_json(output/"inputs.json",records)
pipeline.write_json(output/"python-audit.json",{"status":"PASS","synthetic":True,"searches":audit})
manifest = {"kind":"synthetic_smoke","synthetic":True,"desk_task":None,
            "namespace":row["module"],"aux_namespace":row["module"]+"_aux",
            "truth_table":hex(table),"upper_gates":4,"lower_s":3,
            "source":"Smoke.lean","source_sha256":hashlib.sha256(source.encode()).hexdigest(),
            "source_bytes":len(source.encode()),"status":"GENERATED_UNCHECKED",
            "kernel_check_status":"not_run","minimal_header_status":"Awaiting this synthetic Lean check.",
            "engine_body_sha256":pipeline.BODY_SHA256,
            "reproduce":"python3 finite-circuit-certificates/make_smoke.py"}
pipeline.write_json(output/"manifest.json",manifest)
print(json.dumps({"absolute_source":str(path),**manifest},indent=2))
