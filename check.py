#!/usr/bin/env python3
"""Recheck the complete demo: five specifications and two final-path witnesses."""
import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
PROPERTIES = {
    "noPaymentWithoutConfirmation": "invariant",
    "noDoublePayment": "invariant",
    "moneyConserved": "invariant",
    "noLockedFunds": "temporal",
}
WITNESSES = {"neverPaid": "invariant", "neverRefunded": "invariant"}


FIELDS = {'funded', 'shipped', 'confirmed', 'expired', 'buyer', 'escrow', 'seller', 'payments'}
BOOLS = {'funded', 'shipped', 'confirmed', 'expired'}


def parse_trace(log):
    states = []
    pattern = r'^State (\d+): <([^\n]+)>\s*\ns = \[(.*?)\]'
    for match in re.finditer(pattern, log, re.M | re.S):
        values = {}
        for field in match[3].split(','):
            key, value = field.strip().split(' |-> ')
            if key in BOOLS:
                if value not in {'TRUE', 'FALSE'}:
                    raise ValueError(f'Invalid boolean: {field}')
                values[key] = value == 'TRUE'
            else:
                values[key] = int(value)
        if set(values) != FIELDS:
            raise ValueError('Unsupported state fields; update the exporter for this model')
        states.append({'index': int(match[1]),
                       'action': 'init' if match[2] == 'Initial predicate' else match[2].split()[0],
                       'values': values})
    if not states or [s['index'] for s in states] != list(range(1, len(states) + 1)):
        raise ValueError('Missing or incomplete TLC state trace')
    loop = None
    stutter = re.search(r'^State (\d+): Stuttering', log, re.M)
    back = re.search(r'Back to state (\d+)', log)
    if stutter:
        if int(stutter[1]) != len(states) + 1:
            raise ValueError('Unexpected stuttering index')
        loop = {'type': 'stuttering', 'from_state': len(states), 'to_state': len(states)}
    elif back:
        target = int(back[1])
        if not 1 <= target <= len(states):
            raise ValueError('Invalid cycle target')
        loop = {'type': 'cycle', 'from_state': len(states), 'to_state': target}
    return states, loop


def export_counterexamples(results):
    records = []
    for result in results:
        if result['status'] != 'FAIL':
            continue
        version, prop = result['version'], result['property']
        source = (ROOT / 'specs' / f'{version}.qnt').read_text()
        if hashlib.sha256(source.encode()).hexdigest() != result['spec_sha256']:
            raise ValueError(f'Stale result for {version}; recheck the model first')
        log = (ROOT / result['log']).read_text()
        temporal = prop == 'noLockedFunds'
        marker = ('Temporal property q_temporalProps was violated' if temporal
                  else 'Invariant q_inv is violated')
        if marker not in log:
            raise ValueError(f'Missing violation in {result["log"]}')
        states, loop = parse_trace(log)
        if temporal != (loop is not None):
            raise ValueError('Unexpected or unsupported counterexample ending')
        records.append({'version': version, 'property': prop,
                        'states': states, 'loop': loop, 'source_log': result['log']})
    target = ROOT / 'data/counterexamples.json'
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(records, indent=2) + '\n')
    print(f'Exported {len(records)} counterexamples to {target}')


def check(spec, name, kind):
    command = ["node", str(ROOT / "node_modules/@informalsystems/quint/dist/src/cli.js"),
               "verify", str(spec), "--main", "procurement", "--backend", "tlc",
               "--apalache-version", "0.62.1", "--tlc-config", str(ROOT / "tlc.json"),
               "--verbosity", "3", f"--{kind}", name]
    try:
        with tempfile.TemporaryDirectory(prefix="procurement-check-") as scratch:
            process = subprocess.run(command, cwd=scratch, capture_output=True,
                                     text=True, timeout=180)
        output = process.stdout + process.stderr
        code = process.returncode
    except subprocess.TimeoutExpired as error:
        output = "TIMEOUT\n" + str(error.stdout or "") + str(error.stderr or "")
        code = -1
    output = re.sub(r"\x1b\[[0-9;]*m", "", output)
    status = "ERROR"
    if code == 0 and "Model checking completed. No error has been found." in output:
        status = "PASS"
    elif code != 0 and ("Invariant q_inv is violated" in output
                       or "Temporal property q_temporalProps was violated" in output):
        status = "FAIL"
    if name in WITNESSES:
        status = {"FAIL": "REACHABLE", "PASS": "UNREACHABLE"}.get(status, status)
    log = Path("logs") / f"{spec.stem}-{name}.log"
    (ROOT / log).write_text("$ " + shlex.join(command) + "\n\n" + output)
    states = re.search(r"(\d+) distinct states found", output)
    print(f"{spec.stem:10} {name:30} {status}", flush=True)
    return {"property": name, "status": status, "exit_code": code,
            "distinct_states": int(states[1]) if states else None, "log": str(log)}


def main():
    reference = (ROOT / "specs/generated.qnt").read_text().split("// CHECKS:", 1)[1]
    results = []
    (ROOT / "logs").mkdir(exist_ok=True)
    for version in ["generated", "v0", "v1", "v2", "v3"]:
        spec = ROOT / "specs" / f"{version}.qnt"
        source = spec.read_text()
        block = source.split("// CHECKS:", 1)[1]
        if block != reference:
            raise SystemExit(f"{version}: properties or fairness assumptions were changed")
        checks = PROPERTIES | WITNESSES if version == "v3" else PROPERTIES
        for name, kind in checks.items():
            results.append({"version": version, **check(spec, name, kind),
                            "spec_sha256": hashlib.sha256(source.encode()).hexdigest(),
                            "checks_sha256": hashlib.sha256(block.encode()).hexdigest()})
            (ROOT / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    export_counterexamples(results)
    # Earlier versions intentionally fail; tool errors and final failures do not.
    failed = any(r["status"] == "ERROR" or
                 (r["version"] == "v3" and r["status"] not in {"PASS", "REACHABLE"})
                 for r in results)
    raise SystemExit(1 if failed else 0)


if __name__ == "__main__":
    main()
