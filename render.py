#!/usr/bin/env python3
"""Build one HTML report from saved checker evidence."""
import hashlib
from html import escape
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
rows = json.loads((ROOT / "results.json").read_text())
results = {(r["version"], r["property"]): r for r in rows}
properties = [
    ("noPaymentWithoutConfirmation", "No payment without confirmation"),
    ("noDoublePayment", "No double payment"),
    ("moneyConserved", "Money conservation"),
    ("noLockedFunds", "Prevention of money lock-up"),
]
versions = ["v0", "v1", "v2", "v3"]
for row in rows:
    source = (ROOT / "specs" / (row["version"] + ".qnt")).read_bytes()
    assert hashlib.sha256(source).hexdigest() == row["spec_sha256"], "Stale results"
assert len({r["checks_sha256"] for r in rows}) == 1, "Checks changed"
assert all(results["v3", p]["status"] == "PASS" for p, _ in properties)
assert all(results["v3", p]["status"] == "REACHABLE" for p in ["neverPaid", "neverRefunded"])


def trace(version, prop):
    log = (ROOT / results[version, prop]["log"]).read_text()
    states = []
    for match in re.finditer(r"State (\d+): <([^\n]+)>\ns = \[(.*?)\]", log, re.S):
        fields = dict(re.findall(r"(\w+) \|-> (TRUE|FALSE|-?\d+)", match[3]))
        states.append({"action": match[2].split()[0], **fields})
    assert states, "Counterexample trace is missing"
    actions = [s["action"] for s in states[1:]]
    if re.search(r"State \d+: Stuttering", log):
        actions.append("stutter forever")
    return " → ".join(actions), states[-1]


traces = [trace("v0", properties[0][0]), trace("v1", properties[2][0]),
          trace("v2", properties[3][0])]

svg = ['<svg xmlns="http://www.w3.org/2000/svg" width="1280" height="740" viewBox="0 0 1280 740" role="img" aria-labelledby="title desc">',
       '<title id="title">Three counterexample-guided repairs of a Quint procurement model</title>',
       '<desc id="desc">Controlled defects are repaired after real TLC counterexamples. All four fixed properties pass in v3.</desc>',
       '<defs><marker id="arrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto"><path d="M0 0L8 4L0 8" fill="none" stroke="#94a3b8" stroke-width="1.3"/></marker></defs>',
       '<rect width="1280" height="740" rx="18" fill="#ffffff"/>']


def text(x, y, value, size=18, color="#172b44", weight=400, mono=False):
    font = "Menlo,monospace" if mono else "Arial,Helvetica,sans-serif"
    svg.append(f'<text x="{x}" y="{y}" font-family="{font}" font-size="{size}" fill="{color}" font-weight="{weight}">{escape(str(value))}</text>')


def box(x, y, w, h, fill="#f7f9fc", stroke="#e2e8f0"):
    svg.append(f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="12" fill="{fill}" stroke="{stroke}"/>')


def arrow(x1, y, x2):
    svg.append(f'<path d="M{x1} {y}H{x2}" stroke="#94a3b8" stroke-width="1.8" fill="none" marker-end="url(#arrow)"/>')


# text(44, 43, "FORMAL METHODS  /  PROCUREMENT MVP", 13, "#64748b", 70)
text(44, 89, "MVP for repair loop", 36, weight=700)
# text(44, 122, "Quint specification → TLC counterexample → LLM repair → recheck", 18, "#52657d")
# text(44, 151, "Controlled-defect demonstration · one buyer · one seller · one unit of money", 15, "#64748b")

failures = ["Payment before confirmation", "Payment creates extra money", "Expired escrow never releases"]
repairs = [("Require confirmation", "shipped → confirmed"),
           ("Debit escrow atomically", "escrow → escrow − 1"),
           ("Enable timeout refund", "remove false guard")]
last = [t[1] for t in traces]
details = [f'confirmed = {last[0]["confirmed"].lower()}   payments = {last[0]["payments"]}',
           f'buyer / escrow / seller = {last[1]["buyer"]} / {last[1]["escrow"]} / {last[1]["seller"]}',
           f'expired = {last[2]["expired"].lower()}   escrow = {last[2]["escrow"]} forever']
for i in range(3):
    y = 182 + i * 149
    box(44, y, 84, 120)
    text(61, y + 31, f"ROUND {i + 1}", 11, "#64748b", 700)
    text(65, y + 75, f"v{i}", 29, weight=700)
    arrow(136, y + 60, 158)
    box(170, y, 512, 120, "#fff8f7", "#f0d5d0")
    text(189, y + 27, "TLC COUNTEREXAMPLE", 11, "#b34b37", 700)
    text(189, y + 53, failures[i], 20, weight=700)
    text(189, y + 79, traces[i][0], 15, "#52657d")
    text(189, y + 103, details[i], 14, "#ad4434", mono=True)
    arrow(694, y + 60, 720)
    box(732, y, 338, 120, "#f0f6ff", "#d6e3f6")
    text(752, y + 27, "LLM REPAIR", 11, "#3469aa", 700)
    text(752, y + 59, repairs[i][0], 20, weight=700)
    text(752, y + 91, repairs[i][1], 16, "#3469aa", mono=True)
    arrow(1082, y + 60, 1108)
    box(1120, y, 116, 120, "#f0faf6", "#cee8dc")
    text(1137, y + 29, "RECHECK", 11, "#35775f", 700)
    text(1156, y + 66, f"v{i+1}", 28, weight=700)
    count = sum(results[f"v{i+1}", p]["status"] == "PASS" for p, _ in properties)
    text(1137, y + 96, f"{count}/4 pass", 17, "#35775f", 700)

box(44, 647, 1192, 54, "#eff8f4", "#cee8dc")
state_count = results["v3", "noLockedFunds"]["distinct_states"]
text(64, 681, f"FINAL  v3    4/4 properties pass  ·  {state_count} reachable states  ·  payment and refund both reachable", 19, "#25634d", 700)
svg.append('</svg>')
figure = "\n".join(svg)

table_rows = []
for prop, label in properties:
    cells = []
    for version in versions:
        row = results[version, prop]
        status = row["status"]
        cells.append(f'<td><a class="{status.lower()}" href="{row["log"]}">{status}</a></td>')
    table_rows.append(f'<tr><th scope="row">{escape(label)}</th>{"".join(cells)}</tr>')

report = '''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Procurement · Quint repair loop</title>
<style>
*{box-sizing:border-box}body{margin:0;background:#eef2f6;color:#172b44;font:16px/1.5 Arial,Helvetica,sans-serif}
main{max-width:1328px;margin:24px auto;padding:24px;background:white;border:1px solid #dce3ec;border-radius:16px}
svg{width:100%;height:auto;display:block}section{padding:0 20px 16px}h2{font-size:22px;margin:10px 0 16px}
table{width:100%;border-collapse:collapse;font-size:15px}th,td{padding:14px 16px;border-bottom:1px solid #e2e8f0;text-align:center}
th:first-child{text-align:left}thead{background:#f5f7fa;color:#52657d}tbody th{font-weight:500}
a{color:#3469aa;text-decoration:none}a:hover{text-decoration:underline}.pass,.fail{display:inline-block;padding:3px 12px;border-radius:5px;font-size:12px;font-weight:700}
.pass{color:#25634d;background:#eaf6ef}.fail{color:#ad4434;background:#fff0ec}
.notes{font-size:14px;color:#52657d;margin:18px 0 0}.links{border-top:1px solid #e2e8f0;padding-top:14px;font-size:14px}
@media print{body{background:white}main{margin:0;padding:0;border:0}section{break-inside:avoid}}
</style><main>'''
report += figure + '<section><h2>Three properties repairs.</h2><table><thead><tr><th>Property</th><th>v0 · seeded</th><th>v1</th><th>v2</th><th>v3 · final</th></tr></thead><tbody>'
report += ''.join(table_rows) + '</tbody></table>'
# report += '''<p class="notes"><strong>Provenance.</strong> The naturally generated specification passed all four checks. Three disclosed defects were then seeded into v0. Each repair followed actual TLC feedback; the LLM worked in this chat, without a separate API agent.</p>
# <p class="notes"><strong>Scope.</strong> Quint 0.33.0 · TLC via Apalache 0.62.1 · exhaustive finite-state checking. Trusted delivery confirmation; weak fairness of expiry, payment and refund. Properties and assumptions were unchanged. This verifies the model, not deployed software.</p>
# <p class="links"><a href="specs/v3.qnt">Final Quint model</a> &nbsp; / &nbsp; <a href="REPAIRS.md">Repair record</a> &nbsp; / &nbsp; <a href="results.json">Raw results</a> &nbsp; / &nbsp; <a href="README.md">Reproduce</a></p></section></main></html>'''
(ROOT / "report.html").write_text(report)
print("Built report.html from checked evidence.")
