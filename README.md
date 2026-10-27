# Quint procurement

[Diagram and check results](report.html) · [Repair record](REPAIRS.md) · [Final specification](specs/v3.qnt)

Creators: Brian Qian, Fengxiang He

This prototype is intended for demonstration and quick validation: GPT in Codex generated and repaired the specifications over three fixed repair rounds, while Quint/TLC checked the properties and produced counterexamples. As more rules are added, an open-source model could generate and repair specifications in an automated loop, with Quint/TLC continuing to verify each round.

## Model and assumptions

We consider one buyer, one seller, one order, one unit of money in this demonstration. We then consider five rules: (1) depositing into escrow does not count as paying the seller. (2) buyer should confirm the delivery before expiry. (3) Once confirmed, payment should be made even after expiry. (4) If the order is not confirmed by expiry, it is refunded. (5) Expiry, payment, and refund satisfy weak fairness; cooperation of buyer and seller is not assumed.

Four properties are checked: no payment without confirmation, no double payment,fund conservation and prevention of fund lock-up.


## Running

Local dependencies are bundled in `.tools/` and `.quint/`; the original Codex working directory is not needed. From this directory run:

```sh
sh run-local.sh
python3 render.py
```

On other machines you need Node.js 22+, Java 21, and Python 3.9+:

```sh
npm ci
export QUINT_HOME="$PWD/.quint"
python3 check.py
python3 render.py
```

The first run needs network access to download the verification backend. Quint is pinned to 0.33.0; TLC comes from Apalache 0.62.1.

## Files

| File | Purpose |
|---|---|
| `specs/` | Natural initial version and v0–v3, keeping the experiment history |
| `check.py` | Invokes Quint/TLC; records results and raw counterexamples |
| `logs/` | Full check output; the sole raw record of counterexamples |
| `results.json` | Results and spec hashes for the report script |
| `render.py` → `report.html` | Builds the single display file, with diagram and table |
| `REPAIRS.md` | Three rounds of feedback, changes, and raw-log links |
| `run-local.sh` / `tlc.json` | Local environment entry point / TLC memory and thread config |
| `package.json` / `package-lock.json` | Dependency declaration / exact installed versions |

Tool references: [Quint CLI](https://quint.sh/docs/quint) ·
[model checkers](https://quint.sh/docs/model-checkers) ·
[weak fairness example](https://github.com/quint-co/quint/blob/main/examples/language-features/weakFairness.qnt)

## Counterexample dataset

Find the dataset in [data/counterexamples.json](data/counterexamples.json): a JSON array with one entry per failed check. Each entry contains `version`, `property`, `states` (step-by-step actions and variable values), `loop` (null for a finite trace), and `source_log` (the original TLC log).
