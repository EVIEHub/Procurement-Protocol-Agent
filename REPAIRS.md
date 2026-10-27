# Three repair rounds

The LLM generated `specs/generated.qnt`; all four properties passed.
For this non-blinded demonstration, the LLM then seeded three defects into v0:
payment after shipment, no escrow debit, and a disabled refund action.

Each round used the current specification and its four TLC check outputs.
The LLM made the following changes after reading the counterexample;
all four properties were rechecked after each change.

| Round | Checker feedback | LLM repair |
|---|---|---|
| v0 → v1 | [Payment while confirmation is false](logs/v0-noPaymentWithoutConfirmation.log) | In `pay`, replace `s.shipped` with `s.confirmed`. |
| v1 → v2 | [Buyer / escrow / seller = 0 / 1 / 1](logs/v1-moneyConserved.log) | In `pay`, replace `escrow: s.escrow` with `escrow: s.escrow - 1`. |
| v2 → v3 | [Expired escrow can stutter forever](logs/v2-noLockedFunds.log) | Remove the constant `false` guard from `refund`. |

Properties and fairness formulas were unchanged. Final payment and refund
paths were both reachable. The source versions retain the exact changes;
the linked raw logs retain the counterexamples, without copying them here.
The logs are replaced on recheck, so the selected trace may vary.

The LLM repairs were performed in the chat. `check.py` rechecks saved versions;
it does not call an LLM. This is a controlled demonstration, not a repair benchmark.
