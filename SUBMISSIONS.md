# Formal submissions

Formal entries for Stage 1 of the Lean Kernel Challenge, team **LKC01-T00210**.
For each problem, only the **latest** formal entry before the deadline
(November 20, 2026, 23:59 AoE) counts, even if an earlier one scored better.
So before submitting, make sure the new entry beats the one listed here, check
it in the playground first, and then update this file.

Scores appear in the daily provisional standings (public leaderboard). The
final evaluation runs on hidden inputs after the deadline.

## Current entries

| Problem | Submission | Submitted (UTC) | Source | Author | Playground total (3 public cases) |
|---|---:|---|---|---|---:|
| primecount | 529 | 2026-09-24 01:19 | v3, [run 243](problems/primecount/run-0243_claude_primecount_v3_001/) | Claude | 3,761,393 |
| partition | 480 | 2026-09-23 08:48 | v3, [run 242](problems/partition/run-0242_claude_partition_v3_001/) | Claude | 17,770,587 |
| mertens | 530 | 2026-09-24 01:19 | v3, [run 244](problems/mertens/run-0244_claude_mertens_v3_001/) | Claude | 6,389,272 |
| ca-rule110 | 482 | 2026-09-23 08:48 | [run 219](problems/ca-rule110/run-0219_claude_rule110_bitword_natrec_002/) | Claude | 112,511,454 |
| permanent | 483 | 2026-09-23 08:48 | [run 222](problems/permanent/run-0222_claude_permanent_packed_subset_dp_001/) | Claude | 659,951,953 |
| sha256 | 484 | 2026-09-23 08:48 | [run 221](problems/sha256/run-0221_claude_sha256_fused_rounds_001/) | Claude | 14,532,311,718 |
| fib | 489 | 2026-09-23 | [run 228](problems/fib/run-0228_claude_fib_cps_doubling_001/) | Claude | 12,721,449 |
| polydisc | 1910 | 2026-10-27 13:33 | spec baseline, [run 164](problems/polydisc/run-0164_chatgpt_polydisc_baseline_001/) | ChatGPT | 5,164,713,553 |

Notes:

- partition v3 (entry 480, submitted without a playground run) was
  **accepted** in playground run 242 (17,770,587, down from 47,526,495 for v2 in
  run 220). Entry 480 stands; v2 does not need resubmitting.
- primecount v3 (entry 529, replacing 479) and mertens v3 (entry 530, replacing
  481) were submitted after being accepted in the playground:

  | Problem | Entry | Run | Playground total | Previous entry (playground) | Change |
  |---|---:|---|---:|---:|---:|
  | primecount | 529 | [run 243](problems/primecount/run-0243_claude_primecount_v3_001/) | 3,761,393 | 25,351,692 (run 224, entry 479) | −21,590,299 (−85.16%) |
  | mertens | 530 | [run 244](problems/mertens/run-0244_claude_mertens_v3_001/) | 6,389,272 | 83,698,202 (run 226, entry 481) | −77,308,930 (−92.37%) |

- polydisc (entry 1910) is the organizers' starter, unchanged except for comments:
  `impl := discSpec`, proved by `rfl`. It was accepted in playground run 164.
  It was submitted so that every problem has an entry, not to compete for rank.
- Official scores use two hidden inputs per group (six cases), so they will be
  roughly double the playground totals above.

## How to submit

The format comes from the API guide on the competition site. The file goes in
`payload.text` as plain text. Use a new UUID as `idempotencyKey` for each new
entry, and reuse it only to retry the same request.

```sh
B=https://api.sair.foundation/api/public/v1/competitions/lean-kernel-challenge
LKC_CONTRACT=$(curl -fsS "$B/submission-spec" -H "Authorization: Bearer $SAIR_API_KEY" | jq -er '.data.contractVersion')
jq -n --arg contract "$LKC_CONTRACT" --arg key "$(uuidgen)" --rawfile source Submission.lean \
  '{idempotencyKey: $key, contractVersionAcknowledged: $contract, payload: {problem: "fib", text: $source}}' |
curl -X POST "$B/submissions" -H "Authorization: Bearer $SAIR_API_KEY" \
  -H "Content-Type: application/json" --data-binary @-
```

The response's `rawUploadSha256` is the SHA-256 of the file as uploaded; check
it against `sha256sum Submission.lean`.

## Official results

Daily provisional evaluation of 2026-10-27 (`GET .../submissions/mine`, six
hidden cases per problem, fifteen for permanent). Every entry was **accepted**,
with every case `ok`, the correctness replay `ok`, and the entry eligible for ranking.

| Problem | Entry | Cases ok | Computation total |
|---|---:|---:|---:|
| fib | 489 | 6/6 | 29,938,624 |
| partition | 480 | 6/6 | 42,257,715 |
| mertens | 530 | 6/6 | 13,418,313 |
| primecount | 529 | 6/6 | 7,988,837 |
| permanent | 483 | 15/15 | 3,319,546,039 |
| ca-rule110 | 482 | 6/6 | 225,030,102 |
| sha256 | 484 | 6/6 | 29,039,341,230 |
| polydisc | 1910 | 6/6 | 10,317,863,116 (2026-10-28, its first evaluation) |

On 2026-10-28 all eight entries were accepted again, with every case `ok`. The
seven earlier totals moved by at most 0.12%, which is ordinary measurement
variation.

The final evaluation runs separately after the deadline.

## History

| Date (UTC) | Submission | Problem | Note |
|---|---:|---|---|
| 2026-09-23 | 479–485 | 7 problems | First formal entries |
| 2026-09-23 | 489 | fib | Replaces 485 (ChatGPT placeholder) with Claude's CPS fast doubling |
| 2026-09-24 | — | partition, primecount, mertens | v3 playground runs 242–244, all accepted (no new formal entries) |
| 2026-09-24 | 529, 530 | primecount, mertens | v3 submitted formally, replacing 479 and 481 |
| 2026-10-27 | 1910 | polydisc | Spec baseline (run 164) submitted, so all eight problems have an entry |
| 2026-10-28 | 1910 | polydisc | First daily evaluation: accepted, 6/6 cases `ok`. All eight entries pass |
