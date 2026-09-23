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
| primecount | 479 | 2026-09-23 08:47 | [run 224](problems/primecount/run-0224_claude_primecount_bitsieve_kernighan_002/) | Claude | 25,351,692 |
| partition | 480 | 2026-09-23 08:48 | [work-in-progress/partition-v3](work-in-progress/partition-v3/) | Claude | not run yet (v2, run 220: 47,526,495) |
| mertens | 481 | 2026-09-23 08:48 | [run 226](problems/mertens/run-0226_claude_mertens_bitsets_001/) | Claude | 83,698,202 |
| ca-rule110 | 482 | 2026-09-23 08:48 | [run 219](problems/ca-rule110/run-0219_claude_rule110_bitword_natrec_002/) | Claude | 112,511,454 |
| permanent | 483 | 2026-09-23 08:48 | [run 222](problems/permanent/run-0222_claude_permanent_packed_subset_dp_001/) | Claude | 659,951,953 |
| sha256 | 484 | 2026-09-23 08:48 | [run 221](problems/sha256/run-0221_claude_sha256_fused_rounds_001/) | Claude | 14,532,311,718 |
| fib | 489 | 2026-09-23 | [run 228](problems/fib/run-0228_claude_fib_cps_doubling_001/) | Claude | 12,721,449 |
| polydisc | — | — | not submitted (only the spec baseline exists) | — | — |

Notes:

- partition v3 passed the contest's local judge (same pipeline as the official
  one) but has not had a playground run. If it is rejected, resubmit v2 (run 220).
- Official scores use two hidden inputs per group (six cases), so they will be
  roughly double the playground totals above.

## Official results

Not published yet. This section will be filled in from the daily standings.

## History

| Date (UTC) | Submission | Problem | Note |
|---|---:|---|---|
| 2026-09-23 | 479–485 | 7 problems | First formal entries |
| 2026-09-23 | 489 | fib | Replaces 485 (ChatGPT placeholder) with Claude's CPS fast doubling |
