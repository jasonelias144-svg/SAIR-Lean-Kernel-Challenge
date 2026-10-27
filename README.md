# SAIR Lean Kernel Challenge — Stage 1 (team LKC01-T00210)

Solutions, playground runs and formal entries for Stage 1 of the
[SAIR Lean Kernel Challenge](https://competition.sair.foundation/competitions/lean-kernel-challenge/overview)
(co-organized by the Lean FRO and the SAIR Foundation). Each problem asks for a
Lean 4 `impl` plus a complete proof `impl_correct : ∀ n, impl n = spec n`; entries
are ranked by the number of CPU instructions the Lean kernel spends evaluating
`impl` on hidden inputs (lower is better).

## Status: complete

All eight Stage 1 problems have a formal entry, each with a complete,
machine-checked correctness proof. Seven passed the official daily evaluation of
2026-10-27 (accepted, every hidden case `ok`). polydisc was submitted later that
day, so its first evaluation is on 2026-10-28. No further entries are planned;
the submission deadline is November 20, 2026, and the final evaluation runs
after it.

The exact submitted files are in [`final-submissions/`](final-submissions/).
Their SHA-256 checksums ([`SHA256SUMS`](final-submissions/SHA256SUMS)) match the
hashes the SAIR server recorded for each upload.

| Problem | Entry | Solution (source run) | Author | Official total |
|---|---:|---|---|---:|
| fib | 489 | [CPS fast doubling](problems/fib/run-0228_claude_fib_cps_doubling_001/) | Claude | 29,938,624 |
| partition | 480 | [packed generating function, v3](problems/partition/run-0242_claude_partition_v3_001/) | Claude | 42,257,715 |
| mertens | 530 | [packed sieve with two-`mod` count, v3](problems/mertens/run-0244_claude_mertens_v3_001/) | Claude | 13,418,313 |
| primecount | 529 | [spread-field sieve, v3](problems/primecount/run-0243_claude_primecount_v3_001/) | Claude | 7,988,837 |
| permanent | 483 | [packed subset DP](problems/permanent/run-0222_claude_permanent_packed_subset_dp_001/) | Claude | 3,319,546,039 |
| ca-rule110 | 482 | [bit-word step with `Nat.rec`](problems/ca-rule110/run-0219_claude_rule110_bitword_natrec_002/) | Claude | 225,030,102 |
| sha256 | 484 | [fused rounds](problems/sha256/run-0221_claude_sha256_fused_rounds_001/) | Claude | 29,039,341,230 |
| polydisc | 1910 | [organizers' spec baseline](problems/polydisc/run-0164_chatgpt_polydisc_baseline_001/) | ChatGPT | first evaluated 2026-10-28 |

Official totals come from the daily evaluation of 2026-10-27. Each is the sum,
over six hidden cases (fifteen for permanent), of the median of three kernel
replays. [SUBMISSIONS.md](SUBMISSIONS.md) has submission times, the earlier
entries these replaced, the full history and the submit command. The polydisc
entry is the organizers' starter (`impl := discSpec`, proved by `rfl`). It was
submitted so that every problem has an entry, not to compete on that problem.

## About this record

The work came from three AI assistants on one account: ChatGPT, Grok and
Claude. Working on this repository: [AGENTS.md](AGENTS.md),
[STATUS.md](STATUS.md) and the
[policy handbook](https://github.com/jasonelias144-svg/policy-handbook). Everything under `problems/` is a playground (practice) run, rejected
runs included. The playground uses one public case per test group, so its
totals are indicative, not official scores.

## Layout

```
final-submissions/<problem>/Submission.lean   the exact file submitted for each problem
final-submissions/SHA256SUMS                  checksums (cd final-submissions && sha256sum -c SHA256SUMS)
problems/<problem>/run-<id>_<solution-name>/
    Submission.lean    the exact source that was run
    RESULT.md          verdict and per-case instruction counts
    run_result.json    the full run record returned by the SAIR API
    NOTES.md           design notes (v3 of partition, primecount, mertens)
SUBMISSIONS.md         formal entries, official results, history, submit command
tools/session-setup.sh session setup: Lean toolchain, challenge repo, optional Mathlib
tools/icount-kernel.sh local kernel instruction counter (valgrind/callgrind)
```

## Best accepted run per problem (playground)

| Problem | Best total instructions | By |
|---|---:|---|
| fib | 12,721,449 | Claude (run 228) |
| partition | 17,770,587 | Claude (run 242) |
| mertens | 6,389,272 | Claude (run 244) |
| primecount | 3,761,393 | Claude (run 243) |
| permanent | 659,951,953 | Claude (run 222) |
| ca-rule110 | 112,511,454 | Claude (run 219) |
| sha256 | 14,532,311,718 | Claude (run 221) |
| polydisc | 5,164,713,553 | ChatGPT (run 164) |

## All runs

| Problem | Run | Solution | Author | Verdict | Total instructions |
|---|---:|---|---|---|---:|
| fib | [157](problems/fib/run-0157_chatgpt_001/RESULT.md) | `chatgpt_001` | ChatGPT | accepted | 30,259,944 |
| fib | [165](problems/fib/run-0165_chatgpt_001/RESULT.md) | `chatgpt_001` | ChatGPT | accepted | 30,263,943 |
| fib | [166](problems/fib/run-0166_chatgpt_fib_two_square_001/RESULT.md) | `chatgpt_fib_two_square_001` | ChatGPT | accepted | 49,389,045 |
| fib | [228](problems/fib/run-0228_claude_fib_cps_doubling_001/RESULT.md) | `claude_fib_cps_doubling_001` | Claude | accepted | 12,721,449 |
| partition | [158](problems/partition/run-0158_chatgpt_partition_baseline_001/RESULT.md) | `chatgpt_partition_baseline_001` | ChatGPT | accepted | 41,498,007,670 |
| partition | [167](problems/partition/run-0167_grok_partition_dp_list_001/RESULT.md) | `grok_partition_dp_list_001` | Grok | accepted | 9,194,300,506 |
| partition | [168](problems/partition/run-0168_grok_partition_dp_norange_002/RESULT.md) | `grok_partition_dp_norange_002` | Grok | accepted | 11,658,183,302 |
| partition | [217](problems/partition/run-0217_claude_partition_packed_gf_001/RESULT.md) | `claude_partition_packed_gf_001` | Claude | accepted | 66,504,475 |
| partition | [220](problems/partition/run-0220_claude_partition_packed_gf_natops_002/RESULT.md) | `claude_partition_packed_gf_natops_002` | Claude | accepted | 47,526,495 |
| partition | [242](problems/partition/run-0242_claude_partition_v3_001/RESULT.md) | `claude_partition_v3_001` | Claude | accepted | 17,770,587 |
| mertens | [159](problems/mertens/run-0159_chatgpt_mertens_baseline_001/RESULT.md) | `chatgpt_mertens_baseline_001` | ChatGPT | accepted | 2,482,959,057 |
| mertens | [169](problems/mertens/run-0169_grok_mertens_minfac_rec_001/RESULT.md) | `grok_mertens_minfac_rec_001` | Grok | accepted | 2,164,283,088 |
| mertens | [226](problems/mertens/run-0226_claude_mertens_bitsets_001/RESULT.md) | `claude_mertens_bitsets_001` | Claude | accepted | 83,698,202 |
| mertens | [244](problems/mertens/run-0244_claude_mertens_v3_001/RESULT.md) | `claude_mertens_v3_001` | Claude | accepted | 6,389,272 |
| primecount | [160](problems/primecount/run-0160_chatgpt_primecount_baseline_001/RESULT.md) | `chatgpt_primecount_baseline_001` | ChatGPT | accepted | 2,130,756,878 |
| primecount | [170](problems/primecount/run-0170_grok_primecount_minfac_succ_001/RESULT.md) | `grok_primecount_minfac_succ_001` | Grok | accepted | 2,125,836,371 |
| primecount | [223](problems/primecount/run-0223_claude_primecount_bitsieve_001/RESULT.md) | `claude_primecount_bitsieve_001` | Claude | accepted | 42,128,035 |
| primecount | [224](problems/primecount/run-0224_claude_primecount_bitsieve_kernighan_002/RESULT.md) | `claude_primecount_bitsieve_kernighan_002` | Claude | accepted | 25,351,692 |
| primecount | [243](problems/primecount/run-0243_claude_primecount_v3_001/RESULT.md) | `claude_primecount_v3_001` | Claude | accepted | 3,761,393 |
| permanent | [161](problems/permanent/run-0161_chatgpt_permanent_baseline_001/RESULT.md) | `chatgpt_permanent_baseline_001` | ChatGPT | accepted | 141,593,435,814 |
| permanent | [222](problems/permanent/run-0222_claude_permanent_packed_subset_dp_001/RESULT.md) | `claude_permanent_packed_subset_dp_001` | Claude | accepted | 659,951,953 |
| ca-rule110 | [162](problems/ca-rule110/run-0162_chatgpt_rule110_baseline_001/RESULT.md) | `chatgpt_rule110_baseline_001` | ChatGPT | accepted | 1,078,974,409 |
| ca-rule110 | [214](problems/ca-rule110/run-0214_grok-solution-2/RESULT.md) | `grok-solution-2` | Grok | rejected | — |
| ca-rule110 | [218](problems/ca-rule110/run-0218_claude_rule110_bitword_001/RESULT.md) | `claude_rule110_bitword_001` | Claude | accepted | 177,151,661 |
| ca-rule110 | [219](problems/ca-rule110/run-0219_claude_rule110_bitword_natrec_002/RESULT.md) | `claude_rule110_bitword_natrec_002` | Claude | accepted | 112,511,454 |
| sha256 | [163](problems/sha256/run-0163_chatgpt_sha256_baseline_001/RESULT.md) | `chatgpt_sha256_baseline_001` | ChatGPT | accepted | 91,478,450,830 |
| sha256 | [221](problems/sha256/run-0221_claude_sha256_fused_rounds_001/RESULT.md) | `claude_sha256_fused_rounds_001` | Claude | accepted | 14,532,311,718 |
| polydisc | [164](problems/polydisc/run-0164_chatgpt_polydisc_baseline_001/RESULT.md) | `chatgpt_polydisc_baseline_001` | ChatGPT | accepted | 5,164,713,553 |

## Notes on what made the kernel fast

These held across problems (measured with valgrind and confirmed by the playground):

- **Pack data into one big `Nat`.** The kernel does `Nat` add/sub/mul/div/mod/
  bitwise/shift/pow with GMP, so a whole DP row, bitset or vector becomes a few
  operations (partition, Rule 110, permanent, primecount).
- **Call `Nat.add`, `Nat.land`, … directly** rather than `+`, `&&&`: each
  type-class-routed operation costs extra unfolding.
- **Write loops with `Nat.rec`**, not structural recursion: the `brecOn`
  encoding was up to 36× more expensive for a 16-argument loop.
- **The kernel does not cache big results.** A large value used several times
  is recomputed each time; forcing it to a literal once (`Nat.casesOn` trick)
  fixes that, but forcing costs ~125k instructions, so only force large reused values.
- **`Nat.log2` is not accelerated** in this judge.
- **`noncomputable` definitions are rejected**: the judge wraps `impl` in an
  ordinary `def` (this is why run 214 failed; that solution was also filed under
  the wrong problem).
