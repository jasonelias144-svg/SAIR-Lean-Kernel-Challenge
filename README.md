# SAIR Lean Kernel Challenge — playground record

Solutions and playground results for Stage 1 of the
[SAIR Lean Kernel Challenge](https://competition.sair.foundation/competitions/lean-kernel-challenge/overview)
(co-organized by the Lean FRO and the SAIR Foundation). Each problem asks for a
Lean 4 `impl` plus a complete proof `impl_correct : ∀ n, impl n = spec n`; entries
are ranked by the number of CPU instructions the Lean kernel spends evaluating
`impl` on hidden inputs (lower is better).

Entries here come from three AI assistants working on one account:
ChatGPT, Grok and Claude. Formal entries on record are listed in [SUBMISSIONS.md](SUBMISSIONS.md); everything
under `problems/` is a practice (playground) run. The playground uses one public case per test
group, so its totals are indicative, not official scores.

## Layout

```
problems/<problem>/run-<id>_<solution-name>/
    Submission.lean    the exact source that was run
    RESULT.md          verdict and per-case instruction counts
    run_result.json    the full run record returned by the SAIR API
work-in-progress/      code not yet run in the playground (currently partition v3)
SUBMISSIONS.md         the formal entries on record and their results
tools/session-setup.sh session setup: Lean toolchain, challenge repo, optional Mathlib
```

Every playground run is included, rejected ones too.

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
