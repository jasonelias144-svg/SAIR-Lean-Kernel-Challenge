# mertens v3 (not yet run in the playground)

New algorithm, complete proof (~900 lines), passes the local judge.

The run-226 version walked **every** prime `p ≤ n` (95 of them for n = 500) and
counted set bits one kernel step at a time. v3 only touches the primes
`p ≤ √n` (8 for n = 500) and counts with two `mod`s:

* Each `k ≤ n` owns a `w`-bit field. Three packed vectors:
  `F_k` = product of processed primes dividing `k`, `P_k` = parity of their
  count, `Q_k` = no processed `p²` divides `k`.
* Processing prime `p`: pattern `M` of fields `p, 2p, …` (one closed form);
  `F += (p − 1)·(F & M·(2^w − 1))`, `P ^= M`, clear multiples of `p²` in `Q`.
  Candidates `2, 3, 6j ± 1`; a candidate is prime iff its own `F` field is
  still `1` (so `25`, `35`, … are skipped correctly).
* Once `p² > n`: a squarefree `k ≤ n` has at most one prime factor `≥ √n`,
  and has one iff `F_k < k`, which is one packed subtraction against the
  identity vector `Σ k·X^k` plus a guard bit.
  `μ(k) = Q_k · (−1)^(P_k + [F_k < k])`.
* `2^w ≡ 1 (mod 2^w − 1)`, so `#{μ = 1}` and `#{μ = −1}` are one `mod` each.

Local kernel instruction counts (`tools/icount-kernel.sh`; `Int` results carry a
~0.8–1.0M baseline):

| n | run 226 version | v3 |
|---:|---:|---:|
| 25 | 10.38 M | 2.81 M |
| 150 | — | 3.15 M |
| 300 | 59.96 M | 3.93 M |
| 500 | — | 4.02 M |

Estimated official six-case total: ~167 M → ~15 M (leader: 1.68 M).

Queued for the next mertens playground slot.
