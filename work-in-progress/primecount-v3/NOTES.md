# primecount v3 (playground: accepted, see SUBMISSIONS.md)

New algorithm, complete proof, passes the local judge.

* **Spread fields.** Number `k` owns a `w`-bit field (`2^w > n + 2`); the sieve has
  bit `w·k` set iff `k` is a candidate. In base `2^w` its digits are 0/1, and
  `2^w ≡ 1 (mod 2^w − 1)`, so the number of primes is **one `mod`**:
  `S % (2^w − 1)`. The old version counted set bits one kernel step per prime.
* **Wheel-6 divisors with early exit.** Sieve with `2, 3, 6j+5, 6j+7` and stop
  once `d² > n` (5 rounds for n = 1000 instead of 32).
* **No `Nat.log2` on the fast path.** `log2` is not GMP-accelerated (~0.6M
  instructions per call); `w = 10` for `n < 1022`.
* **`Bool.rec` instead of `cond`.** Saves ~125k–250k per case.

Local kernel instruction counts (`tools/icount-kernel.sh`, includes the ~0.5M
baseline):

| n | run 224 version | v3 |
|---:|---:|---:|
| 50 | 3.97 M | 1.34 M |
| 150 | 7.66 M | 1.65 M |
| 600 | 17.67 M | 2.29 M |
| 1000 | 23.4 M | 2.63 M |

Estimated official six-case total: ~51 M → ~8 M (leader: 1.45 M).

Proof outline: a field invariant `fld w n P S` (bit `i` set iff `w ∣ i`,
`i/w ≤ n`, `P (i/w)`); one lemma per sieve step; a wheel-coverage predicate
turned into primality with `Nat.minFac`; and `pk X f L ≡ Σ f (mod X − 1)` for
the final count.

Queued for the next primecount playground slot.
