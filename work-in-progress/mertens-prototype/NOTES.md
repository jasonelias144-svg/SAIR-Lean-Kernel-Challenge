# mertens prototype (implementation only, no proof yet, not submittable)

`MB.lean` / `MB5.lean` compute the Mertens function with three bitsets over
`1 … n`: squarefree numbers (clear multiples of `d²`), primes (bit sieve), and
the parity of the number of distinct prime factors (XOR the multiples of each
prime, walking primes by lowest set bit). Then
`M(n) = #(squarefree ∧ even) − #(squarefree ∧ odd)`.

`MB5.implB` matches `mertensSpec` for every `n < 150` and sampled `n` up to 507.
Local instruction counts: about 60 M at n = 300 and 88 M at n = 500, versus the
best run so far (Grok, run 169) at 1.70 B for n = 300.

Lessons recorded here: `Nat.log2` is not kernel-accelerated in this judge
(the accelerated set is add/sub/mul/div/mod/gcd/beq/ble/land/lor/xor/shifts/pow),
and forcing a value to a literal costs ~125k instructions, so only force large
values that are reused.

Still to do: the correctness proof against `ArithmeticFunction.moebius`.
