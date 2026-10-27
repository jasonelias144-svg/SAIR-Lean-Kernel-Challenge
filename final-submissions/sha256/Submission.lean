import Spec

/-!
# SHA-256 chain: fused schedule and rounds

Each hash runs the 64 rounds in a single `Nat.rec` loop; round constants are
read from `Kp`, the spec's `K` packed into one number. The eight working variables `a … h` and a sliding window `w0 … w15` of the
next sixteen message-schedule words are passed as arguments. After a round,
the window shifts by one and the schedule word sixteen places ahead is appended
(only evaluated if a later round needs it). The chain itself is a `Nat.rec`.

Everything is written with `Nat.land`, `Nat.add`, … and literal shift amounts,
masking exactly where the spec's `add32` / `rotr32` mask. Each fused round is
therefore definitionally the spec's `round` (`round_eq`), and each new
schedule word is definitionally the spec's (`newWord_eq`). Why the kernel is
cheaper this way: no type-class unfolding per word operation, no list is grown,
measured, dropped from or indexed, and there is no structural-recursion
machinery (`brecOn`) in the hot loops.

`rounds_eq` shows the fused loop equals the spec's `rounds` over
`K.zip (extendW 48 block)`, via the window schedule `sched` (`extendW_eq`)
and `klist_64` (the constants read from `Kp` are `K`, checked by evaluation).
-/

namespace Submission

/-! ## Implementation -/

/-- The 64 round constants packed into one number, `K[0]` in the highest 32 bits,
so constant `K[63 - j]` is `(Kp >>> 32 * j) &&& 0xffffffff`. Built from the spec's
`K` (the kernel evaluates this closed term once per check). -/
def Kp : Nat := K.foldl (fun acc k => Nat.lor (Nat.shiftLeft acc 32) k) 0

/-- Round constant used when `j + 1` rounds remain. -/
def kAt (j : Nat) : Nat := Nat.land (Nat.shiftRight Kp (Nat.mul 32 j)) 4294967295

/-- The fused loop: `roundsK r` runs the last `r` of the 64 rounds. -/
def roundsK (r : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Digest :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Digest)
    (fun a b c d e f g h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨a, b, c, d, e, f, g, h⟩)
    (fun j ih a b c d e f g h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 =>
      let k := kAt j
      -- T1 of FIPS 180-4, with `w0` the current schedule word
      let t1 :=
        (Nat.land (Nat.add h (Nat.land (Nat.add (Nat.xor (Nat.xor (Nat.land (Nat.lor (Nat.shiftRight e
        6) (Nat.shiftLeft e 26)) 4294967295) (Nat.land (Nat.lor (Nat.shiftRight e 11)
        (Nat.shiftLeft e 21)) 4294967295)) (Nat.land (Nat.lor (Nat.shiftRight e 25)
        (Nat.shiftLeft e 7)) 4294967295)) (Nat.land (Nat.add (Nat.xor (Nat.land e f) (Nat.land
        (Nat.xor e 4294967295) g)) (Nat.land (Nat.add k w0) 4294967295)) 4294967295))
        4294967295)) 4294967295)
      ih
        (Nat.land (Nat.add t1 (Nat.land (Nat.add (Nat.xor (Nat.xor (Nat.land (Nat.lor (Nat.shiftRight a
        2) (Nat.shiftLeft a 30)) 4294967295) (Nat.land (Nat.lor (Nat.shiftRight a 13)
        (Nat.shiftLeft a 19)) 4294967295)) (Nat.land (Nat.lor (Nat.shiftRight a 22)
        (Nat.shiftLeft a 10)) 4294967295)) (Nat.xor (Nat.xor (Nat.land a b) (Nat.land a c))
        (Nat.land b c))) 4294967295)) 4294967295)
        a b c
        (Nat.land (Nat.add d t1) 4294967295)
        e f g
        w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        -- schedule word 16 places ahead: σ₁(w14) + w9 + σ₀(w1) + w0
        (Nat.land (Nat.add (Nat.land (Nat.add (Nat.xor (Nat.xor (Nat.land (Nat.lor (Nat.shiftRight w14
        17) (Nat.shiftLeft w14 15)) 4294967295) (Nat.land (Nat.lor (Nat.shiftRight w14 19)
        (Nat.shiftLeft w14 13)) 4294967295)) (Nat.shiftRight w14 10)) w9) 4294967295) (Nat.land
        (Nat.add (Nat.xor (Nat.xor (Nat.land (Nat.lor (Nat.shiftRight w1 7) (Nat.shiftLeft w1
        25)) 4294967295) (Nat.land (Nat.lor (Nat.shiftRight w1 18) (Nat.shiftLeft w1 14))
        4294967295)) (Nat.shiftRight w1 3)) w0) 4294967295)) 4294967295))
    r

/-- One SHA-256 of a digest (one padded block), as in the spec's `sha256step`. -/
def stepK (d : Digest) : Digest :=
  let f := roundsK 64 iv.a iv.b iv.c iv.d iv.e iv.f iv.g iv.h
    d.a d.b d.c d.d d.e d.f d.g d.h 0x80000000 0 0 0 0 0 0 256
  ⟨add32 iv.a f.a, add32 iv.b f.b, add32 iv.c f.c, add32 iv.d f.d, add32 iv.e f.e,
    add32 iv.f f.f, add32 iv.g f.g, add32 iv.h f.h⟩

/-- The chain: `stepK` applied `t` times. -/
def chain (t : Nat) (d : Digest) : Digest :=
  Nat.rec (motive := fun _ => Digest) d (fun _ acc => stepK acc) t

def impl (n : Nat) : Nat :=
  encodeDigest (chain (Nat.shiftRight n 32) (seedDigest (Nat.land n 4294967295)))

/-! ## Correctness -/

/-- The spec's schedule word sixteen places after `w0`. -/
def newWord (w0 w1 w9 w14 : Nat) : Nat :=
  add32 (add32 (smallSigma1 w14) w9) (add32 (smallSigma0 w1) w0)

/-- `k` further schedule words generated from a 16-word window. -/
def sched : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat → Nat → Nat → Nat → List Nat
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => []
  | k + 1, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15 =>
    newWord w0 w1 w9 w14 :: sched k w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      (newWord w0 w1 w9 w14)

theorem round_eq (a b c d e f g h k w0 : Nat) :
    round ⟨a, b, c, d, e, f, g, h⟩ k w0 =
      let t1 :=
        (Nat.land (Nat.add h (Nat.land (Nat.add (Nat.xor (Nat.xor (Nat.land (Nat.lor (Nat.shiftRight e
        6) (Nat.shiftLeft e 26)) 4294967295) (Nat.land (Nat.lor (Nat.shiftRight e 11)
        (Nat.shiftLeft e 21)) 4294967295)) (Nat.land (Nat.lor (Nat.shiftRight e 25)
        (Nat.shiftLeft e 7)) 4294967295)) (Nat.land (Nat.add (Nat.xor (Nat.land e f) (Nat.land
        (Nat.xor e 4294967295) g)) (Nat.land (Nat.add k w0) 4294967295)) 4294967295))
        4294967295)) 4294967295)
      ⟨(Nat.land (Nat.add t1 (Nat.land (Nat.add (Nat.xor (Nat.xor (Nat.land (Nat.lor (Nat.shiftRight a
        2) (Nat.shiftLeft a 30)) 4294967295) (Nat.land (Nat.lor (Nat.shiftRight a 13)
        (Nat.shiftLeft a 19)) 4294967295)) (Nat.land (Nat.lor (Nat.shiftRight a 22)
        (Nat.shiftLeft a 10)) 4294967295)) (Nat.xor (Nat.xor (Nat.land a b) (Nat.land a c))
        (Nat.land b c))) 4294967295)) 4294967295),
        a, b, c,
        (Nat.land (Nat.add d t1) 4294967295),
        e, f, g⟩ := rfl

theorem newWord_eq (w0 w1 w9 w14 : Nat) :
    newWord w0 w1 w9 w14 =
      (Nat.land (Nat.add (Nat.land (Nat.add (Nat.xor (Nat.xor (Nat.land (Nat.lor (Nat.shiftRight w14
      17) (Nat.shiftLeft w14 15)) 4294967295) (Nat.land (Nat.lor (Nat.shiftRight w14 19)
      (Nat.shiftLeft w14 13)) 4294967295)) (Nat.shiftRight w14 10)) w9) 4294967295) (Nat.land
      (Nat.add (Nat.xor (Nat.xor (Nat.land (Nat.lor (Nat.shiftRight w1 7) (Nat.shiftLeft w1
      25)) 4294967295) (Nat.land (Nat.lor (Nat.shiftRight w1 18) (Nat.shiftLeft w1 14))
      4294967295)) (Nat.shiftRight w1 3)) w0) 4294967295)) 4294967295) := rfl

theorem extendW_eq : ∀ (k : Nat) (pre : List Nat) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Nat),
    extendW k (pre ++ [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15]) =
      pre ++ [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] ++
        sched k w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
  | 0, pre, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [extendW, sched]
  | k + 1, pre, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15 => by
    have hdrop : (pre ++ [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15]).drop
        ((pre ++ [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15]).length - 16) =
        [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] := by
      simp
    simp only [extendW]
    rw [hdrop]
    have happ : pre ++ [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] ++
        [newWord w0 w1 w9 w14] =
        (pre ++ [w0]) ++ [w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
          newWord w0 w1 w9 w14] := by
      simp
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [show add32 (add32 (smallSigma1 w14) w9) (add32 (smallSigma0 w1) w0) = newWord w0 w1 w9 w14
      from rfl, happ, extendW_eq k (pre ++ [w0])]
    simp only [sched, List.append_assoc, List.cons_append, List.nil_append]

theorem zip_append_of_le {α β : Type} : ∀ (ks : List α) (l r : List β),
    ks.length ≤ l.length → ks.zip (l ++ r) = ks.zip l
  | [], _, _, _ => by simp
  | _ :: _, [], _, h => by simp at h
  | k :: ks, x :: l, r, h => by
    simp only [List.cons_append, List.zip_cons_cons]
    rw [zip_append_of_le ks l r (by simp at h; omega)]

/-- The constants `roundsK r` walks through, in order. -/
def klist : Nat → List Nat
  | 0 => []
  | j + 1 => kAt j :: klist j

theorem klist_length : ∀ r, (klist r).length = r
  | 0 => rfl
  | r + 1 => by simp [klist, klist_length r]

theorem klist_64 : klist 64 = K := by decide

/-- The fused loop equals the spec's rounds over the window schedule. -/
theorem rounds_eq : ∀ (r n a b c d e f g h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Nat),
    r ≤ n + 16 →
    roundsK r a b c d e f g h w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 =
      rounds ((klist r).zip ([w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] ++
        sched n w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15)) ⟨a, b, c, d, e, f, g, h⟩
  | 0, _, a, b, c, d, e, f, g, h, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [rounds, klist]; rfl
  | r + 1, n, a, b, c, d, e, f, g, h, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, hlen => by
    simp only [klist, List.cons_append, List.zip_cons_cons, rounds]
    rw [round_eq]
    show roundsK r _ a b c _ e f g w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
      (newWord w0 w1 w9 w14) = _
    cases n with
    | zero =>
      rw [rounds_eq r 0 _ a b c _ e f g w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        (newWord w0 w1 w9 w14) (by omega)]
      simp only [sched, List.append_nil]
      rw [show [w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, newWord w0 w1 w9 w14]
        = [w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15] ++ [newWord w0 w1 w9 w14]
        from rfl, zip_append_of_le (klist r) _ _ (by simp [klist_length]; omega)]
    | succ n =>
      rw [rounds_eq r n _ a b c _ e f g w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        (newWord w0 w1 w9 w14) (by omega)]
      simp only [sched, List.cons_append, List.nil_append]

theorem stepK_eq (d : Digest) : stepK d = sha256step d := by
  have h := extendW_eq 48 [] d.a d.b d.c d.d d.e d.f d.g d.h 0x80000000 0 0 0 0 0 0 256
  simp only [List.nil_append] at h
  have hr := rounds_eq 64 48 iv.a iv.b iv.c iv.d iv.e iv.f iv.g iv.h
    d.a d.b d.c d.d d.e d.f d.g d.h 0x80000000 0 0 0 0 0 0 256 (by decide)
  unfold stepK sha256step compress
  dsimp only
  rw [h, hr, klist_64]

theorem iterDigest_succ' (step : Digest → Digest) :
    ∀ t d, iterDigest step (t + 1) d = step (iterDigest step t d)
  | 0, _ => rfl
  | t + 1, d => by
    show iterDigest step (t + 1) (step d) = step (iterDigest step (t + 1) d)
    rw [iterDigest_succ' step t (step d)]
    rfl

theorem chain_eq : ∀ t d, chain t d = iterSha t d
  | 0, _ => rfl
  | t + 1, d => by
    show stepK (chain t d) = _
    rw [chain_eq t d, stepK_eq]
    exact (iterDigest_succ' sha256step t d).symm

theorem impl_correct : ∀ n, impl n = sha256Spec n := by
  intro n
  show encodeDigest (chain (n >>> 32) (seedDigest (n &&& 4294967295))) = _
  rw [chain_eq]
  rfl

end Submission
