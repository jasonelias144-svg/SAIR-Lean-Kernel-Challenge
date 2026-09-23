import Spec

/-!
# Rule 110 on a 256-bit word

The row is kept as one natural number (bit `i` = cell `i`). One step is
`new = (C xor R) or (C and not L)`, where `L` and `R` are the row rotated so
that each cell sees its left or right neighbour. The seeded initial row is
built directly as a number, cell by cell, without the intermediate `List Bool`.

The computational definitions call `Nat.land`, `Nat.xor`, … and raw literals
directly, so the kernel does not unfold type-class instances on every
operation. Each is definitionally equal to the ordinary notation, which the
proofs use.
-/

namespace Submission

/-! ## Implementation -/

/-- `2 ^ 256 - 1`. -/
def mask : Nat :=
  115792089237316195423570985008687907853269984665640564039457584007913129639935

/-- The three rounds of `caMix32`. -/
def g1 (x : Nat) : Nat :=
  Nat.land (Nat.mul (Nat.xor x (Nat.shiftRight x 16)) 2146121005)
    4294967295
def g2 (x : Nat) : Nat :=
  Nat.land (Nat.mul (Nat.xor x (Nat.shiftRight x 15)) 2221713035)
    4294967295
def g3 (x : Nat) : Nat :=
  Nat.land (Nat.xor x (Nat.shiftRight x 16)) 4294967295

def mix (x : Nat) : Nat := g3 (g2 (g1 x))

/-- Initial value (0 or 1) of cell `i ≥ 2`. -/
def cell (seed i : Nat) : Nat :=
  Nat.land (Nat.shiftRight
    (mix (Nat.add seed (Nat.mul (Nat.add i 1) 2654435769))) 31)
    1

/-- Cells `s, s + 1, …, s + k - 1` packed with cell `s` in the lowest bit. -/
def enc (seed : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | s, k + 1 => Nat.add (Nat.mul 2 (enc seed (Nat.add s 1) k)) (cell seed s)

/-- The seeded initial row: cell 0 is on, cell 1 is off, the rest come from `cell`. -/
def initV (seed : Nat) : Nat :=
  Nat.add (Nat.mul 4 (enc seed 2 254)) 1

/-- Bit `i` becomes cell `i + 1` (each cell's right neighbour). -/
def rotR (c : Nat) : Nat :=
  Nat.lor (Nat.shiftRight c 1) (Nat.shiftLeft (Nat.land c 1) 255)

/-- Bit `i` becomes cell `i - 1` (each cell's left neighbour). -/
def rotL (c : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.shiftLeft c 1) mask) (Nat.shiftRight c 255)

def stepV (c : Nat) : Nat :=
  Nat.lor (Nat.xor c (rotR c)) (Nat.land c (Nat.xor mask (rotL c)))

def iterV : Nat → Nat → Nat
  | 0, c => c
  | t + 1, c => iterV t (stepV c)

def impl (n : Nat) : Nat :=
  iterV (Nat.shiftRight n 32) (initV (Nat.land n 4294967295))

/-! ## Encoding rows as numbers -/

theorem encodeRow_cons (b : Bool) (bs : List Bool) :
    encodeRow (b :: bs) = 2 * encodeRow bs + (if b then 1 else 0) := rfl

theorem testBit_encodeRow : ∀ (row : List Bool) (i : Nat),
    (encodeRow row).testBit i = row.getD i false
  | [], i => by simp [encodeRow]
  | b :: bs, 0 => by
    rw [encodeRow_cons, Nat.testBit_zero]
    cases b <;> simp <;> omega
  | b :: bs, i + 1 => by
    rw [encodeRow_cons, Nat.testBit_succ]
    have : (2 * encodeRow bs + (if b then 1 else 0)) / 2 = encodeRow bs := by
      cases b <;> simp <;> omega
    rw [this, testBit_encodeRow bs i]
    simp

theorem encodeRow_lt : ∀ (row : List Bool), encodeRow row < 2 ^ row.length
  | [] => by simp [encodeRow]
  | b :: bs => by
    have := encodeRow_lt bs
    rw [encodeRow_cons, List.length_cons, Nat.pow_succ]
    split <;> omega

/-! ## The initial row -/

theorem mix_eq (x : Nat) : mix x = caMix32 x := rfl

theorem cell_eq (seed i : Nat) :
    cell seed i =
      if (caMix32 (seed + (i + 1) * 0x9e3779b9)).testBit 31 then 1 else 0 := by
  show (mix (seed + (i + 1) * 0x9e3779b9) >>> 31) &&& 1 = _
  rw [mix_eq, Nat.and_one_is_mod]
  generalize caMix32 (seed + (i + 1) * 0x9e3779b9) = m
  have h : m.testBit 31 = (m >>> 31).testBit 0 := by
    rw [Nat.testBit_shiftRight]
  rw [h, Nat.testBit_zero]
  have := Nat.mod_two_eq_zero_or_one (m >>> 31)
  rcases this with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp

theorem enc_eq (seed : Nat) (f : Nat → Bool)
    (hf : ∀ i, 2 ≤ i → cell seed i = if f i then 1 else 0) :
    ∀ k s, 2 ≤ s → enc seed s k = encodeRow ((List.range' s k).map f)
  | 0, _, _ => rfl
  | k + 1, s, hs => by
    show 2 * enc seed (s + 1) k + cell seed s = _
    rw [List.range'_succ, List.map_cons, encodeRow_cons, enc_eq seed f hf k (s + 1) (by omega),
      hf s hs]

theorem initV_eq (seed : Nat) : initV seed = encodeRow (initRowFor seed) := by
  unfold initRowFor ruleWidth
  rw [List.range_eq_range', show (256 : Nat) = 254 + 1 + 1 from rfl, List.range'_succ,
    List.range'_succ, List.map_cons, List.map_cons, encodeRow_cons, encodeRow_cons]
  show 4 * enc seed 2 254 + 1 = _
  have hF := enc_eq seed
    (fun i => if i = 0 then true else if i = 1 then false
      else (caMix32 (seed + (i + 1) * 2654435769)).testBit 31)
    (fun i hi => by
      rw [cell_eq, if_neg (show i ≠ 0 by omega), if_neg (show i ≠ 1 by omega)])
    254 2 (Nat.le_refl 2)
  rw [show (0 + 1 + 1 : Nat) = 2 from rfl, ← hF]
  simp only [Nat.zero_add, if_true, if_false, show (1 : Nat) ≠ 0 by decide, Bool.false_eq_true]
  omega

/-! ## One step -/

theorem mask_eq : mask = 2 ^ 256 - 1 := by decide

theorem testBit_mask (i : Nat) : mask.testBit i = decide (i < 256) := by
  rw [mask_eq, Nat.testBit_two_pow_sub_one]

theorem testBit_rotR {c : Nat} (hc : c < 2 ^ 256) (i : Nat) :
    (rotR c).testBit i = (decide (i < 256) && c.testBit ((i + 1) % 256)) := by
  show ((c >>> 1) ||| ((c &&& 1) <<< 255)).testBit i = _
  rw [Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, Nat.testBit_and]
  by_cases h1 : i < 255
  · have : (i + 1) % 256 = 1 + i := by omega
    simp [this, show i < 256 by omega, show ¬ (i ≥ 255) by omega]
  · by_cases h2 : i = 255
    · subst h2
      simp [Nat.testBit_lt_two_pow hc]
    · have hb : c.testBit (1 + i) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega)))
      have h1' : Nat.testBit 1 (i - 255) = false :=
        Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
      simp [hb, h1', show ¬ i < 256 by omega]

theorem testBit_rotL {c : Nat} (hc : c < 2 ^ 256) (i : Nat) :
    (rotL c).testBit i = (decide (i < 256) && c.testBit ((i + 255) % 256)) := by
  show (((c <<< 1) &&& mask) ||| (c >>> 255)).testBit i = _
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    testBit_mask]
  by_cases h0 : i = 0
  · subst h0; simp
  · have hb : c.testBit (255 + i) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [hb, Bool.or_false]
    by_cases h : i < 256
    · have : (i + 255) % 256 = i - 1 := by omega
      simp [h, this, show i ≥ 1 by omega]
    · simp [h]

theorem testBit_stepV {c : Nat} (hc : c < 2 ^ 256) (i : Nat) :
    (stepV c).testBit i =
      (decide (i < 256) &&
        rule110 (c.testBit ((i + 255) % 256)) (c.testBit i) (c.testBit ((i + 1) % 256))) := by
  show ((c ^^^ rotR c) ||| (c &&& (mask ^^^ rotL c))).testBit i = _
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_xor, testBit_rotR hc,
    testBit_rotL hc, testBit_mask]
  by_cases h : i < 256
  · simp only [h, decide_true, Bool.true_and]
    generalize c.testBit ((i + 255) % 256) = l
    generalize c.testBit i = m
    generalize c.testBit ((i + 1) % 256) = r
    cases l <;> cases m <;> cases r <;> rfl
  · have : c.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [h, this]

theorem getD_stepRow (row : List Bool) (i : Nat) :
    (stepRow row).getD i false =
      (decide (i < row.length) &&
        rule110 (row.getD ((i + row.length - 1) % row.length) false)
          (row.getD i false) (row.getD ((i + 1) % row.length) false)) := by
  by_cases h : i < row.length
  · simp [stepRow, List.getD_eq_getElem?_getD, h]
  · have : (stepRow row).length ≤ i := by simp [stepRow]; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
    simp [h]

theorem length_stepRow (row : List Bool) : (stepRow row).length = row.length := by
  simp [stepRow]

theorem stepV_eq (row : List Bool) (hlen : row.length = 256) :
    encodeRow (stepRow row) = stepV (encodeRow row) := by
  have hc : encodeRow row < 2 ^ 256 := hlen ▸ encodeRow_lt row
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_encodeRow, getD_stepRow, testBit_stepV hc, hlen, testBit_encodeRow,
    testBit_encodeRow, testBit_encodeRow, show i + 256 - 1 = i + 255 by omega]

theorem iterV_eq : ∀ (t : Nat) (row : List Bool), row.length = 256 →
    encodeRow (iterRow t row) = iterV t (encodeRow row)
  | 0, _, _ => rfl
  | t + 1, row, hlen => by
    show encodeRow (iterRow t (stepRow row)) = iterV t (stepV (encodeRow row))
    rw [iterV_eq t (stepRow row) (by rw [length_stepRow, hlen]), stepV_eq row hlen]

/-! ## Correctness -/

theorem impl_correct : ∀ n, impl n = caSpecN n := by
  intro n
  show iterV (n >>> 32) (initV (n &&& 0xffffffff)) = _
  unfold caSpecN caSteps caSeed
  rw [iterV_eq _ _ (by simp [initRowFor, ruleWidth]), initV_eq]

end Submission
