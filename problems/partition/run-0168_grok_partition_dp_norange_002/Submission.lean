import Spec

/-!
1-D DP, same recurrence as the first file.

Change vs run 167: no `List.range`; each part-size scan starts at
that part. `step` is only applied at in-range indices `≥ part`.
-/

namespace Submission

theorem range_zero : List.range 0 = [] := rfl

theorem range_one : List.range 1 = [0] := rfl

theorem foldl_add_left (xs : List Nat) (a : Nat) :
    xs.foldl (· + ·) a = a + xs.foldl (· + ·) 0 := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (a + x)]
    have hx := ih x
    have : (0 + x) = x := Nat.zero_add x
    rw [this, hx]
    omega

theorem foldl_add_cons (x : Nat) (xs : List Nat) :
    (x :: xs).foldl (· + ·) 0 = x + xs.foldl (· + ·) 0 := by
  rw [List.foldl_cons, foldl_add_left, Nat.zero_add]

theorem range_succ_eq (n : Nat) : List.range (n + 1) = List.range n ++ [n] :=
  List.range_succ (n := n)

theorem range_eq_zero_cons (t : Nat) :
    List.range (t + 1) = 0 :: (List.range t).map (· + 1) := by
  induction t with
  | zero =>
    rw [range_one, range_zero]
    simp
  | succ t ih =>
    have hmid : List.range (t + 2) =
        (0 :: (List.range t).map (· + 1)) ++ [t + 1] := by
      rw [range_succ_eq (t + 1), ih]
    rw [hmid]
    have happ : (0 :: (List.range t).map (· + 1)) ++ [t + 1] =
        0 :: ((List.range t).map (· + 1) ++ [t + 1]) := rfl
    rw [happ]
    apply congrArg (List.cons 0)
    have hmap : (List.range t).map (· + 1) ++ [t + 1] =
        (List.range (t + 1)).map (· + 1) := by
      rw [range_succ_eq t, List.map_append]
      simp
    exact hmap

theorem partAux_succ_of_lt (k m : Nat) (h : m < k + 1) :
    partAux (k + 1) m = partAux k m := by
  change
    ((List.range (m / (k + 1) + 1)).map (fun j => partAux k (m - j * (k + 1)))).foldl (· + ·) 0 =
      partAux k m
  rw [Nat.div_eq_of_lt h, range_one]
  simp

theorem sub_succ_mul (m j p : Nat) :
    m - (j + 1) * p = m - p - j * p := by
  rw [Nat.add_mul, Nat.one_mul, Nat.sub_add_eq, Nat.sub_right_comm]

theorem partAux_succ_split (k m : Nat) (h : k + 1 ≤ m) :
    partAux (k + 1) m = partAux k m + partAux (k + 1) (m - (k + 1)) := by
  let p := k + 1
  have hpos : 0 < p := Nat.succ_pos k
  have hdiv : m / p = (m - p) / p + 1 := Nat.div_eq_sub_div hpos h
  have hrange :
      List.range (m / p + 1) =
        0 :: (List.range ((m - p) / p + 1)).map (· + 1) := by
    rw [hdiv]
    exact range_eq_zero_cons _
  have hmap :
      (List.range (m / p + 1)).map (fun j => partAux k (m - j * p)) =
        partAux k m ::
          (List.range ((m - p) / p + 1)).map
            (fun j => partAux k (m - (j + 1) * p)) := by
    rw [hrange, List.map_cons]
    simp [List.map_map, Function.comp]
  have htail :
      (List.range ((m - p) / p + 1)).map (fun j => partAux k (m - (j + 1) * p)) =
        (List.range ((m - p) / p + 1)).map (fun j => partAux k (m - p - j * p)) := by
    apply List.map_congr_left
    intro j _
    rw [sub_succ_mul]
  have hsum :
      ((List.range (m / p + 1)).map (fun j => partAux k (m - j * p))).foldl (· + ·) 0 =
        partAux k m +
          ((List.range ((m - p) / p + 1)).map
            (fun j => partAux k (m - p - j * p))).foldl (· + ·) 0 := by
    rw [hmap, foldl_add_cons, htail]
  have hlhs :
      partAux (k + 1) m =
        ((List.range (m / p + 1)).map (fun j => partAux k (m - j * p))).foldl (· + ·) 0 := by
    simp [partAux, p]
  have hrhs :
      partAux (k + 1) (m - (k + 1)) =
        ((List.range ((m - p) / p + 1)).map
          (fun j => partAux k (m - p - j * p))).foldl (· + ·) 0 := by
    simp [partAux, p, Nat.sub_sub]
  rw [hlhs, hrhs, hsum]

def row0 (n : Nat) : List Nat := 1 :: List.replicate n 0

/-- Write one cell `s` for part-size `part`, then continue. Fuel bounds the walk. -/
def addFrom (dp : List Nat) (part s fuel : Nat) : List Nat :=
  match fuel with
  | 0 => dp
  | fuel + 1 =>
    if s < dp.length then
      addFrom (dp.set s (dp.getD s 0 + dp.getD (s - part) 0)) part (s + 1) fuel
    else
      dp

def addPart (dp : List Nat) (part : Nat) : List Nat :=
  addFrom dp part part (dp.length - part)

def row (n k : Nat) : List Nat :=
  match k with
  | 0 => row0 n
  | k + 1 => addPart (row n k) (k + 1)

def impl (n : Nat) : Nat := (row n n).getD n 0

theorem getD_set_eq (l : List Nat) (i v : Nat) (hi : i < l.length) :
    (l.set i v).getD i 0 = v := by
  simp [List.getD, hi]

theorem getD_set_ne (l : List Nat) (i j v : Nat) (h : i ≠ j) :
    (l.set i v).getD j 0 = l.getD j 0 := by
  simp [List.getD, h]

theorem addFrom_length (dp : List Nat) (part s fuel : Nat) :
    (addFrom dp part s fuel).length = dp.length := by
  induction fuel generalizing dp s with
  | zero => simp [addFrom]
  | succ fuel ih =>
    unfold addFrom
    by_cases h : s < dp.length
    · rw [if_pos h, ih, List.length_set]
    · rw [if_neg h]

theorem addPart_length (dp : List Nat) (part : Nat) :
    (addPart dp part).length = dp.length :=
  addFrom_length dp part part (dp.length - part)

theorem row0_length (n : Nat) : (row0 n).length = n + 1 := by
  simp [row0]

theorem row0_getD (n m : Nat) (hm : m ≤ n) :
    (row0 n).getD m 0 = partAux 0 m := by
  cases m with
  | zero =>
    simp [row0, partAux]
  | succ m =>
    have hm' : m < n := Nat.lt_of_succ_le hm
    simp [row0, partAux, List.getD, hm']

/-- After `fuel` writes starting at `s`, with `part = k+1` and `k+1 ≤ s`:
    indices `< s` are already `partAux (k+1)`; newly written cells
    `[s, s+written)` become `partAux (k+1)`; the tail stays `partAux k`. -/
theorem addFrom_spec (n k s fuel : Nat) (dp : List Nat)
    (hlen : dp.length = n + 1)
    (hs : k + 1 ≤ s)
    (hval_low : ∀ m, m < s → m ≤ n → dp.getD m 0 = partAux (k + 1) m)
    (hval_high : ∀ m, s ≤ m → m ≤ n → dp.getD m 0 = partAux k m) :
    (∀ m, m < s + fuel → m ≤ n → (addFrom dp (k + 1) s fuel).getD m 0 = partAux (k + 1) m) ∧
      (∀ m, s + fuel ≤ m → m ≤ n → (addFrom dp (k + 1) s fuel).getD m 0 = partAux k m) := by
  induction fuel generalizing dp s with
  | zero =>
    constructor
    · intro m hm hmn
      have : m < s := by simpa using hm
      exact hval_low m this hmn
    · intro m hm hmn
      have : s ≤ m := by simpa using hm
      exact hval_high m this hmn
  | succ fuel ih =>
    unfold addFrom
    have hsLen : s < dp.length ↔ s ≤ n := by
      rw [hlen]; omega
    by_cases hslt : s < dp.length
    · rw [if_pos hslt]
      have hsn : s ≤ n := hsLen.mp hslt
      have hold : dp.getD s 0 = partAux k s :=
        hval_high s (Nat.le_refl s) hsn
      have hprev : dp.getD (s - (k + 1)) 0 = partAux (k + 1) (s - (k + 1)) := by
        have hsub : s - (k + 1) < s :=
          Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.succ_pos k) hs) (Nat.succ_pos k)
        have hsubn : s - (k + 1) ≤ n := Nat.le_trans (Nat.le_of_lt hsub) hsn
        exact hval_low (s - (k + 1)) hsub hsubn
      have hlen' :
          (dp.set s (dp.getD s 0 + dp.getD (s - (k + 1)) 0)).length = n + 1 := by
        simp [List.length_set, hlen]
      have hcell :
          (dp.set s (dp.getD s 0 + dp.getD (s - (k + 1)) 0)).getD s 0 =
            partAux (k + 1) s := by
        rw [getD_set_eq dp s _ hslt, hold, hprev]
        exact (partAux_succ_split k s hs).symm
      have hlow' :
          ∀ m, m < s + 1 → m ≤ n →
            (dp.set s (dp.getD s 0 + dp.getD (s - (k + 1)) 0)).getD m 0 =
              partAux (k + 1) m := by
        intro m hm hmn
        have hm' : m ≤ s := Nat.lt_succ_iff.mp hm
        by_cases heq : m = s
        · rw [heq]; exact hcell
        · have hlt : m < s := Nat.lt_of_le_of_ne hm' heq
          rw [getD_set_ne dp s m _ (Ne.symm heq)]
          exact hval_low m hlt hmn
      have hhigh' :
          ∀ m, s + 1 ≤ m → m ≤ n →
            (dp.set s (dp.getD s 0 + dp.getD (s - (k + 1)) 0)).getD m 0 =
              partAux k m := by
        intro m hm hmn
        rw [getD_set_ne dp s m _ (Nat.ne_of_lt (Nat.lt_of_succ_le hm))]
        exact hval_high m (Nat.le_trans (Nat.le_succ s) hm) hmn
      have ih :=
        ih (s + 1) (dp.set s (dp.getD s 0 + dp.getD (s - (k + 1)) 0))
          hlen' (Nat.le_trans hs (Nat.le_succ s)) hlow' hhigh'
      simpa [Nat.add_assoc, Nat.add_comm fuel 1, Nat.add_left_comm s 1 fuel] using ih
    · rw [if_neg hslt]
      have hbig : n < s := by
        have : ¬ s ≤ n := mt hsLen.mpr hslt
        omega
      constructor
      · intro m hm hmn
        have : m < s := Nat.lt_of_le_of_lt hmn hbig
        exact hval_low m this hmn
      · intro m hm hmn
        have : s ≤ n := Nat.le_trans (Nat.le_add_right s (fuel + 1)) (Nat.le_trans hm hmn)
        exact (Nat.not_le_of_gt hbig this).elim

theorem addPart_spec (n k : Nat) (dp : List Nat)
    (hlen : dp.length = n + 1)
    (hval : ∀ m, m ≤ n → dp.getD m 0 = partAux k m) :
    ∀ m, m ≤ n → (addPart dp (k + 1)).getD m 0 = partAux (k + 1) m := by
  intro m hm
  have hs : k + 1 ≤ k + 1 := Nat.le_refl _
  have hlow : ∀ m', m' < k + 1 → m' ≤ n → dp.getD m' 0 = partAux (k + 1) m' := by
    intro m' hlt hmn
    rw [hval m' hmn, partAux_succ_of_lt k m' hlt]
  have hhigh : ∀ m', k + 1 ≤ m' → m' ≤ n → dp.getD m' 0 = partAux k m' := by
    intro m' _ hmn
    exact hval m' hmn
  have h := addFrom_spec n k (k + 1) (dp.length - (k + 1)) dp hlen hs hlow hhigh
  change (addFrom dp (k + 1) (k + 1) (dp.length - (k + 1))).getD m 0 = partAux (k + 1) m
  have hbound : m < (k + 1) + (dp.length - (k + 1)) := by
    rw [hlen]
    omega
  exact h.1 m hbound hm

theorem row_spec (n k : Nat) :
    (row n k).length = n + 1 ∧
      ∀ m, m ≤ n → (row n k).getD m 0 = partAux k m := by
  induction k with
  | zero =>
    refine ⟨row0_length n, ?_⟩
    intro m hm
    simpa [row] using row0_getD n m hm
  | succ k ih =>
    simp [row]
    refine ⟨?_, ?_⟩
    · rw [addPart_length, ih.1]
    · exact addPart_spec n k (row n k) ih.1 ih.2

theorem impl_correct : ∀ n, impl n = partitionSpec n := by
  intro n
  simp [impl, partitionSpec]
  exact (row_spec n n).2 n (Nat.le_refl n)

end Submission
