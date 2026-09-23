import Spec

/-!
1-D DP: start from `partAux 0`, then add part sizes 1, 2, …, n.
Left-to-right update implements
`partAux (k+1) m = partAux k m + partAux (k+1) (m-(k+1))`.
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

def step (acc : List Nat) (s part : Nat) : List Nat :=
  if s < part then acc else acc.set s (acc.getD s 0 + acc.getD (s - part) 0)

def addPartPrefix (dp : List Nat) (part t : Nat) : List Nat :=
  (List.range t).foldl (fun acc s => step acc s part) dp

def addPart (dp : List Nat) (part : Nat) : List Nat :=
  addPartPrefix dp part dp.length

def row (n k : Nat) : List Nat :=
  (List.range k).foldl (fun dp i => addPart dp (i + 1)) (row0 n)

def impl (n : Nat) : Nat := (row n n).getD n 0

theorem getD_set_eq (l : List Nat) (i v : Nat) (hi : i < l.length) :
    (l.set i v).getD i 0 = v := by
  simp [List.getD, List.getElem?_set, hi]

theorem getD_set_ne (l : List Nat) (i j v : Nat) (h : i ≠ j) :
    (l.set i v).getD j 0 = l.getD j 0 := by
  simp [List.getD, List.getElem?_set, h]

theorem step_length (acc : List Nat) (s part : Nat) :
    (step acc s part).length = acc.length := by
  unfold step
  by_cases h : s < part
  · rw [if_pos h]
  · rw [if_neg h, List.length_set]

theorem foldl_addPart_length (dp : List Nat) (part : Nat) (ks : List Nat) :
    (ks.foldl (fun acc s => step acc s part) dp).length = dp.length := by
  induction ks generalizing dp with
  | nil => simp
  | cons s ks ih =>
    rw [List.foldl_cons, ih, step_length]

theorem addPartPrefix_length (dp : List Nat) (part t : Nat) :
    (addPartPrefix dp part t).length = dp.length :=
  foldl_addPart_length dp part (List.range t)

theorem addPart_length (dp : List Nat) (part : Nat) :
    (addPart dp part).length = dp.length :=
  addPartPrefix_length dp part dp.length

theorem addPartPrefix_zero (dp : List Nat) (part : Nat) :
    addPartPrefix dp part 0 = dp := by
  simp [addPartPrefix, range_zero]

theorem addPartPrefix_succ (dp : List Nat) (part t : Nat) :
    addPartPrefix dp part (t + 1) = step (addPartPrefix dp part t) t part := by
  unfold addPartPrefix
  rw [range_succ_eq, List.foldl_append]
  simp [List.foldl]

theorem row0_length (n : Nat) : (row0 n).length = n + 1 := by
  simp [row0]

theorem row0_getD (n m : Nat) (hm : m ≤ n) :
    (row0 n).getD m 0 = partAux 0 m := by
  cases m with
  | zero =>
    simp [row0, partAux]
  | succ m =>
    have hm' : m < n := Nat.lt_of_succ_le hm
    simp [row0, partAux, List.getD, List.getElem?_cons_succ, List.getElem?_replicate, hm']

/-- After `t` steps of adding `part = k+1` to a correct `k`-row of length `n+1`:
    indices `< t` are `partAux (k+1)`, indices `≥ t` are still `partAux k`. -/
theorem addPartPrefix_spec (n k t : Nat) (dp : List Nat)
    (hlen : dp.length = n + 1)
    (hval : ∀ m, m ≤ n → dp.getD m 0 = partAux k m)
    (ht : t ≤ n + 1) :
    (addPartPrefix dp (k + 1) t).length = n + 1 ∧
      (∀ m, m < t → m ≤ n → (addPartPrefix dp (k + 1) t).getD m 0 = partAux (k + 1) m) ∧
      (∀ m, t ≤ m → m ≤ n → (addPartPrefix dp (k + 1) t).getD m 0 = partAux k m) := by
  induction t with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · simpa [addPartPrefix_zero] using hlen
    · intro m hm
      exact (Nat.not_lt_zero m hm).elim
    · intro m _ hm
      simpa [addPartPrefix_zero] using hval m hm
  | succ t ih =>
    have ht' : t ≤ n + 1 := Nat.le_trans (Nat.le_succ t) ht
    have ih := ih ht'
    have accDef : addPartPrefix dp (k + 1) (t + 1) =
        step (addPartPrefix dp (k + 1) t) t (k + 1) :=
      addPartPrefix_succ dp (k + 1) t
    refine ⟨?len, ?low, ?high⟩
    · rw [accDef, step_length, ih.1]
    · intro m hm hmn
      rw [accDef]
      have hm' : m ≤ t := Nat.lt_succ_iff.mp hm
      by_cases hmp : t < k + 1
      · unfold step
        rw [if_pos hmp]
        by_cases hmt : m = t
        · rw [hmt, ih.2.2 t (Nat.le_refl t) (hmt ▸ hmn), partAux_succ_of_lt k t hmp]
        · have : m < t := Nat.lt_of_le_of_ne hm' hmt
          exact ih.2.1 m this hmn
      · unfold step
        rw [if_neg hmp]
        by_cases hmt : m = t
        · have htlt : t < (addPartPrefix dp (k + 1) t).length := by
            rw [ih.1]; exact Nat.lt_of_succ_le ht
          rw [hmt, getD_set_eq _ t _ htlt]
          have hold : (addPartPrefix dp (k + 1) t).getD t 0 = partAux k t :=
            ih.2.2 t (Nat.le_refl t) (hmt ▸ hmn)
          have hnew :
              (addPartPrefix dp (k + 1) t).getD (t - (k + 1)) 0 =
                partAux (k + 1) (t - (k + 1)) := by
            have htp : k + 1 ≤ t := Nat.le_of_not_gt hmp
            have hsub : t - (k + 1) < t :=
              Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.succ_pos k) htp) (Nat.succ_pos k)
            have hsubn : t - (k + 1) ≤ n := Nat.le_trans (Nat.le_of_lt hsub) (hmt ▸ hmn)
            exact ih.2.1 (t - (k + 1)) hsub hsubn
          rw [hold, hnew, ← partAux_succ_split k t (Nat.le_of_not_gt hmp)]
        · have hne : t ≠ m := Ne.symm hmt
          rw [getD_set_ne _ t m _ hne]
          have : m < t := Nat.lt_of_le_of_ne hm' hmt
          exact ih.2.1 m this hmn
    · intro m hm hmn
      rw [accDef]
      have hne : t ≠ m := Nat.ne_of_lt (Nat.lt_of_succ_le hm)
      unfold step
      by_cases hmp : t < k + 1
      · rw [if_pos hmp]
        exact ih.2.2 m (Nat.le_trans (Nat.le_succ t) hm) hmn
      · rw [if_neg hmp, getD_set_ne _ t m _ hne]
        exact ih.2.2 m (Nat.le_trans (Nat.le_succ t) hm) hmn

theorem addPart_spec (n k : Nat) (dp : List Nat)
    (hlen : dp.length = n + 1)
    (hval : ∀ m, m ≤ n → dp.getD m 0 = partAux k m) :
    (addPart dp (k + 1)).length = n + 1 ∧
      ∀ m, m ≤ n → (addPart dp (k + 1)).getD m 0 = partAux (k + 1) m := by
  have ht : n + 1 ≤ n + 1 := Nat.le_refl _
  have h := addPartPrefix_spec n k (n + 1) dp hlen hval ht
  have hdef : addPart dp (k + 1) = addPartPrefix dp (k + 1) (n + 1) := by
    simp [addPart, hlen]
  refine ⟨?_, ?_⟩
  · simpa [hdef] using h.1
  · intro m hm
    have : m < n + 1 := Nat.lt_succ_of_le hm
    simpa [hdef] using h.2.1 m this hm

theorem row_spec (n k : Nat) :
    (row n k).length = n + 1 ∧
      ∀ m, m ≤ n → (row n k).getD m 0 = partAux k m := by
  induction k with
  | zero =>
    refine ⟨row0_length n, ?_⟩
    intro m hm
    simpa [row, range_zero] using row0_getD n m hm
  | succ k ih =>
    have hrow : row n (k + 1) = addPart (row n k) (k + 1) := by
      unfold row
      rw [range_succ_eq, List.foldl_append]
      simp [List.foldl]
    rw [hrow]
    exact addPart_spec n k (row n k) ih.1 ih.2

theorem impl_correct : ∀ n, impl n = partitionSpec n := by
  intro n
  simp [impl, partitionSpec]
  exact (row_spec n n).2 n (Nat.le_refl n)

end Submission

