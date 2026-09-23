import Spec

namespace Submission

def rowSupport (dimension seed i : Nat) : List Nat :=
  if dimension < 3 then
    List.range dimension
  else
    [i,
      permanentColumnOne dimension seed i,
      permanentColumnTwo dimension seed i]

def permWalk (width : Nat) : List (List Nat) → Nat → Nat
  | [], _ => 1
  | cols :: rows, used =>
      cols.foldl
        (fun total j =>
          if used.testBit j then
            total
          else
            total + permWalk width rows (used ||| (1 <<< j)))
        0

def supports (dimension seed : Nat) : List (List Nat) :=
  (List.range dimension).map (rowSupport dimension seed)

def impl (n : Nat) : Nat :=
  permWalk (permanentDimension n)
    (supports (permanentDimension n) (permanentSeed n)) 0

/-! ### skip maps -/

theorem skipOne_ne (excluded k : Nat) :
    permanentSkipOne excluded k ≠ excluded := by
  unfold permanentSkipOne
  split
  · next h => exact Nat.ne_of_lt h
  · next h => exact Nat.ne_of_gt (Nat.lt_succ_of_le (Nat.le_of_not_gt h))

theorem skipOne_lt {n excluded k : Nat}
    (hn : 0 < n) (hk : k < n - 1) :
    permanentSkipOne excluded k < n := by
  have h1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have hkn : k + 1 < n := by
    have hs : k + 1 < (n - 1) + 1 := Nat.succ_lt_succ hk
    simpa [Nat.sub_add_cancel h1] using hs
  have hk' : k < n := Nat.lt_of_lt_of_le hk (Nat.sub_le n 1)
  unfold permanentSkipOne
  split
  · exact hk'
  · exact hkn

theorem skipTwo_of_le (a b k : Nat) (h : a ≤ b) :
    permanentSkipTwo a b k =
      (if k < a then k else if k + 1 < b then k + 1 else k + 2) := by
  unfold permanentSkipTwo
  rw [Nat.min_eq_left h, Nat.max_eq_right h]
  dsimp
  by_cases hk : k < a
  · simp [hk, Nat.lt_of_lt_of_le hk h]
  · simp [hk]

theorem skipTwo_of_ge (a b k : Nat) (h : b ≤ a) :
    permanentSkipTwo a b k =
      (if k < b then k else if k + 1 < a then k + 1 else k + 2) := by
  unfold permanentSkipTwo
  rw [Nat.min_eq_right h, Nat.max_eq_left h]
  dsimp
  by_cases hk : k < b
  · simp [hk, Nat.lt_of_lt_of_le hk h]
  · simp [hk]

theorem skipTwo_ne_left {a b k : Nat} :
    permanentSkipTwo a b k ≠ a := by
  by_cases hle : a ≤ b
  · rw [skipTwo_of_le _ _ _ hle]
    by_cases hk : k < a
    · simp [hk]; exact Nat.ne_of_lt hk
    · simp [hk]
      by_cases hx : k + 1 < b
      · simp [hx]; exact Nat.ne_of_gt (Nat.lt_succ_of_le (Nat.le_of_not_gt hk))
      · simp [hx]; exact Nat.ne_of_gt (Nat.lt_succ_of_lt (Nat.lt_succ_of_le (Nat.le_of_not_gt hk)))
  · have hge : b ≤ a := Nat.le_of_not_ge hle
    rw [skipTwo_of_ge _ _ _ hge]
    by_cases hk : k < b
    · simp [hk]; exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hk hge)
    · simp [hk]
      by_cases hx : k + 1 < a
      · simp [hx]; exact Nat.ne_of_lt hx
      · simp [hx]; exact Nat.ne_of_gt (Nat.lt_succ_of_le (Nat.le_of_not_gt hx))

theorem skipTwo_ne_right {a b k : Nat} :
    permanentSkipTwo a b k ≠ b := by
  by_cases hle : a ≤ b
  · rw [skipTwo_of_le _ _ _ hle]
    by_cases hk : k < a
    · simp [hk]; exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hk hle)
    · simp [hk]
      by_cases hx : k + 1 < b
      · simp [hx]; exact Nat.ne_of_lt hx
      · simp [hx]; exact Nat.ne_of_gt (Nat.lt_succ_of_le (Nat.le_of_not_gt hx))
  · have hge : b ≤ a := Nat.le_of_not_ge hle
    rw [skipTwo_of_ge _ _ _ hge]
    by_cases hk : k < b
    · simp [hk]; exact Nat.ne_of_lt hk
    · simp [hk]
      by_cases hx : k + 1 < a
      · simp [hx]; exact Nat.ne_of_gt (Nat.lt_succ_of_le (Nat.le_of_not_gt hk))
      · simp [hx]; exact Nat.ne_of_gt (Nat.lt_succ_of_lt (Nat.lt_succ_of_le (Nat.le_of_not_gt hk)))

theorem add2_lt_of_lt_sub2 {n k : Nat} (hn : 2 ≤ n) (hk : k < n - 2) :
    k + 2 < n := by
  have hs : k + 2 < (n - 2) + 2 := Nat.add_lt_add_right hk 2
  simpa [Nat.sub_add_cancel hn] using hs

theorem skipTwo_lt {n a b k : Nat} (hn : 2 ≤ n) (hk : k < n - 2) :
    permanentSkipTwo a b k < n := by
  have hk2 := add2_lt_of_lt_sub2 hn hk
  have hk1 : k + 1 < n := Nat.lt_trans (Nat.lt_succ_self _) hk2
  have hk0 : k < n := Nat.lt_trans (Nat.lt_succ_self _) hk1
  by_cases hle : a ≤ b
  · rw [skipTwo_of_le _ _ _ hle]
    by_cases hk' : k < a
    · simp [hk']; exact hk0
    · simp [hk']
      by_cases hx : k + 1 < b
      · simp [hx]; exact hk1
      · simp [hx]; exact hk2
  · have hge : b ≤ a := Nat.le_of_not_ge hle
    rw [skipTwo_of_ge _ _ _ hge]
    by_cases hk' : k < b
    · simp [hk']; exact hk0
    · simp [hk']
      by_cases hx : k + 1 < a
      · simp [hx]; exact hk1
      · simp [hx]; exact hk2

/-! ### column bounds -/

theorem dim_pos {d : Nat} (hd : 3 ≤ d) : 0 < d :=
  Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 3) hd

theorem dim_ge2 {d : Nat} (hd : 3 ≤ d) : 2 ≤ d :=
  Nat.le_trans (by decide : (2 : Nat) ≤ 3) hd

theorem dim_sub1_pos {d : Nat} (hd : 3 ≤ d) : 0 < d - 1 :=
  Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : (1 : Nat) < 3) hd)

theorem dim_sub2_pos {d : Nat} (hd : 3 ≤ d) : 0 < d - 2 :=
  Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : (2 : Nat) < 3) hd)

theorem col1_lt {d seed i : Nat} (hd : 3 ≤ d) :
    permanentColumnOne d seed i < d := by
  unfold permanentColumnOne
  exact skipOne_lt (dim_pos hd) (Nat.mod_lt _ (dim_sub1_pos hd))

theorem col1_ne_diag (d seed i : Nat) :
    permanentColumnOne d seed i ≠ i :=
  skipOne_ne _ _

theorem col2_lt {d seed i : Nat} (hd : 3 ≤ d) :
    permanentColumnTwo d seed i < d := by
  unfold permanentColumnTwo
  exact skipTwo_lt (dim_ge2 hd) (Nat.mod_lt _ (dim_sub2_pos hd))

theorem col2_ne_diag (d seed i : Nat) :
    permanentColumnTwo d seed i ≠ i := by
  unfold permanentColumnTwo
  exact skipTwo_ne_left

theorem col2_ne_col1 (d seed i : Nat) :
    permanentColumnTwo d seed i ≠ permanentColumnOne d seed i := by
  unfold permanentColumnTwo
  exact skipTwo_ne_right

/-! ### entries -/

theorem entry_of_lt3 {d seed i j : Nat} (h : d < 3) :
    permanentEntry d seed i j = 1 := by
  simp [permanentEntry, h]

theorem getD_map_range (d j : Nat) (f : Nat → Nat) :
    ((List.range d).map f).getD j 0 = if j < d then f j else 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hj : j < d
  · have hlen : j < ((List.range d).map f).length := by
      simpa [List.length_map, List.length_range]
    rw [List.getElem?_eq_getElem hlen, Option.getD_some, List.getElem_map, List.getElem_range]
    simp [hj]
  · have hle : ((List.range d).map f).length ≤ j := by
      simpa [List.length_map, List.length_range] using Nat.le_of_not_gt hj
    rw [List.getElem?_eq_none hle, Option.getD_none]
    simp [hj]

theorem genRow_getD (d seed i j : Nat) :
    (genPermanentRow d seed i).getD j 0 =
      if j < d then permanentEntry d seed i j else 0 :=
  getD_map_range d j (permanentEntry d seed i)

theorem entry_ge3_eq (d seed i j : Nat) (hd : 3 ≤ d) :
    permanentEntry d seed i j =
      if j = i || j = permanentColumnOne d seed i ||
          j = permanentColumnTwo d seed i then 1 else 0 := by
  unfold permanentEntry
  have hdim : ¬ d < 3 := Nat.not_lt.mpr hd
  simp [hdim]
  by_cases hij : i = j
  · simp [hij]
  · by_cases h1 : j = permanentColumnOne d seed i
    · simp [hij, h1]
    · by_cases h2 : j = permanentColumnTwo d seed i
      · simp [hij, h1, h2]
      · simp [hij, h1, h2, Ne.symm hij]

/-! ### sparse sums -/

def lsum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => lsum n f + f n

theorem foldl_add_eq_lsum (f : Nat → Nat) :
    ∀ w acc, (List.range w).foldl (fun t j => t + f j) acc = acc + lsum w f
  | 0, acc => by simp [lsum]
  | w + 1, acc => by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [foldl_add_eq_lsum f w acc]
      simp [lsum, Nat.add_assoc]

theorem foldl_range_congr (w : Nat) (f g : Nat → Nat → Nat)
    (h : ∀ acc j, j < w → f acc j = g acc j) (acc : Nat) :
    (List.range w).foldl f acc = (List.range w).foldl g acc := by
  induction w generalizing acc with
  | zero => rfl
  | succ w ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_append,
          List.foldl_cons, List.foldl_cons, List.foldl_nil, List.foldl_nil]
      rw [ih (fun acc j hj => h acc j (Nat.lt_succ_of_lt hj)) acc]
      exact h _ w (Nat.lt_succ_self _)

theorem lsum_eq {w : Nat} {f g : Nat → Nat} (h : ∀ j, j < w → f j = g j) :
    lsum w f = lsum w g := by
  induction w with
  | zero => rfl
  | succ w ih =>
      simp [lsum, h w (Nat.lt_succ_self _), ih fun j hj => h j (Nat.lt_succ_of_lt hj)]

theorem lsum_zero {w : Nat} {f : Nat → Nat} (h : ∀ j, j < w → f j = 0) :
    lsum w f = 0 := by
  induction w with
  | zero => rfl
  | succ w ih =>
      simp [lsum, h w (Nat.lt_succ_self _), ih fun j hj => h j (Nat.lt_succ_of_lt hj)]

theorem lsum_single {w a : Nat} (ha : a < w) (v : Nat) :
    lsum w (fun j => if j = a then v else 0) = v := by
  induction w with
  | zero => exact absurd ha (Nat.not_lt_zero _)
  | succ w ih =>
      simp [lsum]
      by_cases hw : w = a
      · subst w
        have hz : lsum a (fun j => if j = a then v else 0) = 0 :=
          lsum_zero (fun j hj => by simp [Nat.ne_of_lt hj])
        simp [hz]
      · have ha' : a < w :=
          Nat.lt_of_le_of_ne (Nat.le_of_lt_succ ha) (Ne.symm hw)
        simp [hw, ih ha']

theorem lsum_add (w : Nat) (f g : Nat → Nat) :
    lsum w (fun j => f j + g j) = lsum w f + lsum w g := by
  induction w with
  | zero => rfl
  | succ w ih =>
      simp [lsum, ih]
      omega

theorem lsum_three {w a b c : Nat} (ha : a < w) (hb : b < w) (hc : c < w)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (fa fb fc : Nat) :
    lsum w (fun j =>
        if j = a then fa else if j = b then fb else if j = c then fc else 0) =
      fa + fb + fc := by
  let f := fun j =>
    (if j = a then fa else 0) + (if j = b then fb else 0) + (if j = c then fc else 0)
  have hfg : ∀ j, j < w →
      (if j = a then fa else if j = b then fb else if j = c then fc else 0) = f j := by
    intro j _
    by_cases ja : j = a
    · subst ja; simp [f, hab, hac]
    · by_cases jb : j = b
      · subst jb; simp [f, ja, Ne.symm hab, hbc]
      · by_cases jc : j = c
        · subst jc; simp [f, ja, jb]
        · simp [f, ja, jb, jc]
  rw [lsum_eq hfg]
  change lsum w (fun j =>
      ((if j = a then fa else 0) + (if j = b then fb else 0)) + (if j = c then fc else 0)) = _
  rw [lsum_add, lsum_add, lsum_single ha, lsum_single hb, lsum_single hc]

theorem foldl_three (a b c : Nat) (P : Nat → Bool) (g : Nat → Nat) :
    [a, b, c].foldl (fun t j => if P j then t else t + g j) 0 =
      (if P a then 0 else g a) + (if P b then 0 else g b) + (if P c then 0 else g c) := by
  simp [List.foldl_cons, List.foldl_nil]
  cases hP : P a <;> cases hQ : P b <;> cases hR : P c <;> simp

/-! ### one-row agreement -/

def spike (used : Nat) (rec : Nat → Nat) (j : Nat) : Nat :=
  if used.testBit j then 0 else rec (used ||| (1 <<< j))

theorem one_row_lt3 (d seed i used : Nat) (rec : Nat → Nat) (hd : d < 3) :
    (rowSupport d seed i).foldl
        (fun t j => if used.testBit j then t else t + rec (used ||| (1 <<< j))) 0 =
      (List.range d).foldl
        (fun t j =>
          let e := (genPermanentRow d seed i).getD j 0
          if e = 0 || used.testBit j then t
          else t + e * rec (used ||| (1 <<< j))) 0 := by
  have hs : rowSupport d seed i = List.range d := by simp [rowSupport, hd]
  rw [hs]
  refine foldl_range_congr d
    (fun t j => if used.testBit j then t else t + rec (used ||| (1 <<< j)))
    (fun t j =>
      let e := (genPermanentRow d seed i).getD j 0
      if e = 0 || used.testBit j then t
      else t + e * rec (used ||| (1 <<< j)))
    ?_ 0
  intro acc j hj
  have he : (genPermanentRow d seed i).getD j 0 = 1 := by
    rw [genRow_getD, if_pos hj, entry_of_lt3 hd]
  rw [List.getD_eq_getElem?_getD] at he ⊢
  simp [he]

theorem spec_fold_as_lsum (d seed i used : Nat) (rec : Nat → Nat) :
    (List.range d).foldl
      (fun t j =>
        let e := (genPermanentRow d seed i).getD j 0
        if e = 0 || used.testBit j then t
        else t + e * rec (used ||| (1 <<< j))) 0 =
      lsum d (fun j =>
        let e := (genPermanentRow d seed i).getD j 0
        if e = 0 || used.testBit j then 0
        else e * rec (used ||| (1 <<< j))) := by
  have hstep :
      (List.range d).foldl
        (fun t j =>
          let e := (genPermanentRow d seed i).getD j 0
          if e = 0 || used.testBit j then t
          else t + e * rec (used ||| (1 <<< j))) 0 =
      (List.range d).foldl
        (fun t j =>
          t +
            (let e := (genPermanentRow d seed i).getD j 0
             if e = 0 || used.testBit j then 0
             else e * rec (used ||| (1 <<< j)))) 0 := by
    refine foldl_range_congr d _ _ ?_ 0
    intro acc j hj
    rw [List.getD_eq_getElem?_getD]
    by_cases he : (genPermanentRow d seed i)[j]?.getD 0 = 0
    · simp [he]
    · by_cases hu : used.testBit j = true
      · simp [he, hu]
      · simp [he, hu]
  rw [hstep, foldl_add_eq_lsum]
  simp

theorem one_row_ge3 (d seed i used : Nat) (rec : Nat → Nat)
    (hd : 3 ≤ d) (hi : i < d) :
    (rowSupport d seed i).foldl
        (fun t j => if used.testBit j then t else t + rec (used ||| (1 <<< j))) 0 =
      (List.range d).foldl
        (fun t j =>
          let e := (genPermanentRow d seed i).getD j 0
          if e = 0 || used.testBit j then t
          else t + e * rec (used ||| (1 <<< j))) 0 := by
  have hs : rowSupport d seed i =
      [i, permanentColumnOne d seed i, permanentColumnTwo d seed i] := by
    simp [rowSupport, Nat.not_lt.mpr hd]
  rw [hs, foldl_three, spec_fold_as_lsum]
  have hb : permanentColumnOne d seed i < d := col1_lt hd
  have hc : permanentColumnTwo d seed i < d := col2_lt hd
  have hab : i ≠ permanentColumnOne d seed i := (col1_ne_diag d seed i).symm
  have hac : i ≠ permanentColumnTwo d seed i := (col2_ne_diag d seed i).symm
  have hbc : permanentColumnOne d seed i ≠ permanentColumnTwo d seed i :=
    (col2_ne_col1 d seed i).symm
  have hpt : ∀ j, j < d →
      (let e := (genPermanentRow d seed i).getD j 0
       if e = 0 || used.testBit j then 0
       else e * rec (used ||| (1 <<< j))) =
        (if j = i then spike used rec i
         else if j = permanentColumnOne d seed i then
           spike used rec (permanentColumnOne d seed i)
         else if j = permanentColumnTwo d seed i then
           spike used rec (permanentColumnTwo d seed i)
         else 0) := by
    intro j hj
    rw [genRow_getD, if_pos hj, entry_ge3_eq d seed i j hd]
    by_cases ja : j = i
    · subst ja; simp [spike]
    · by_cases jb : j = permanentColumnOne d seed i
      · subst jb; simp [ja, spike]
      · by_cases jc : j = permanentColumnTwo d seed i
        · subst jc; simp [ja, jb, spike]
        · simp [ja, jb, jc]
  rw [lsum_eq hpt, lsum_three hi hb hc hab hac hbc]
  simp [spike]

theorem one_row (d seed i used : Nat) (rec : Nat → Nat) (hi : i < d) :
    (rowSupport d seed i).foldl
        (fun t j => if used.testBit j then t else t + rec (used ||| (1 <<< j))) 0 =
      (List.range d).foldl
        (fun t j =>
          let e := (genPermanentRow d seed i).getD j 0
          if e = 0 || used.testBit j then t
          else t + e * rec (used ||| (1 <<< j))) 0 := by
  by_cases hd : d < 3
  · exact one_row_lt3 d seed i used rec hd
  · exact one_row_ge3 d seed i used rec (Nat.le_of_not_gt hd) hi

/-! ### row-list agreement -/

theorem walk_eq_rows (d seed : Nat) :
    ∀ (ids : List Nat) used,
      (∀ i ∈ ids, i < d) →
      permWalk d (ids.map (rowSupport d seed)) used =
        permanentRows d (ids.map (genPermanentRow d seed)) used
  | [], used, _ => by simp [permWalk, permanentRows]
  | i :: ids, used, hids => by
      have hi : i < d := hids i List.mem_cons_self
      have htail : ∀ j ∈ ids, j < d := fun j hj =>
        hids j (List.mem_cons_of_mem i hj)
      simp [permWalk, permanentRows]
      have ih := walk_eq_rows d seed ids
      refine (one_row d seed i used
        (fun mask => permWalk d (ids.map (rowSupport d seed)) mask) hi).trans ?_
      refine foldl_range_congr d _ _ ?_ 0
      intro acc j hj
      rw [List.getD_eq_getElem?_getD]
      by_cases he : (genPermanentRow d seed i)[j]?.getD 0 = 0
      · simp [he]
      · by_cases hu : used.testBit j = true
        · simp [he, hu]
        · simp [he, hu]
          rw [ih (used ||| (1 <<< j)) htail]

theorem impl_correct : ∀ n, impl n = permanentSpecN n := by
  intro n
  simp [impl, permanentSpecN, permanentSpec, supports, genPermanentMatrix]
  exact walk_eq_rows (permanentDimension n) (permanentSeed n)
    (List.range (permanentDimension n)) 0 (by
      intro i hi
      exact (List.mem_range.mp hi))

end Submission
