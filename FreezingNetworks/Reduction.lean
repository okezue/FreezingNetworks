import FreezingNetworks.Defs

namespace FreezingNetworks

structure CNF3 where
  n : ℕ
  cls : List (Fin 3 → (Fin n × Bool))

def CNF3.satisfiable (φ : CNF3) : Prop :=
  ∃ α : Fin φ.n → Bool,
    ∀ c ∈ φ.cls, ∃ j : Fin 3,
      (((c j).2 = true ∧ α (c j).1 = true) ∨
       ((c j).2 = false ∧ α (c j).1 = false))

inductive TV (n m : ℕ) where
  | t (i : Fin n) | f (i : Fin n) | c (j : Fin m)
deriving DecidableEq, Fintype

abbrev BoolConfig (V : Type*) := Config V 1

def witnessTerm {n m : ℕ} (i : Fin n) (pos : Bool) :
    ConjGuard (TV n m) 1 :=
  if pos then [.lb (.t i) 1, .ub (.f i) 0]
  else [.lb (.f i) 1, .ub (.t i) 0]

abbrev DNFGuard (V : Type*) (h : ℕ) := List (ConjGuard V h)

structure DNFBoolNet (V : Type*) [Fintype V] [DecidableEq V] where
  guard : V → DNFGuard V 1

def DNFBoolNet.localF {V : Type*} [Fintype V] [DecidableEq V]
    (N : DNFBoolNet V) (v : V) (x : BoolConfig V) : Fin 2 :=
  if (x v) = 0 ∧ (N.guard v).any (fun term =>
    term.all (fun lit => @decide (lit.holds x) (inferInstance)))
  then 1 else x v

theorem DNFBoolNet.localF_freezing {V : Type*} [Fintype V] [DecidableEq V]
    (N : DNFBoolNet V) (v : V) (x : BoolConfig V) :
    x v ≤ N.localF v x := by
  simp only [localF]; split
  · obtain ⟨hv0, _⟩ := ‹_ ∧ _›
    simp [hv0]
  · exact le_refl _

def DNFBoolNet.reachable {V : Type*} [Fintype V] [DecidableEq V]
    (N : DNFBoolNet V) (x y : BoolConfig V) : Prop :=
  asyncReachable N.localF x y

def redNet (φ : CNF3) : DNFBoolNet (TV φ.n φ.cls.length) where
  guard := fun v =>
    match v with
    | .t _ => [[]]
    | .f _ => [[]]
    | .c j =>
      let c := φ.cls.get ⟨j, j.isLt⟩
      (List.finRange 3).map fun l => witnessTerm (c l).1 (c l).2

def allZero (V : Type*) [Fintype V] [DecidableEq V] : BoolConfig V :=
  fun _ => 0

def allOne (V : Type*) [Fintype V] [DecidableEq V] : BoolConfig V :=
  fun _ => 1

private lemma localF_tf {n m : ℕ} (N : DNFBoolNet (TV n m))
    (hg : ∀ i : Fin n, N.guard (.t i) = [[]] ∧ N.guard (.f i) = [[]])
    (x : BoolConfig (TV n m)) (v : TV n m)
    (hv : match v with | .t i => true | .f i => true | .c _ => false)
    (hx0 : x v = 0) :
    N.localF v x = 1 := by
  simp only [DNFBoolNet.localF]
  rw [if_pos]
  constructor
  · exact hx0
  · cases v with
    | t i => simp [(hg i).1]
    | f i => simp [(hg i).2]
    | c _ => simp at hv

private lemma fin2_eq_zero_or_one (x : Fin 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩; interval_cases v <;> simp [Fin.ext_iff]

private lemma fin2_le_zero (x : Fin 2) (h : x ≤ 0) : x = 0 := by
  rcases fin2_eq_zero_or_one x with rfl | rfl <;> simp_all

private lemma fin2_one_le (x : Fin 2) (h : 1 ≤ x) : x = 1 := by
  rcases fin2_eq_zero_or_one x with rfl | rfl <;> simp_all

private lemma wit_all_pos {n m : ℕ} (i : Fin n)
    (x : BoolConfig (TV n m)) (ht : x (.t i) = 1) (hf : x (.f i) = 0) :
    (witnessTerm (m := m) i true).all
      (fun lit => @decide (lit.holds x) (inferInstance)) = true := by
  simp only [witnessTerm, ite_true]
  rw [List.all_cons, List.all_cons, List.all_nil]
  simp only [Bool.and_true, Bool.and_eq_true]
  constructor
  · exact decide_eq_true_eq.mpr (show IntervalLit.holds (.lb (.t i) 1) x from by
      simp [IntervalLit.holds, ht])
  · exact decide_eq_true_eq.mpr (show IntervalLit.holds (.ub (.f i) 0) x from by
      simp [IntervalLit.holds, hf])

private lemma wit_all_neg {n m : ℕ} (i : Fin n)
    (x : BoolConfig (TV n m)) (ht : x (.t i) = 0) (hf : x (.f i) = 1) :
    (witnessTerm (m := m) i false).all
      (fun lit => @decide (lit.holds x) (inferInstance)) = true := by
  simp only [witnessTerm, Bool.false_eq_true, ite_false]
  rw [List.all_cons, List.all_cons, List.all_nil]
  simp only [Bool.and_true, Bool.and_eq_true]
  constructor
  · exact decide_eq_true_eq.mpr (show IntervalLit.holds (.lb (.f i) 1) x from by
      simp [IntervalLit.holds, hf])
  · exact decide_eq_true_eq.mpr (show IntervalLit.holds (.ub (.t i) 0) x from by
      simp [IntervalLit.holds, ht])

private def schedPred (α : Fin n → Bool) (v : TV n m) : Bool :=
  match v with
  | .t i => α i
  | .f i => !α i
  | .c _ => false

theorem sat_implies_reach (φ : CNF3) (hSat : φ.satisfiable) :
    (redNet φ).reachable (allZero _) (allOne _) := by
  obtain ⟨α, hα⟩ := hSat
  let mid : BoolConfig (TV φ.n φ.cls.length) := fun v =>
    match v with
    | .t i => if α i then 1 else 0
    | .f i => if α i then 0 else 1
    | .c _ => 0
  let S₀ : Finset (TV φ.n φ.cls.length) :=
    Finset.univ.filter fun v => schedPred α v
  let S₁ : Finset (TV φ.n φ.cls.length) := Finset.univ
  let orbit : Fin 3 → BoolConfig (TV φ.n φ.cls.length) :=
    fun t => match t with
    | ⟨0, _⟩ => allZero _
    | ⟨1, _⟩ => mid
    | ⟨2, _⟩ => allOne _
  let sched : Fin 2 → Finset (TV φ.n φ.cls.length) :=
    fun t => match t with
    | ⟨0, _⟩ => S₀
    | ⟨1, _⟩ => S₁
  refine ⟨2, orbit, sched, ?_, ?_, ?_⟩
  · ext v; simp [orbit, allZero]
  · ext v; simp [orbit, allOne]
  · intro ⟨t, ht⟩
    interval_cases t
    · ext v
      simp only [orbit, sched, asyncStep]
      cases v with
      | t i =>
        simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and, schedPred]
        cases hα_i : α i
        · simp [hα_i, mid, allZero]
        · simp [hα_i, DNFBoolNet.localF, redNet, allZero, mid]
      | f i =>
        simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and, schedPred]
        cases hα_i : α i
        · simp [hα_i, DNFBoolNet.localF, redNet, allZero, mid]
        · simp [hα_i, mid, allZero]
      | c j =>
        simp only [S₀, Finset.mem_filter, Finset.mem_univ, true_and, schedPred,
          Bool.false_eq_true, ite_false]
        simp [allZero, mid]
    · ext v
      simp only [orbit, sched, asyncStep, S₁, Finset.mem_univ, ite_true]
      cases v with
      | t i =>
        unfold DNFBoolNet.localF
        simp only [mid, redNet, allOne]
        cases α i <;> simp
      | f i =>
        unfold DNFBoolNet.localF
        simp only [mid, redNet, allOne]
        cases α i <;> simp
      | c j =>
        have hcmem : φ.cls.get ⟨j, j.isLt⟩ ∈ φ.cls :=
          List.get_mem φ.cls ⟨j, j.isLt⟩
        obtain ⟨l, hl⟩ := hα _ hcmem
        simp only [DNFBoolNet.localF, allOne]
        rw [if_pos]
        constructor
        · show mid (.c j) = 0; rfl
        · rw [List.any_eq_true]
          set cl := φ.cls.get ⟨j, j.isLt⟩
          refine ⟨witnessTerm (cl l).1 (cl l).2, ?_, ?_⟩
          · show witnessTerm (cl l).1 (cl l).2 ∈ (redNet φ).guard (.c j)
            simp only [redNet]
            exact List.mem_map_of_mem (List.mem_finRange l) (f := fun l => witnessTerm (cl l).1 (cl l).2)
          · cases hl with
            | inl hp =>
              obtain ⟨hpos, hαt⟩ := hp
              rw [hpos]
              exact wit_all_pos (cl l).1 mid
                (show mid (.t (cl l).1) = 1 by simp [mid, hαt])
                (show mid (.f (cl l).1) = 0 by simp [mid, hαt])
            | inr hp =>
              obtain ⟨hpos, hαf⟩ := hp
              rw [hpos]
              exact wit_all_neg (cl l).1 mid
                (show mid (.t (cl l).1) = 0 by simp [mid, hαf])
                (show mid (.f (cl l).1) = 1 by simp [mid, hαf])

noncomputable def activationTime {V : Type*} [DecidableEq V] {T : ℕ}
    (orbit : Fin (T + 1) → BoolConfig V) (v : V) : ℕ :=
  if h : ∃ t : Fin (T + 1), orbit t v = 1 then
    (Finset.univ.filter (fun t : Fin (T + 1) => orbit t v = 1)).min'
      ⟨h.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.choose_spec⟩⟩ |>.val
  else T + 1

private lemma orbit_mono_le {T : ℕ} {V : Type*} [DecidableEq V]
    (orbit : Fin (T + 1) → BoolConfig V)
    (hM : ∀ s : Fin T, ∀ w,
      orbit ⟨s.val, by omega⟩ w ≤ orbit ⟨s.val + 1, by omega⟩ w)
    (v : V) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ T) :
    orbit ⟨i, by omega⟩ v ≤ orbit ⟨j, by omega⟩ v := by
  induction j with
  | zero => simp [Nat.le_zero.mp hij]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact le_refl _
    · exact le_trans (ih (by omega) (by omega))
        (hM ⟨k, by omega⟩ v)

private lemma actTime_le {V : Type*} [DecidableEq V] {T : ℕ}
    (orbit : Fin (T + 1) → BoolConfig V)
    (hM : ∀ s : Fin T, ∀ w,
      orbit ⟨s.val, by omega⟩ w ≤ orbit ⟨s.val + 1, by omega⟩ w)
    (v : V) (t : Fin (T + 1)) (h1 : orbit t v = 1) :
    activationTime orbit v ≤ t.val := by
  unfold activationTime
  have hex : ∃ t' : Fin (T + 1), orbit t' v = 1 := ⟨t, h1⟩
  simp only [dif_pos hex]
  have hmem : t ∈ Finset.univ.filter (fun s : Fin (T + 1) => orbit s v = 1) := by
    simp [Finset.mem_filter, h1]
  exact Fin.val_le_of_le (Finset.min'_le _ t hmem)

private lemma actTime_gt {V : Type*} [DecidableEq V] {T : ℕ}
    (orbit : Fin (T + 1) → BoolConfig V)
    (hM : ∀ s : Fin T, ∀ w,
      orbit ⟨s.val, by omega⟩ w ≤ orbit ⟨s.val + 1, by omega⟩ w)
    (v : V) (t : Fin (T + 1)) (h0 : orbit t v = 0) :
    activationTime orbit v > t.val := by
  unfold activationTime
  split
  · rename_i hex
    set S := Finset.univ.filter (fun s : Fin (T + 1) => orbit s v = 1) with hS_def
    have hne : S.Nonempty :=
      ⟨hex.choose, by simp [hS_def, Finset.mem_filter, hex.choose_spec]⟩
    by_contra hle; push_neg at hle
    have hm_mem := Finset.min'_mem S hne
    have h1 : orbit (S.min' hne) v = 1 := by
      simp [hS_def, Finset.mem_filter] at hm_mem; exact hm_mem
    have hmono := orbit_mono_le orbit hM v hle (Nat.lt_succ_iff.mp t.isLt)
    rw [h1] at hmono
    have ht_eq : (⟨t.val, by omega⟩ : Fin (T + 1)) = t := Fin.ext rfl
    rw [ht_eq] at hmono
    rw [h0] at hmono
    exact absurd hmono (by simp)
  · omega

theorem witness_implies_order {n m T : ℕ}
    (orbit : Fin (T + 1) → BoolConfig (TV n m))
    (hMono : ∀ t : Fin T, ∀ v,
      orbit ⟨t.val, by omega⟩ v ≤ orbit ⟨t.val + 1, by omega⟩ v)
    (t : Fin (T + 1)) (i : Fin n) (pos : Bool)
    (hw : (witnessTerm i pos).holds (orbit t)) :
    if pos then activationTime orbit (TV.t i) < activationTime orbit (TV.f i)
    else activationTime orbit (TV.f i) < activationTime orbit (TV.t i) := by
  unfold ConjGuard.holds at hw
  simp only [witnessTerm] at hw
  cases pos with
  | true =>
    simp only [ite_true, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw ⊢
    have h_lb := hw (.lb (.t i) 1) (Or.inl rfl)
    have h_ub := hw (.ub (.f i) 0) (Or.inr rfl)
    simp only [IntervalLit.holds] at h_lb h_ub
    have hti : orbit t (.t i) = 1 := fin2_one_le _ h_lb
    have hfi : orbit t (.f i) = 0 := fin2_le_zero _ h_ub
    exact lt_of_le_of_lt (actTime_le orbit hMono _ t hti) (actTime_gt orbit hMono _ t hfi)
  | false =>
    have h_lb := hw (.lb (.f i) 1) (by simp [witnessTerm])
    have h_ub := hw (.ub (.t i) 0) (by simp [witnessTerm])
    simp only [IntervalLit.holds] at h_lb h_ub
    have hfi : orbit t (.f i) = 1 := fin2_one_le _ h_lb
    have hti : orbit t (.t i) = 0 := fin2_le_zero _ h_ub
    exact lt_of_le_of_lt (actTime_le orbit hMono _ t hfi) (actTime_gt orbit hMono _ t hti)

theorem reach_implies_sat (φ : CNF3)
    (hReach : (redNet φ).reachable (allZero _) (allOne _)) :
    φ.satisfiable := by
  obtain ⟨T, orbit, sched, hx, hy, hOrbit⟩ := hReach
  have hMono : ∀ t : Fin T, ∀ v,
      orbit ⟨t.val, by omega⟩ v ≤ orbit ⟨t.val + 1, by omega⟩ v := by
    intro t v; rw [hOrbit t]
    exact asyncStep_freeze (DNFBoolNet.localF_freezing _) _ _ v
  refine ⟨fun i =>
    activationTime orbit (.t i) < activationTime orbit (.f i), ?_⟩
  intro c hc
  have hcIdx : ∃ j : Fin φ.cls.length, φ.cls.get ⟨j, j.isLt⟩ = c := by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    exact ⟨⟨j, hj⟩, rfl⟩
  obtain ⟨j, hcj⟩ := hcIdx
  have hT1 : orbit ⟨T, by omega⟩ (.c j) = 1 := by
    have := congr_fun hy (.c j); simp [allOne] at this; exact this
  have h01 : orbit ⟨0, by omega⟩ (.c j) = 0 := by
    have := congr_fun hx (.c j); simp [allZero] at this; exact this
  have hT_pos : 0 < T := by
    by_contra h0; push_neg at h0
    have : T = 0 := by omega
    subst this; rw [h01] at hT1; simp at hT1
  have hstep_all : ∀ t : Fin (T + 1), orbit t (.c j) = 0 ∨
      ∃ s : Fin T, orbit ⟨s.val, by omega⟩ (.c j) = 0 ∧
        orbit ⟨s.val + 1, by omega⟩ (.c j) = 1 := by
    intro ⟨t, ht⟩; induction t with
    | zero => left; exact h01
    | succ k ih =>
      rcases ih (by omega) with hk0 | ⟨s, hs⟩
      · rcases fin2_eq_zero_or_one (orbit ⟨k + 1, ht⟩ (.c j)) with h | h
        · left; exact h
        · right; exact ⟨⟨k, by omega⟩, hk0, h⟩
      · right; exact ⟨s, hs⟩
  have ⟨t0, ht0_zero, ht0_one⟩ : ∃ t0 : Fin T,
      orbit ⟨t0.val, by omega⟩ (.c j) = 0 ∧
      orbit ⟨t0.val + 1, by omega⟩ (.c j) = 1 := by
    rcases hstep_all ⟨T, by omega⟩ with h | ⟨s, hs⟩
    · exact absurd h (by simp [hT1])
    · exact ⟨s, hs⟩
  have hstep := congr_fun (hOrbit t0) (.c j)
  simp only [asyncStep] at hstep
  split_ifs at hstep with hmem
  · rw [ht0_one] at hstep
    simp only [DNFBoolNet.localF] at hstep
    split_ifs at hstep with hcond
    · obtain ⟨_, hany⟩ := hcond
      rw [List.any_eq_true] at hany
      obtain ⟨term, hmem_term, hall⟩ := hany
      simp only [redNet] at hmem_term
      rw [List.mem_map] at hmem_term
      obtain ⟨l, _, rfl⟩ := hmem_term
      subst hcj
      refine ⟨l, ?_⟩
      have hw : (witnessTerm (φ.cls.get ⟨j, j.isLt⟩ l).1
          (φ.cls.get ⟨j, j.isLt⟩ l).2).holds (orbit ⟨t0.val, by omega⟩) := by
        intro lit hlit
        exact decide_eq_true_eq.mp (List.all_eq_true.mp hall lit hlit)
      have hord := witness_implies_order orbit hMono ⟨t0.val, by omega⟩
        (φ.cls.get ⟨j, j.isLt⟩ l).1 (φ.cls.get ⟨j, j.isLt⟩ l).2 hw
      cases hb : (φ.cls.get ⟨j, j.isLt⟩ l).2
      · rw [hb] at hord; simp only [Bool.false_eq_true, ite_false] at hord
        right; exact ⟨rfl, decide_eq_false_iff_not.mpr (by omega)⟩
      · rw [hb] at hord; simp at hord
        left; exact ⟨rfl, decide_eq_true_eq.mpr hord⟩
    · rw [ht0_zero] at hstep; simp at hstep
  · rw [ht0_zero] at hstep; rw [hstep] at ht0_one; simp at ht0_one

theorem reduction_iff (φ : CNF3) :
    φ.satisfiable ↔ (redNet φ).reachable (allZero _) (allOne _) :=
  ⟨sat_implies_reach φ, reach_implies_sat φ⟩

section GuardBounds

theorem redNet_guardSize (φ : CNF3) :
    ∀ v : TV φ.n φ.cls.length,
      ((redNet φ).guard v).length ≤ 3 := by
  intro v; cases v with
  | t _ => simp [redNet]
  | f _ => simp [redNet]
  | c j => simp [redNet, List.finRange]

theorem redNet_termWidth (φ : CNF3) :
    ∀ v : TV φ.n φ.cls.length,
      ∀ term ∈ (redNet φ).guard v, term.length ≤ 2 := by
  intro v term hmem
  cases v with
  | t _ => simp [redNet] at hmem; subst hmem; simp
  | f _ => simp [redNet] at hmem; subst hmem; simp
  | c j =>
    simp [redNet] at hmem
    obtain ⟨l, rfl⟩ := hmem
    simp [witnessTerm]; split <;> simp

end GuardBounds

end FreezingNetworks
