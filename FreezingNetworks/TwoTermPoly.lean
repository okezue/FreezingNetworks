import FreezingNetworks.Defs
import FreezingNetworks.BellmanFord
import FreezingNetworks.MainTheorem
import FreezingNetworks.Reduction
import FreezingNetworks.FPT

namespace FreezingNetworks

variable {V : Type*} [Fintype V] [DecidableEq V]

section TwoTermNPHard

variable {h : ℕ}

def isTwoTermDNF (N : DisjUIFN V h) : Prop :=
  ∀ v (k : Fin h), (N.guard v k).length ≤ 2

inductive TV2 (n m : ℕ) where
  | t (i : Fin n)
  | f (i : Fin n)
  | z (j : Fin m)
  | w (j : Fin m)
  | c (j : Fin m)
deriving DecidableEq, Fintype

abbrev BoolConfig2 (V : Type*) := Config V 1

def witnessTerm2 {n m : ℕ} (i : Fin n) (pos : Bool) :
    ConjGuard (TV2 n m) 1 :=
  if pos then [.lb (.t i) 1, .ub (.f i) 0]
  else [.lb (.f i) 1, .ub (.t i) 0]

def redNet2 (φ : CNF3) : DNFBoolNet (TV2 φ.n φ.cls.length) where
  guard := fun v =>
    match v with
    | .t _ => [[]]
    | .f _ => [[]]
    | .z j =>
      let cl := φ.cls.get ⟨j, j.isLt⟩
      [witnessTerm2 (cl 0).1 (cl 0).2, [.lb (.c j) 1]]
    | .w j =>
      let cl := φ.cls.get ⟨j, j.isLt⟩
      [witnessTerm2 (cl 1).1 (cl 1).2, [.lb (.z j) 1]]
    | .c j =>
      let cl := φ.cls.get ⟨j, j.isLt⟩
      [[.lb (.w j) 1], witnessTerm2 (cl 2).1 (cl 2).2]

theorem redNet2_two_term (φ : CNF3) :
    ∀ v : TV2 φ.n φ.cls.length,
      ((redNet2 φ).guard v).length ≤ 2 := by
  intro v; cases v with
  | t _ => simp [redNet2]
  | f _ => simp [redNet2]
  | z _ => simp [redNet2]
  | w _ => simp [redNet2]
  | c _ => simp [redNet2]

theorem redNet2_term_width (φ : CNF3) :
    ∀ v : TV2 φ.n φ.cls.length,
      ∀ term ∈ (redNet2 φ).guard v, term.length ≤ 2 := by
  intro v term hmem
  cases v with
  | t _ => simp [redNet2] at hmem; subst hmem; simp
  | f _ => simp [redNet2] at hmem; subst hmem; simp
  | z j =>
    simp [redNet2] at hmem
    rcases hmem with rfl | rfl
    · simp [witnessTerm2]; split <;> simp
    · simp
  | w j =>
    simp [redNet2] at hmem
    rcases hmem with rfl | rfl
    · simp [witnessTerm2]; split <;> simp
    · simp
  | c j =>
    simp [redNet2] at hmem
    rcases hmem with rfl | rfl
    · simp
    · simp [witnessTerm2]; split <;> simp

private lemma fin2_eq_zero_or_one' (x : Fin 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩; interval_cases v <;> simp [Fin.ext_iff]

private lemma fin2_le_zero' (x : Fin 2) (hx : x ≤ 0) : x = 0 := by
  rcases fin2_eq_zero_or_one' x with rfl | rfl <;> simp_all

private lemma fin2_one_le' (x : Fin 2) (hx : 1 ≤ x) : x = 1 := by
  rcases fin2_eq_zero_or_one' x with rfl | rfl <;> simp_all

private lemma wit2_all_pos {n m : ℕ} (i : Fin n)
    (x : BoolConfig (TV2 n m)) (ht : x (.t i) = 1) (hf : x (.f i) = 0) :
    (witnessTerm2 (m := m) i true).all
      (fun lit => @decide (lit.holds x) (inferInstance)) = true := by
  simp only [witnessTerm2, ite_true, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨decide_eq_true_eq.mpr (by simp [IntervalLit.holds, ht]),
         decide_eq_true_eq.mpr (by simp [IntervalLit.holds, hf])⟩

private lemma wit2_all_neg {n m : ℕ} (i : Fin n)
    (x : BoolConfig (TV2 n m)) (ht : x (.t i) = 0) (hf : x (.f i) = 1) :
    (witnessTerm2 (m := m) i false).all
      (fun lit => @decide (lit.holds x) (inferInstance)) = true := by
  simp only [witnessTerm2, Bool.false_eq_true, ite_false, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true]
  exact ⟨decide_eq_true_eq.mpr (by simp [IntervalLit.holds, hf]),
         decide_eq_true_eq.mpr (by simp [IntervalLit.holds, ht])⟩

private lemma orbit_mono_le' {T n m : ℕ}
    (orbit : Fin (T + 1) → BoolConfig (TV2 n m))
    (hM : ∀ s : Fin T, ∀ w,
      orbit ⟨s.val, by omega⟩ w ≤ orbit ⟨s.val + 1, by omega⟩ w)
    (v : TV2 n m) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ T) :
    orbit ⟨i, by omega⟩ v ≤ orbit ⟨j, by omega⟩ v := by
  induction j with
  | zero => simp [Nat.le_zero.mp hij]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact le_refl _
    · exact le_trans (ih (by omega) (by omega)) (hM ⟨k, by omega⟩ v)

private lemma actTime_le' {n m T : ℕ}
    (orbit : Fin (T + 1) → BoolConfig (TV2 n m))
    (hM : ∀ s : Fin T, ∀ w,
      orbit ⟨s.val, by omega⟩ w ≤ orbit ⟨s.val + 1, by omega⟩ w)
    (v : TV2 n m) (t : Fin (T + 1)) (h1 : orbit t v = 1) :
    activationTime orbit v ≤ t.val := by
  unfold activationTime; rw [dif_pos ⟨t, h1⟩]
  exact Fin.val_le_of_le (Finset.min'_le _ t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩))

private lemma actTime_gt' {n m T : ℕ}
    (orbit : Fin (T + 1) → BoolConfig (TV2 n m))
    (hM : ∀ s : Fin T, ∀ w,
      orbit ⟨s.val, by omega⟩ w ≤ orbit ⟨s.val + 1, by omega⟩ w)
    (v : TV2 n m) (t : Fin (T + 1)) (h0 : orbit t v = 0) :
    activationTime orbit v > t.val := by
  unfold activationTime; split
  · rename_i hex
    by_contra hle; push_neg at hle
    set S := Finset.univ.filter (fun s : Fin (T + 1) => orbit s v = 1)
    have hne : S.Nonempty :=
      ⟨hex.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hex.choose_spec⟩⟩
    have h1 := (Finset.mem_filter.mp (Finset.min'_mem S hne)).2
    have hmono := orbit_mono_le' orbit hM v hle (Nat.lt_succ_iff.mp t.isLt)
    rw [h1, show (⟨t.val, by omega⟩ : Fin (T + 1)) = t from Fin.ext rfl, h0] at hmono
    exact absurd hmono (by simp)
  · omega

private theorem witness_implies_order2 {n m T : ℕ}
    (orbit : Fin (T + 1) → BoolConfig (TV2 n m))
    (hMono : ∀ t : Fin T, ∀ v,
      orbit ⟨t.val, by omega⟩ v ≤ orbit ⟨t.val + 1, by omega⟩ v)
    (t : Fin (T + 1)) (i : Fin n) (pos : Bool)
    (hw : (witnessTerm2 i pos).holds (orbit t)) :
    if pos then activationTime orbit (TV2.t i) < activationTime orbit (TV2.f i)
    else activationTime orbit (TV2.f i) < activationTime orbit (TV2.t i) := by
  unfold ConjGuard.holds at hw; simp only [witnessTerm2] at hw
  cases pos with
  | true =>
    simp only [ite_true, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw ⊢
    have h_lb := hw (.lb (.t i) 1) (Or.inl rfl)
    have h_ub := hw (.ub (.f i) 0) (Or.inr rfl)
    simp only [IntervalLit.holds] at h_lb h_ub
    exact lt_of_le_of_lt (actTime_le' orbit hMono _ t (fin2_one_le' _ h_lb))
      (actTime_gt' orbit hMono _ t (fin2_le_zero' _ h_ub))
  | false =>
    have h_lb := hw (.lb (.f i) 1) (by simp [witnessTerm2])
    have h_ub := hw (.ub (.t i) 0) (by simp [witnessTerm2])
    simp only [IntervalLit.holds] at h_lb h_ub
    exact lt_of_le_of_lt (actTime_le' orbit hMono _ t (fin2_one_le' _ h_lb))
      (actTime_gt' orbit hMono _ t (fin2_le_zero' _ h_ub))

private lemma fire_wit {n m : ℕ} (i : Fin n) (pos : Bool) (α : Fin n → Bool)
    (x : BoolConfig (TV2 n m))
    (hsat : (pos = true ∧ α i = true) ∨ (pos = false ∧ α i = false))
    (hxt : x (.t i) = if α i then 1 else 0)
    (hxf : x (.f i) = if α i then 0 else 1) :
    (witnessTerm2 (m := m) i pos).all
      (fun lit => @decide (lit.holds x) (inferInstance)) = true := by
  rcases hsat with ⟨hp, ha⟩ | ⟨hp, ha⟩
  · rw [hp]; exact wit2_all_pos i x (by simp [hxt, ha]) (by simp [hxf, ha])
  · rw [hp]; exact wit2_all_neg i x (by simp [hxt, ha]) (by simp [hxf, ha])

private lemma lb_all2 {n m : ℕ} (v : TV2 n m)
    (x : BoolConfig (TV2 n m)) (hv : x v = 1) :
    ([.lb v 1] : ConjGuard (TV2 n m) 1).all
      (fun lit => @decide (lit.holds x) (inferInstance)) = true := by
  simp [List.all_cons, List.all_nil, decide_eq_true_eq, IntervalLit.holds, hv]

set_option maxHeartbeats 12800000 in
theorem sat_implies_reach2 (φ : CNF3)
    (hSat : φ.satisfiable) :
    (redNet2 φ).reachable (fun _ => 0) (fun _ => 1) := by
  obtain ⟨α, hα⟩ := hSat
  let gcl (j : Fin φ.cls.length) := φ.cls.get ⟨j, j.isLt⟩
  have hgm : ∀ j, gcl j ∈ φ.cls := fun j => List.get_mem φ.cls ⟨j, j.isLt⟩
  let lj (j : Fin φ.cls.length) : Fin 3 := (hα (gcl j) (hgm j)).choose
  have hlj : ∀ j, (((gcl j) (lj j)).2 = true ∧ α ((gcl j) (lj j)).1 = true) ∨
      (((gcl j) (lj j)).2 = false ∧ α ((gcl j) (lj j)).1 = false) :=
    fun j => (hα (gcl j) (hgm j)).choose_spec
  let x1 : BoolConfig (TV2 φ.n φ.cls.length) := fun v =>
    match v with
    | .t i => if α i then 1 else 0 | .f i => if α i then 0 else 1 | _ => 0
  let x2 : BoolConfig (TV2 φ.n φ.cls.length) := fun v =>
    match v with
    | .t i => if α i then 1 else 0 | .f i => if α i then 0 else 1
    | .z j => if lj j = 0 then 1 else 0 | .w j => if lj j = 1 then 1 else 0
    | .c j => if lj j = 2 then 1 else 0
  let x3 : BoolConfig (TV2 φ.n φ.cls.length) := fun v =>
    match v with
    | .t i => if α i then 1 else 0 | .f i => if α i then 0 else 1
    | .z j => if lj j = 0 ∨ lj j = 2 then 1 else 0
    | .w j => if lj j = 1 ∨ lj j = 0 then 1 else 0
    | .c j => if lj j = 2 ∨ lj j = 1 then 1 else 0
  have hwit : ∀ j, (witnessTerm2 ((gcl j) (lj j)).1 ((gcl j) (lj j)).2).all
      (fun lit => @decide (lit.holds x1) (inferInstance)) = true := by
    intro j; exact fire_wit _ _ α x1 (hlj j) rfl rfl
  have hfin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by
    intro ⟨v, hv⟩; interval_cases v <;> simp [Fin.ext_iff]
  let orbit : Fin 5 → BoolConfig (TV2 φ.n φ.cls.length) := fun t =>
    if t.val = 0 then fun _ => 0
    else if t.val = 1 then x1
    else if t.val = 2 then x2
    else if t.val = 3 then x3
    else fun _ => 1
  let sp0 : TV2 φ.n φ.cls.length → Bool := fun v =>
    match v with | .t i => α i | .f i => !α i | _ => false
  let sp1 : TV2 φ.n φ.cls.length → Bool := fun v =>
    match v with | .z j => lj j == 0 | .w j => lj j == 1 | .c j => lj j == 2 | _ => false
  let sp2 : TV2 φ.n φ.cls.length → Bool := fun v =>
    match v with | .z j => lj j == 2 | .w j => lj j == 0 | .c j => lj j == 1 | _ => false
  let sched : Fin 4 → Finset (TV2 φ.n φ.cls.length) := fun t =>
    if t.val = 0 then Finset.univ.filter (fun v => sp0 v = true)
    else if t.val = 1 then Finset.univ.filter (fun v => sp1 v = true)
    else if t.val = 2 then Finset.univ.filter (fun v => sp2 v = true)
    else Finset.univ
  have horb0 : orbit ⟨0, by omega⟩ = fun _ => 0 := by simp [orbit]
  have horb4 : orbit ⟨4, by omega⟩ = fun _ => 1 := by simp [orbit]
  have horb1 : orbit ⟨1, by omega⟩ = x1 := by simp [orbit]
  have horb2 : orbit ⟨2, by omega⟩ = x2 := by simp [orbit]
  have horb3 : orbit ⟨3, by omega⟩ = x3 := by simp [orbit]
  have hsched0 : sched ⟨0, by omega⟩ = Finset.univ.filter (fun v => sp0 v = true) := by simp [sched]
  have hsched1 : sched ⟨1, by omega⟩ = Finset.univ.filter (fun v => sp1 v = true) := by simp [sched]
  have hsched2 : sched ⟨2, by omega⟩ = Finset.univ.filter (fun v => sp2 v = true) := by simp [sched]
  have hsched3 : sched ⟨3, by omega⟩ = Finset.univ := by simp [sched]
  refine ⟨4, orbit, sched, ?_, ?_, ?_⟩
  · exact horb0
  · exact horb4
  · intro ⟨t, ht⟩
    interval_cases t
    · -- step 0→1
      rw [horb0, horb1]; funext v; simp only [asyncStep, hsched0]
      cases v with
      | t i =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, sp0]
        cases hαi : α i <;> simp [hαi, x1, DNFBoolNet.localF, redNet2]
      | f i =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, sp0]
        cases hαi : α i <;> simp [hαi, x1, DNFBoolNet.localF, redNet2]
      | z _ => simp [Finset.mem_filter, sp0, x1]
      | w _ => simp [Finset.mem_filter, sp0, x1]
      | c _ => simp [Finset.mem_filter, sp0, x1]
    · -- step 1→2
      rw [horb1, horb2]; funext v; simp only [asyncStep, hsched1]
      cases v with
      | t i => simp [Finset.mem_filter, sp1, x1, x2]
      | f i => simp [Finset.mem_filter, sp1, x1, x2]
      | z j =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, sp1]
        by_cases h0 : lj j = 0
        · simp only [h0, beq_self_eq_true, ite_true, x2, ite_true, DNFBoolNet.localF]
          have hwj := hwit j; simp only [h0, gcl] at hwj
          simp only [redNet2, gcl, x1, List.any_cons, List.any_nil, Bool.or_false,
            hwj, Bool.true_or, and_self, ite_true]
        · have : (lj j == 0) = false := beq_eq_false_iff_ne.mpr (by exact_mod_cast h0)
          simp [this, x1, x2, h0]
      | w j =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, sp1]
        by_cases h1 : lj j = 1
        · have hwj := hwit j; simp only [h1, gcl] at hwj
          have hbeq : (lj j == 1) = true := beq_iff_eq.mpr h1
          simp only [hbeq, ite_true, x2, h1, DNFBoolNet.localF]
          have hany : ((redNet2 φ).guard (TV2.w j)).any
            (fun term => term.all (fun lit => @decide (lit.holds x1) (inferInstance))) = true := by
            simp only [redNet2, gcl, List.any_cons, List.any_nil, Bool.or_false, hwj, Bool.true_or]
          rw [if_pos (And.intro rfl hany)]; simp
        · have : (lj j == 1) = false := beq_eq_false_iff_ne.mpr (by exact_mod_cast h1)
          simp [this, x1, x2, h1]
      | c j =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, sp1]
        by_cases h2 : lj j = 2
        · have hwj := hwit j; simp only [h2, gcl] at hwj
          have hbeq : (lj j == 2) = true := beq_iff_eq.mpr h2
          simp only [hbeq, ite_true, x2, h2, DNFBoolNet.localF]
          have hany : ((redNet2 φ).guard (TV2.c j)).any
            (fun term => term.all (fun lit => @decide (lit.holds x1) (inferInstance))) = true := by
            simp only [redNet2, gcl, List.any_cons, List.any_nil, Bool.or_false, hwj, Bool.or_true]
          rw [if_pos (And.intro rfl hany)]; simp
        · have : (lj j == 2) = false := beq_eq_false_iff_ne.mpr (by exact_mod_cast h2)
          simp [this, x1, x2, h2]
    · -- step 2→3
      rw [horb2, horb3]; funext v; simp only [asyncStep, hsched2]
      cases v with
      | t i => simp [Finset.mem_filter, x2, x3]
      | f i => simp [Finset.mem_filter, x2, x3]
      | z j =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h2 : lj j = 2
        · have hcj : x2 (.c j) = 1 := by simp [x2, h2]
          simp [sp2, h2, x3, x2, DNFBoolNet.localF, redNet2, gcl,
            lb_all2 (.c j) x2 hcj]
        · rcases hfin3 (lj j) with h0 | h1 | h2'
          · simp [sp2, x2, x3, h0, h2]
          · simp [sp2, x2, x3, h1, h2]
          · exact absurd h2' h2
      | w j =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h0 : lj j = 0
        · have hzj : x2 (.z j) = 1 := by simp [x2, h0]
          simp [sp2, h0, x3, x2, DNFBoolNet.localF, redNet2, gcl,
            lb_all2 (.z j) x2 hzj]
        · rcases hfin3 (lj j) with h0' | h1 | h2
          · exact absurd h0' h0
          · simp [sp2, x2, x3, h1, h0]
          · simp [sp2, x2, x3, h2, h0]
      | c j =>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h1 : lj j = 1
        · have hwj : x2 (.w j) = 1 := by simp [x2, h1]
          simp [sp2, h1, x3, x2, DNFBoolNet.localF, redNet2, gcl,
            lb_all2 (.w j) x2 hwj]
        · rcases hfin3 (lj j) with h0 | h1' | h2
          · simp [sp2, x2, x3, h0, h1]
          · exact absurd h1' h1
          · simp [sp2, x2, x3, h2, h1]
    · -- step 3→4
      rw [horb3]; funext v; simp only [asyncStep, hsched3, Finset.mem_univ, ite_true]
      have horb4v : orbit ⟨4, by omega⟩ v = 1 := by simp [orbit]
      rw [horb4v]
      cases v with
      | t i => simp [DNFBoolNet.localF, x3, redNet2]
      | f i => simp [DNFBoolNet.localF, x3, redNet2]
      | z j =>
        rcases hfin3 (lj j) with h0 | h1 | h2
        · simp [DNFBoolNet.localF, x3, h0]
        · have hcj : x3 (.c j) = 1 := by simp [x3, h1]
          have hzj0 : x3 (.z j) = 0 := by simp [x3]; omega
          simp [DNFBoolNet.localF, redNet2, gcl, x3, lb_all2 (.c j) x3 hcj, hzj0]
        · simp [DNFBoolNet.localF, x3, h2]
      | w j =>
        rcases hfin3 (lj j) with h0 | h1 | h2
        · simp [DNFBoolNet.localF, x3, h0]
        · simp [DNFBoolNet.localF, x3, h1]
        · have hzj : x3 (.z j) = 1 := by simp [x3, h2]
          have hwj0 : x3 (.w j) = 0 := by simp [x3]; omega
          simp [DNFBoolNet.localF, redNet2, gcl, x3, lb_all2 (.z j) x3 hzj, hwj0]
      | c j =>
        rcases hfin3 (lj j) with h0 | h1 | h2
        · have hwj : x3 (.w j) = 1 := by simp [x3, h0]
          have hcj0 : x3 (.c j) = 0 := by simp [x3]; omega
          simp [DNFBoolNet.localF, redNet2, gcl, x3, lb_all2 (.w j) x3 hwj, hcj0]
        · simp [DNFBoolNet.localF, x3, h1]
        · simp [DNFBoolNet.localF, x3, h2]

theorem reach2_implies_sat (φ : CNF3)
    (hReach : (redNet2 φ).reachable (fun _ => 0) (fun _ => 1)) :
    φ.satisfiable := by
  obtain ⟨T, orbit, sched, hx, hy, hOrbit⟩ := hReach
  have hMono : ∀ t : Fin T, ∀ v,
      orbit ⟨t.val, by omega⟩ v ≤ orbit ⟨t.val + 1, by omega⟩ v := by
    intro t v; rw [hOrbit t]; exact asyncStep_freeze (DNFBoolNet.localF_freezing _) _ _ v
  let gcl (j : Fin φ.cls.length) := φ.cls.get ⟨j, j.isLt⟩
  refine ⟨fun i => activationTime orbit (.t i) < activationTime orbit (.f i), ?_⟩
  intro cls hcls
  have hcIdx : ∃ j : Fin φ.cls.length, gcl j = cls := by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcls; exact ⟨⟨j, hj⟩, rfl⟩
  obtain ⟨j, hcj⟩ := hcIdx; subst hcj
  have find_flip : ∀ (u : TV2 φ.n φ.cls.length),
      orbit ⟨0, by omega⟩ u = 0 → orbit ⟨T, by omega⟩ u = 1 →
      ∃ t0 : Fin T, orbit ⟨t0.val, by omega⟩ u = 0 ∧
        orbit ⟨t0.val + 1, by omega⟩ u = 1 := by
    intro u h0u hTu
    suffices ∀ t : Fin (T + 1), orbit t u = 0 ∨
        ∃ s : Fin T, orbit ⟨s.val, by omega⟩ u = 0 ∧
          orbit ⟨s.val + 1, by omega⟩ u = 1 by
      rcases this ⟨T, by omega⟩ with h | ⟨s, hs⟩
      · exact absurd h (by simp [hTu])
      · exact ⟨s, hs⟩
    intro ⟨t, ht⟩; induction t with
    | zero => left; exact h0u
    | succ k ih =>
      rcases ih (by omega) with hk0 | ⟨s, hs⟩
      · rcases fin2_eq_zero_or_one' (orbit ⟨k + 1, ht⟩ u) with h | h
        · left; exact h
        · right; exact ⟨⟨k, by omega⟩, hk0, h⟩
      · right; exact ⟨s, hs⟩
  have hT_pos : 0 < T := by
    by_contra h0; push_neg at h0; have hT0 : T = 0 := by omega
    have := congr_fun hx (.c j); have := congr_fun hy (.c j); simp_all
  have get_term : ∀ (u : TV2 φ.n φ.cls.length) (tu : Fin T),
      orbit ⟨tu.val, by omega⟩ u = 0 → orbit ⟨tu.val + 1, by omega⟩ u = 1 →
      ∃ term ∈ (redNet2 φ).guard u,
        term.all (fun lit => @decide (lit.holds (orbit ⟨tu.val, by omega⟩)) (inferInstance)) = true := by
    intro u tu h0u h1u
    have hstep := congr_fun (hOrbit tu) u; simp only [asyncStep] at hstep
    split_ifs at hstep with hmem
    · rw [h1u] at hstep; simp only [DNFBoolNet.localF] at hstep
      split_ifs at hstep with hcond
      · obtain ⟨_, hany⟩ := hcond; rw [List.any_eq_true] at hany
        exact hany
      · rw [h0u] at hstep; simp at hstep
    · rw [h0u] at hstep; rw [hstep] at h1u; simp at h1u
  obtain ⟨tc, htc0, htc1⟩ := find_flip (.c j)
    (by have := congr_fun hx (.c j); simp at this; exact this)
    (by have := congr_fun hy (.c j); simp at this; exact this)
  obtain ⟨tz, htz0, htz1⟩ := find_flip (.z j)
    (by have := congr_fun hx (.z j); simp at this; exact this)
    (by have := congr_fun hy (.z j); simp at this; exact this)
  obtain ⟨tw, htw0, htw1⟩ := find_flip (.w j)
    (by have := congr_fun hx (.w j); simp at this; exact this)
    (by have := congr_fun hy (.w j); simp at this; exact this)
  have from_wit : ∀ (l : Fin 3) (tu : Fin T),
      (witnessTerm2 ((gcl j) l).1 ((gcl j) l).2).all
        (fun lit => @decide (lit.holds (orbit ⟨tu.val, by omega⟩)) (inferInstance)) = true →
      ∃ k : Fin 3,
        (((gcl j) k).2 = true ∧ decide (activationTime orbit (.t ((gcl j) k).1) <
          activationTime orbit (.f ((gcl j) k).1)) = true) ∨
        (((gcl j) k).2 = false ∧ decide (activationTime orbit (.t ((gcl j) k).1) <
          activationTime orbit (.f ((gcl j) k).1)) = false) := by
    intro l tu hall
    have hw : (witnessTerm2 ((gcl j) l).1 ((gcl j) l).2).holds (orbit ⟨tu.val, by omega⟩) :=
      fun lit hlit => decide_eq_true_eq.mp (List.all_eq_true.mp hall lit hlit)
    have hord := witness_implies_order2 orbit hMono ⟨tu.val, by omega⟩
      ((gcl j) l).1 ((gcl j) l).2 hw
    refine ⟨l, ?_⟩
    cases hb : ((gcl j) l).2
    · rw [hb] at hord; simp only [Bool.false_eq_true, ite_false] at hord
      right; exact ⟨rfl, decide_eq_false_iff_not.mpr (not_lt.mpr (Nat.le_of_lt hord))⟩
    · rw [hb] at hord; simp only [ite_true] at hord
      left; exact ⟨rfl, decide_eq_true_eq.mpr hord⟩
  have lb_read : ∀ (u : TV2 φ.n φ.cls.length) (tu : Fin T),
      ([.lb u 1] : ConjGuard (TV2 φ.n φ.cls.length) 1).all
        (fun lit => @decide (lit.holds (orbit ⟨tu.val, by omega⟩)) (inferInstance)) = true →
      orbit ⟨tu.val, by omega⟩ u = 1 := by
    intro u tu hall; rw [List.all_cons, List.all_nil, Bool.and_true] at hall
    exact fin2_one_le' _ (decide_eq_true_eq.mp hall)
  obtain ⟨term_c, hmem_c, hall_c⟩ := get_term (.c j) tc htc0 htc1
  simp only [redNet2, gcl] at hmem_c
  rcases List.mem_cons.mp hmem_c with rfl | hmem_c'
  · have hwj1 := lb_read (.w j) tc hall_c
    obtain ⟨term_w, hmem_w, hall_w⟩ := get_term (.w j) tw htw0 htw1
    simp only [redNet2, gcl] at hmem_w
    rcases List.mem_cons.mp hmem_w with rfl | hmem_w'
    · exact from_wit 1 tw hall_w
    · rcases List.mem_cons.mp hmem_w' with rfl | hmem_w''
      · have hzj1 := lb_read (.z j) tw hall_w
        obtain ⟨term_z, hmem_z, hall_z⟩ := get_term (.z j) tz htz0 htz1
        simp only [redNet2, gcl] at hmem_z
        rcases List.mem_cons.mp hmem_z with rfl | hmem_z'
        · exact from_wit 0 tz hall_z
        · rcases List.mem_cons.mp hmem_z' with rfl | hmem_z''
          · have hcj1 := lb_read (.c j) tz hall_z
            exfalso
            have htcT := Nat.le_of_lt tc.isLt
            have htwT := Nat.le_of_lt tw.isLt
            have htzT := Nat.le_of_lt tz.isLt
            have h1 : tw.val < tc.val := by
              by_contra hge; push_neg at hge
              have hmle := orbit_mono_le' orbit hMono (.w j) hge htwT
              rw [hwj1] at hmle; rw [htw0] at hmle; exact absurd hmle (by simp)
            have h2 : tz.val < tw.val := by
              by_contra hge; push_neg at hge
              have hmle := orbit_mono_le' orbit hMono (.z j) hge htzT
              rw [hzj1] at hmle; rw [htz0] at hmle; exact absurd hmle (by simp)
            have h3 : tc.val < tz.val := by
              by_contra hge; push_neg at hge
              have hmle := orbit_mono_le' orbit hMono (.c j) hge htcT
              rw [hcj1] at hmle; rw [htc0] at hmle; exact absurd hmle (by simp)
            omega
          · simp at hmem_z''
      · simp at hmem_w''
  · rcases List.mem_cons.mp hmem_c' with rfl | hmem_c''
    · exact from_wit 2 tc hall_c
    · simp at hmem_c''

theorem two_term_reduction_iff (φ : CNF3) :
    φ.satisfiable ↔
    (redNet2 φ).reachable (fun _ => 0) (fun _ => 1) :=
  ⟨sat_implies_reach2 φ, reach2_implies_sat φ⟩

end TwoTermNPHard

end FreezingNetworks
