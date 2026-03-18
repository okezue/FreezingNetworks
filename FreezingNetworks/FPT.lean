import FreezingNetworks.Defs

namespace FreezingNetworks

variable {V : Type*} [Fintype V] [DecidableEq V]

structure DisjUIFN (V : Type*) [Fintype V] [DecidableEq V] (h : ℕ) where
  graph : SimpleGraph V
  [graphDec : DecidableRel graph.Adj]
  guard : V → Fin h → List (ConjGuard V h)

attribute [instance] DisjUIFN.graphDec

def DisjUIFN.localF {h : ℕ} (N : DisjUIFN V h)
    (v : V) (x : Config V h) : Fin (h + 1) :=
  if hlt : (x v).val < h then
    if (N.guard v ⟨(x v).val, hlt⟩).any (fun term =>
      term.all (fun lit => @decide (lit.holds x) (inferInstance)))
    then ⟨(x v).val + 1, by omega⟩
    else x v
  else x v

theorem DisjUIFN.localF_freezing {h : ℕ} (N : DisjUIFN V h)
    (v : V) (x : Config V h) : x v ≤ N.localF v x := by
  simp only [localF]
  split
  · split
    · exact Fin.le_iff_val_le_val.mpr (Nat.le_succ _)
    · exact le_refl _
  · exact le_refl _

def DisjUIFN.reachable {h : ℕ} (N : DisjUIFN V h)
    (x y : Config V h) : Prop :=
  asyncReachable N.localF x y

noncomputable def chooseBranch {h : ℕ} (N : DisjUIFN V h)
    (σ : V → Fin h → ℕ) : CIUIFN V h where
  graph := N.graph
  graphDec := N.graphDec
  guard := fun v k =>
    let terms := N.guard v k
    if terms.length ≤ 1 then terms.head?.getD []
    else terms.getD (σ v k % terms.length) []

section Helpers

variable {h : ℕ}

theorem cb_guard_mem (N : DisjUIFN V h) (σ : V → Fin h → ℕ)
    (v : V) (k : Fin h) (hne : N.guard v k ≠ []) :
    (chooseBranch N σ).guard v k ∈ N.guard v k := by
  unfold chooseBranch; simp only; split
  · obtain ⟨a, tl, heq⟩ := List.exists_cons_of_ne_nil hne; rw [heq]; simp [List.head?]
  · rename_i hgt; push_neg at hgt
    have hmod := Nat.mod_lt (σ v k) (by omega : (N.guard v k).length > 0)
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by omega)]; simp

theorem incr_agree (N : DisjUIFN V h) (σ : V → Fin h → ℕ) (v : V)
    (x : Config V h) (hne : ∀ k : Fin h, N.guard v k ≠ []) :
    CIUIFN.localF (chooseBranch N σ) v x = x v ∨
    DisjUIFN.localF N v x = CIUIFN.localF (chooseBranch N σ) v x := by
  simp only [CIUIFN.localF, DisjUIFN.localF]
  by_cases hl : (x v).val < h
  · rw [dif_pos hl, dif_pos hl]
    by_cases hg : ((chooseBranch N σ).guard v ⟨(x v).val, hl⟩).holds x
    · right; rw [if_pos hg, if_pos (List.any_eq_true.mpr ⟨_,
        cb_guard_mem N σ v _ (hne _),
        by rw [List.all_eq_true]; intro l hl'; exact decide_eq_true_eq.mpr (hg l hl')⟩)]
    · left; rw [if_neg hg]
  · left; rw [dif_neg hl]

end Helpers

theorem fpt_soundness {h : ℕ} (N : DisjUIFN V h)
    (x y : Config V h) (σ : V → Fin h → ℕ)
    (hne : ∀ v (k : Fin h), N.guard v k ≠ [])
    (hReach : (chooseBranch N σ).reachable x y) :
    N.reachable x y := by
  obtain ⟨T, o, s, hx, hy, hO⟩ := hReach
  let s' : Fin T → Finset V := fun t =>
    (s t).filter fun v =>
      CIUIFN.localF (chooseBranch N σ) v (o ⟨t.val, by omega⟩) ≠ (o ⟨t.val, by omega⟩) v
  refine ⟨T, o, s', hx, hy, ?_⟩
  intro t; ext v
  have hstep := congr_fun (hO t) v
  simp only [asyncStep] at hstep ⊢
  by_cases hv : v ∈ s t
  · rw [if_pos hv] at hstep
    rcases incr_agree N σ v (o ⟨t.val, by omega⟩) (hne v) with heq | heq
    · have hv' : v ∉ s' t := by
        simp only [s', Finset.mem_filter]; push_neg; intro _; exact heq
      rw [if_neg hv', hstep, heq]
    · by_cases hv' : v ∈ s' t
      · rw [if_pos hv', hstep, heq]
      · simp only [s', Finset.mem_filter, not_and, not_not] at hv'
        rw [if_neg (by simp [s', Finset.mem_filter, not_and]; exact fun _ => hv' hv),
            hstep, hv' hv]
  · rw [if_neg hv] at hstep
    have hv' : v ∉ s' t := by
      simp only [s', Finset.mem_filter]; push_neg; intro h; exact absurd h hv
    rw [if_neg hv', hstep]

theorem disj_guard_gives_index {h : ℕ} (N : DisjUIFN V h) (v : V)
    (x : Config V h) (hl : (x v).val < h)
    (hany : (N.guard v ⟨(x v).val, hl⟩).any (fun t =>
      t.all (fun l => @decide (l.holds x) (inferInstance))) = true) :
    ∃ idx : ℕ, ∃ hb : idx < (N.guard v ⟨(x v).val, hl⟩).length,
      ((N.guard v ⟨(x v).val, hl⟩)[idx]'hb).holds x := by
  rw [List.any_eq_true] at hany
  obtain ⟨term, hmem, hall⟩ := hany
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  exact ⟨i, hi, fun l hl' => decide_eq_true_eq.mp ((List.all_eq_true.mp hall) l hl')⟩

/-- For each disjunctive event in the reaching orbit, pick the satisfied disjunct.
Aristotle-verified: project e406345d-1578-4ac1-9683-1e27d963340b -/
theorem fpt_completeness {h : ℕ} (N : DisjUIFN V h)
    (x y : Config V h) (hle : configLE x y)
    (hReach : N.reachable x y) :
    ∃ σ : V → Fin h → ℕ,
      (chooseBranch N σ).reachable x y := by
  obtain ⟨T, orbit, sched, hx, hy, hO⟩ := hReach
  have hTransUniq : ∀ (w : V) (kv : ℕ) (t₁ t₂ : Fin T),
      ((orbit ⟨t₁.val, by omega⟩ w).val = kv ∧
       (orbit ⟨t₁.val + 1, by omega⟩ w).val = kv + 1) →
      ((orbit ⟨t₂.val, by omega⟩ w).val = kv ∧
       (orbit ⟨t₂.val + 1, by omega⟩ w).val = kv + 1) →
      t₁ = t₂ := by
    intro w kv t₁ t₂ ⟨hv1, hf1⟩ ⟨hv2, hf2⟩
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h12 | h21
    · have hm := orbit_mono_trans (DisjUIFN.localF_freezing N) orbit sched hO w
        (by omega : t₁.val + 1 ≤ t₂.val) (by omega : t₂.val ≤ T)
      have := Fin.val_le_of_le hm; omega
    · have hm := orbit_mono_trans (DisjUIFN.localF_freezing N) orbit sched hO w
        (by omega : t₂.val + 1 ≤ t₁.val) (by omega : t₁.val ≤ T)
      have := Fin.val_le_of_le hm; omega
  let σ : V → Fin h → ℕ := fun v k =>
    if hex : ∃ t : Fin T, v ∈ sched t ∧
        (orbit ⟨t.val, by omega⟩ v).val = k.val ∧
        (orbit ⟨t.val + 1, by omega⟩ v).val = k.val + 1
    then
      let cfg := orbit ⟨hex.choose.val, by omega⟩
      if hlt : (cfg v).val < h then
        if hany : (N.guard v ⟨(cfg v).val, hlt⟩).any (fun term =>
          term.all (fun lit => @decide (lit.holds cfg) (inferInstance))) = true then
          (disj_guard_gives_index N v cfg hlt hany).choose
        else 0
      else 0
    else 0
  let sched' : Fin T → Finset V := fun t =>
    (sched t).filter fun v =>
      N.localF v (orbit ⟨t.val, by omega⟩) ≠ (orbit ⟨t.val, by omega⟩) v
  refine ⟨σ, T, orbit, sched', hx, hy, ?_⟩
  intro t; funext v
  have hstepO := congr_fun (hO t) v
  simp only [asyncStep] at hstepO ⊢
  by_cases hmem' : v ∈ sched' t
  · have hmem : v ∈ sched t := (Finset.mem_filter.mp hmem').1
    have hne_v : N.localF v (orbit ⟨t.val, by omega⟩) ≠ orbit ⟨t.val, by omega⟩ v :=
      (Finset.mem_filter.mp hmem').2
    rw [if_pos hmem'] at ⊢; rw [if_pos hmem] at hstepO; rw [hstepO]
    set cfg := orbit ⟨t.val, by omega⟩ with hcfg_def
    simp only [DisjUIFN.localF] at hne_v
    simp only [DisjUIFN.localF, CIUIFN.localF]
    by_cases hlt : (cfg v).val < h
    · rw [dif_pos hlt, dif_pos hlt]
      rw [dif_pos hlt] at hne_v
      by_cases hany : (N.guard v ⟨(cfg v).val, hlt⟩).any (fun term =>
        term.all (fun lit => @decide (lit.holds cfg) (inferInstance))) = true
      · rw [if_pos hany]
        have hfire : (orbit ⟨t.val + 1, by omega⟩ v).val = (cfg v).val + 1 := by
          simp only [DisjUIFN.localF] at hstepO
          rw [dif_pos hlt, if_pos hany] at hstepO
          exact congrArg Fin.val hstepO
        have hex : ∃ t' : Fin T, v ∈ sched t' ∧
            (orbit ⟨t'.val, by omega⟩ v).val = (cfg v).val ∧
            (orbit ⟨t'.val + 1, by omega⟩ v).val = (cfg v).val + 1 :=
          ⟨t, hmem, rfl, hfire⟩
        have hchoose_eq : hex.choose = t :=
          hTransUniq v (cfg v).val hex.choose t hex.choose_spec.2 ⟨rfl, hfire⟩
        suffices hg : ((chooseBranch N σ).guard v ⟨(cfg v).val, hlt⟩).holds cfg by
          rw [if_pos hg]
        unfold chooseBranch; simp only
        set guards := N.guard v ⟨(cfg v).val, hlt⟩
        have hne_guards : guards ≠ [] := by
          intro hempty; rw [hempty] at hany; simp at hany
        by_cases hlen : guards.length ≤ 1
        · rw [if_pos hlen]
          rcases guards with _ | ⟨a, tl⟩
          · exact absurd rfl hne_guards
          · simp only [List.head?, Option.getD_some]
            have htl : tl = [] := by
              have : tl.length + 1 ≤ 1 := hlen
              rcases tl with _ | ⟨b, tl'⟩
              · rfl
              · simp at this
            subst htl
            simp only [List.any_cons, List.any_nil, Bool.or_false] at hany
            exact fun l hl' => decide_eq_true_eq.mp ((List.all_eq_true.mp hany) l hl')
        · rw [if_neg hlen]
          show (guards.getD (σ v ⟨(cfg v).val, hlt⟩ % guards.length) []).holds cfg
          simp only [σ, dif_pos hex]
          have hcfg_same : (⟨hex.choose.val, by omega⟩ : Fin (T + 1)) = ⟨t.val, by omega⟩ :=
            Fin.ext (show hex.choose.val = t.val from congrArg Fin.val hchoose_eq)
          simp only [hcfg_same]
          rw [dif_pos hlt]
          rw [dif_pos hany]
          set pi := (disj_guard_gives_index N v cfg hlt hany).choose
          have ⟨hpi_lt, hpi_holds⟩ := (disj_guard_gives_index N v cfg hlt hany).choose_spec
          rw [Nat.mod_eq_of_lt hpi_lt]
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_getElem hpi_lt]; simp only [Option.getD_some]
          exact hpi_holds
      · exfalso; rw [if_neg hany] at hne_v; exact hne_v rfl
    · exfalso; rw [dif_neg hlt] at hne_v; exact hne_v rfl
  · rw [if_neg hmem']
    by_cases hmem : v ∈ sched t
    · rw [if_pos hmem] at hstepO
      have hno_change : N.localF v (orbit ⟨t.val, by omega⟩) = orbit ⟨t.val, by omega⟩ v := by
        by_contra hne_v
        exact hmem' (Finset.mem_filter.mpr ⟨hmem, hne_v⟩)
      rw [hstepO, hno_change]
    · rw [if_neg hmem] at hstepO; exact hstepO

theorem fpt_iff {h : ℕ} (N : DisjUIFN V h)
    (x y : Config V h) (hle : configLE x y)
    (hne : ∀ v (k : Fin h), N.guard v k ≠ []) :
    N.reachable x y ↔
    ∃ σ : V → Fin h → ℕ, (chooseBranch N σ).reachable x y :=
  ⟨fpt_completeness N x y hle,
   fun ⟨σ, h⟩ => fpt_soundness N x y σ hne h⟩

end FreezingNetworks
