import FreezingNetworks.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Duplicate

namespace FreezingNetworks

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

instance {h : ℕ} : Fintype (IncrEvent V h) :=
  Fintype.ofEquiv (V × Fin h)
    { toFun := fun ⟨v, k⟩ => ⟨v, k⟩,
      invFun := fun ⟨v, k⟩ => ⟨v, k⟩,
      left_inv := fun _ => rfl,
      right_inv := fun _ => rfl }

@[simp]
def maxPW {h : ℕ} (G : EventDigraph V h) (k : ℕ) (v : IncrEvent V h) : ℕ :=
  match k with
  | 0 => 0
  | n + 1 =>
    List.foldl max (maxPW G n v)
      (List.filterMap (fun (e : WtEdge V h) =>
        if e.tgt = v then some (maxPW G n e.src + e.wt) else none) G.edges)

lemma maxPW_increasing {h : ℕ} (G : EventDigraph V h) (k : ℕ) (v : IncrEvent V h) :
    maxPW G k v ≤ maxPW G (k + 1) v := by
  simp [maxPW]
  induction (List.filterMap (fun e : WtEdge V h =>
    if e.tgt = v then Option.some (maxPW G k e.src + e.wt) else Option.none)
    G.edges) using List.reverseRecOn <;> simp_all [List.foldl]

private lemma pathWt_append {h : ℕ} (p q : List (WtEdge V h)) :
    pathWt (p ++ q) = pathWt p + pathWt q := by
  induction p with
  | nil => simp [pathWt]
  | cons e es ih => simp [pathWt, ih]; omega

private lemma dwalk_append {h : ℕ} {edges : List (WtEdge V h)}
    {a b c : IncrEvent V h} {p q : List (WtEdge V h)}
    (hp : DWalk edges a b p) (hq : DWalk edges b c q) :
    DWalk edges a c (p ++ q) := by
  induction hp with
  | nil _ => exact hq
  | cons hmem _ ih => exact DWalk.cons hmem (ih hq)

private lemma foldl_max_ge_init (init : ℕ) (l : List ℕ) :
    init ≤ List.foldl max init l := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl]
    exact le_trans (Nat.le_max_left _ _) (ih _)

private lemma foldl_max_mem {l : List ℕ} {init x : ℕ} (hx : x ∈ l) :
    x ≤ List.foldl max init l := by
  induction l generalizing init with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp hx with rfl | hm
    · exact le_trans (Nat.le_max_right _ _) (foldl_max_ge_init _ _)
    · exact ih hm

private lemma foldl_max_gt_init_mem {init : ℕ} {l : List ℕ}
    (h : List.foldl max init l > init) :
    ∃ x ∈ l, x = List.foldl max init l := by
  induction l using List.reverseRecOn generalizing init with
  | nil => simp at h
  | append_singleton xs x ih =>
    simp only [List.foldl_append, List.foldl] at *
    by_cases hle : x ≤ List.foldl max init xs
    · rw [max_eq_left hle] at h ⊢
      obtain ⟨y, hy, heq⟩ := ih h
      exact ⟨y, List.mem_append_left _ hy, heq⟩
    · push_neg at hle
      rw [max_eq_right (le_of_lt hle)] at h ⊢
      exact ⟨x, List.mem_append_right _ (List.mem_singleton.mpr rfl), rfl⟩

private lemma maxPW_ge_of_edge {h : ℕ} (G : EventDigraph V h) (k : ℕ)
    {u v : IncrEvent V h} {w : ℕ} (he : ⟨u, v, w⟩ ∈ G.edges) :
    maxPW G (k + 1) v ≥ maxPW G k u + w := by
  simp only [maxPW]
  apply foldl_max_mem
  rw [List.mem_filterMap]
  exact ⟨⟨u, v, w⟩, he, by simp⟩

lemma maxPW_spec {h : ℕ} (G : EventDigraph V h) (k : ℕ) (v : IncrEvent V h) :
    ∃ (u : IncrEvent V h) (p : List (WtEdge V h)),
      DWalk G.edges u v p ∧ p.length ≤ k ∧ pathWt p = maxPW G k v := by
  induction k generalizing v with
  | zero => exact ⟨v, [], DWalk.nil v, by simp, rfl⟩
  | succ k ih =>
    simp only [maxPW]
    set fv := List.foldl max (maxPW G k v)
      (List.filterMap (fun e : WtEdge V h =>
        if e.tgt = v then some (maxPW G k e.src + e.wt) else none) G.edges)
    rcases Nat.lt_or_ge (maxPW G k v) fv with hlt | hle
    · obtain ⟨val, hval_mem, hval_eq⟩ := foldl_max_gt_init_mem hlt
      rw [List.mem_filterMap] at hval_mem
      obtain ⟨e, he_edges, he_val⟩ := hval_mem
      by_cases htgt : e.tgt = v
      · simp only [htgt, ite_true, Option.some.injEq] at he_val
        obtain ⟨u, p, hpu, hplen, hpwt⟩ := ih e.src
        refine ⟨u, p ++ [e], dwalk_append hpu (htgt ▸ DWalk.cons he_edges (DWalk.nil _)),
          by simp; omega, ?_⟩
        rw [pathWt_append]
        simp only [pathWt, Nat.add_zero]
        linarith [hpwt.symm, he_val.symm, hval_eq.symm]
      · simp only [htgt, ite_false] at he_val
        exact absurd he_val (by simp)
    · have heq : fv = maxPW G k v := le_antisymm hle (foldl_max_ge_init _ _)
      obtain ⟨u, p, hpw, hpl, hpwt⟩ := ih v
      exact ⟨u, p, hpw, Nat.le_succ_of_le hpl, by rw [heq]; exact hpwt⟩

private lemma dwalk_reverse_split {h : ℕ} {edges : List (WtEdge V h)}
    {u v : IncrEvent V h} {p : List (WtEdge V h)}
    (hp : DWalk edges u v p) (hp_ne : p ≠ []) :
    ∃ (x : IncrEvent V h) (w : ℕ) (pref : List (WtEdge V h)),
      p = pref ++ [⟨x, v, w⟩] ∧ ⟨x, v, w⟩ ∈ edges ∧ DWalk edges u x pref := by
  induction hp with
  | nil _ => exact absurd rfl hp_ne
  | @cons a b c w rest hmem hrest ih =>
    cases Decidable.em (rest = []) with
    | inl hemp =>
      subst hemp; cases hrest
      exact ⟨a, w, [], by simp, hmem, DWalk.nil a⟩
    | inr hne =>
      obtain ⟨x, w', pref, hp_eq, he_mem, hpref⟩ := ih hne
      exact ⟨x, w', ⟨a, b, w⟩ :: pref, by simp [hp_eq], he_mem, DWalk.cons hmem hpref⟩

lemma pathWt_le_maxPW {h : ℕ} (G : EventDigraph V h) (k : ℕ)
    {u v : IncrEvent V h} {p : List (WtEdge V h)}
    (hp : DWalk G.edges u v p) (hlen : p.length ≤ k) :
    pathWt p ≤ maxPW G k v := by
  induction k generalizing u v p with
  | zero =>
    cases hp with
    | nil _ => simp [pathWt]
    | cons _ _ => simp at hlen
  | succ k ih =>
    cases Decidable.em (p = []) with
    | inl hemp => subst hemp; cases hp; simp [pathWt]
    | inr hne =>
      obtain ⟨x, w, pref, hp_eq, he_mem, hpref⟩ := dwalk_reverse_split hp hne
      subst hp_eq
      simp only [List.length_append, List.length_singleton] at hlen
      rw [pathWt_append]
      simp only [pathWt, Nat.add_zero]
      exact Nat.le_trans (by linarith [ih hpref (by omega)])
        (maxPW_ge_of_edge G k he_mem)

private lemma dwalk_vertices {h : ℕ} {edges : List (WtEdge V h)}
    {u v : IncrEvent V h} {p : List (WtEdge V h)}
    (hp : DWalk edges u v p) : v ∈ u :: p.map WtEdge.tgt := by
  induction hp with
  | nil e => simp
  | cons _ _ ih => simp only [List.map_cons, List.mem_cons] at ih ⊢; tauto

private lemma dwalk_split_at_vertex {h : ℕ} {edges : List (WtEdge V h)}
    {u v x : IncrEvent V h} {p : List (WtEdge V h)}
    (hp : DWalk edges u v p) (hx : x ∈ u :: p.map WtEdge.tgt) :
    ∃ (p1 p2 : List (WtEdge V h)),
      p = p1 ++ p2 ∧ DWalk edges u x p1 ∧ DWalk edges x v p2 := by
  induction hp with
  | nil e =>
    simp only [List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx; exact ⟨[], [], by simp, DWalk.nil x, DWalk.nil x⟩
  | @cons a b c w rest hmem hrest ih =>
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with hxa | hxb | hxrest
    · subst hxa; exact ⟨[], ⟨x, b, w⟩ :: rest, by simp, DWalk.nil x, DWalk.cons hmem hrest⟩
    · subst hxb; exact ⟨[⟨a, x, w⟩], rest, by simp, DWalk.cons hmem (DWalk.nil x), hrest⟩
    · have hx_in : x ∈ b :: rest.map WtEdge.tgt := List.mem_cons.mpr (Or.inr hxrest)
      obtain ⟨p1, p2, hp_eq, hw1, hw2⟩ := ih hx_in
      exact ⟨⟨a, b, w⟩ :: p1, p2, by simp [hp_eq], DWalk.cons hmem hw1, hw2⟩

private lemma dwalk_split_cyc_general {h : ℕ} {edges : List (WtEdge V h)}
    {u v : IncrEvent V h} {p : List (WtEdge V h)}
    (hp : DWalk edges u v p)
    (hnodup : ¬(u :: p.map WtEdge.tgt).Nodup) :
    ∃ (x : IncrEvent V h) (p1 cyc p2 : List (WtEdge V h)),
      p = p1 ++ cyc ++ p2 ∧ cyc ≠ [] ∧
      DWalk edges u x p1 ∧ DWalk edges x x cyc ∧ DWalk edges x v p2 := by
  induction hp with
  | nil e => simp at hnodup
  | @cons a b c w rest hmem hrest ih =>
    simp only [List.map_cons] at hnodup
    rw [show a :: WtEdge.tgt ⟨a, b, w⟩ :: List.map WtEdge.tgt rest =
        a :: b :: rest.map WtEdge.tgt from rfl] at hnodup
    rw [List.nodup_cons, not_and_or, not_not] at hnodup
    rcases hnodup with ha_dup | hnodup_rest
    · obtain ⟨q1, q2, hq_eq, hw1, hw2⟩ := dwalk_split_at_vertex hrest ha_dup
      exact ⟨a, [], ⟨a, b, w⟩ :: q1, q2,
             by simp [hq_eq], by simp,
             DWalk.nil a, DWalk.cons hmem hw1, hw2⟩
    · obtain ⟨x, p1, cyc, p2, hp_eq, hcyc_ne, hw1, hwcyc, hw2⟩ := ih hnodup_rest
      exact ⟨x, ⟨a, b, w⟩ :: p1, cyc, p2, by simp [hp_eq], hcyc_ne,
             DWalk.cons hmem hw1, hwcyc, hw2⟩

lemma shorter_walk_of_long {h : ℕ} (G : EventDigraph V h) (hG : ¬hasPosCycle G)
    {u v : IncrEvent V h} {p : List (WtEdge V h)}
    (hp : DWalk G.edges u v p)
    (hlen : p.length > Fintype.card (IncrEvent V h)) :
    ∃ p', DWalk G.edges u v p' ∧ p'.length < p.length ∧ pathWt p' ≥ pathWt p := by
  have hnodup : ¬(u :: p.map WtEdge.tgt).Nodup := fun hnd =>
    absurd (List.Nodup.length_le_card hnd) (by simp; omega)
  obtain ⟨x, p1, cyc, p2, hp_eq, hcyc_ne, hw1, hwcyc, hw2⟩ :=
    dwalk_split_cyc_general hp hnodup
  have hcyc_wt : pathWt cyc = 0 := by
    by_contra hpos; exact hG ⟨x, cyc, hwcyc, hcyc_ne, by omega⟩
  exact ⟨p1 ++ p2, dwalk_append hw1 hw2,
    by rw [hp_eq]; simp [List.length_append]
       have : cyc.length ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by simp [hcyc_ne])
       omega,
    by rw [hp_eq, pathWt_append, pathWt_append, pathWt_append]; omega⟩

lemma maxPW_succ_ge_add {h : ℕ} (G : EventDigraph V h) (k : ℕ)
    {u v : IncrEvent V h} {w : ℕ} (he : ⟨u, v, w⟩ ∈ G.edges) :
    maxPW G (k + 1) v ≥ maxPW G k u + w :=
  maxPW_ge_of_edge G k he

end

lemma maxPW_stabilizes {h : ℕ} (G : EventDigraph V h) (hG : ¬hasPosCycle G)
    (v : IncrEvent V h) :
    maxPW G (Fintype.card (IncrEvent V h)) v =
    maxPW G (Fintype.card (IncrEvent V h) + 1) v := by
  by_contra h_neq
  obtain ⟨u, p, hp, hp_len, hp_wt⟩ := maxPW_spec G (Fintype.card (IncrEvent V h) + 1) v
  by_cases hp_short : p.length ≤ Fintype.card (IncrEvent V h)
  · exact h_neq (le_antisymm (maxPW_increasing G _ _) (hp_wt ▸ pathWt_le_maxPW G _ hp hp_short))
  · obtain ⟨p', hp', hp'_len, hp'_wt⟩ := shorter_walk_of_long G hG hp (by omega)
    exact h_neq (le_antisymm (maxPW_increasing G _ _)
      (by linarith [pathWt_le_maxPW G _ hp' (by omega : p'.length ≤ Fintype.card (IncrEvent V h))]))

theorem validTiming_of_noPosCycle {h : ℕ}
    (G : EventDigraph V h) (hG : ¬hasPosCycle G) :
    ∃ τ : IncrEvent V h → ℤ, TimingValid G τ ∧ ∀ e, τ e ≥ 1 := by
  refine ⟨fun v => ↑(maxPW G (Fintype.card (IncrEvent V h)) v) + 1, ?_, ?_⟩
  · intro e he
    have h1 := maxPW_succ_ge_add G (Fintype.card (IncrEvent V h)) he
    have h2 := maxPW_stabilizes G hG e.tgt
    push_cast; linarith
  · intro e; push_cast; omega

end FreezingNetworks
