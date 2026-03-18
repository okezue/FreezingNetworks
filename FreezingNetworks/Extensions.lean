import FreezingNetworks.Defs
import FreezingNetworks.BellmanFord
import FreezingNetworks.MainTheorem
import FreezingNetworks.Reduction
import FreezingNetworks.FPT

namespace FreezingNetworks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Decidability of CI-UIFN reachability -/

noncomputable instance {h : ℕ} (N : CIUIFN V h) (x y : Config V h) :
    Decidable (N.reachable x y) :=
  Classical.dec _

/-! ## 2. SCC characterization of positive cycles -/

section SCCChar

variable {h : ℕ}

def inSameSCC (G : EventDigraph V h) (a b : IncrEvent V h) : Prop :=
  ∃ (p1 p2 : List (WtEdge V h)),
    DWalk G.edges a b p1 ∧ DWalk G.edges b a p2

private lemma dwalk_append {h : ℕ} {edges : List (WtEdge V h)}
    {a b c : IncrEvent V h} {p1 p2 : List (WtEdge V h)}
    (hw1 : DWalk edges a b p1) (hw2 : DWalk edges b c p2) :
    DWalk edges a c (p1 ++ p2) := by
  induction hw1 with
  | nil _ => exact hw2
  | cons hmem _ ih => exact DWalk.cons hmem (ih hw2)

private lemma dwalk_edge_mem {h : ℕ} {edges : List (WtEdge V h)}
    {a b : IncrEvent V h} {path : List (WtEdge V h)}
    (hw : DWalk edges a b path) (e : WtEdge V h) (he : e ∈ path) :
    e ∈ edges := by
  induction hw with
  | nil => exact absurd he List.not_mem_nil
  | cons hmem _ ih =>
    rcases List.mem_cons.mp he with rfl | h'
    · exact hmem
    · exact ih h'

private lemma dwalk_split_at {h : ℕ} {edges : List (WtEdge V h)}
    {a b : IncrEvent V h} {path : List (WtEdge V h)}
    (hw : DWalk edges a b path)
    {e : WtEdge V h} (he : e ∈ path) :
    ∃ p1 p2, DWalk edges a e.src p1 ∧ DWalk edges e.tgt b p2 := by
  induction hw with
  | nil => exact absurd he List.not_mem_nil
  | @cons a' b' c' w rest hmem hrest ih =>
    rcases List.mem_cons.mp he with rfl | h'
    · exact ⟨[], rest, DWalk.nil _, hrest⟩
    · obtain ⟨p1, p2, hw1, hw2⟩ := ih h'
      exact ⟨⟨a', b', w⟩ :: p1, p2, DWalk.cons hmem hw1, hw2⟩

theorem posCycle_iff_wt1_in_SCC (G : EventDigraph V h) :
    hasPosCycle G ↔
    ∃ e ∈ G.edges, e.wt ≥ 1 ∧ inSameSCC G e.src e.tgt := by
  constructor
  · intro ⟨v, path, hwalk, hne, hpos⟩
    have hexists : ∃ e ∈ path, e.wt ≥ 1 := by
      by_contra hall; push_neg at hall
      have : pathWt path = 0 := by
        clear hne hpos hwalk v
        induction path with
        | nil => rfl
        | cons e es ih =>
          simp [pathWt]; have := hall e List.mem_cons_self
          have := ih (fun e' he' => hall e' (List.mem_cons_of_mem _ he'))
          omega
      omega
    obtain ⟨e, hmem, hwt⟩ := hexists
    have hedge : e ∈ G.edges := dwalk_edge_mem hwalk e hmem
    refine ⟨e, hedge, hwt, ?_⟩
    obtain ⟨p1, p2, hw1, hw2⟩ := dwalk_split_at hwalk hmem
    exact ⟨[e], p2 ++ p1,
      DWalk.cons hedge (DWalk.nil _),
      dwalk_append hw2 hw1⟩
  · intro ⟨e, hmem, hwt, p1, p2, hw1, hw2⟩
    exact ⟨e.src, ⟨e.src, e.tgt, e.wt⟩ :: p2,
      DWalk.cons hmem hw2, by simp,
      by simp [pathWt]; omega⟩

end SCCChar

/-! ## 3. Bootstrap percolation as a CI-UIFN -/

section Bootstrap

noncomputable def bootstrapNet (G : SimpleGraph V) [DecidableRel G.Adj]
    (thr : V → ℕ) : CIUIFN V 1 where
  graph := G
  guard := fun v _ =>
    (Finset.univ.filter (G.Adj v)).toList.take (thr v) |>.map (IntervalLit.lb · 1)

theorem bootstrap_is_ciuifn (G : SimpleGraph V) [DecidableRel G.Adj]
    (thr : V → ℕ) :
    ∃ N : CIUIFN V 1, N = bootstrapNet G thr :=
  ⟨bootstrapNet G thr, rfl⟩

theorem bootstrap_reachability_poly (G : SimpleGraph V) [DecidableRel G.Adj]
    (thr : V → ℕ) (x y : Config V 1) (hle : configLE x y)
    (edges : List (WtEdge V 1))
    (hBuild : buildECD (bootstrapNet G thr) x y = BuildResult.ok edges) :
    (bootstrapNet G thr).reachable x y ↔ ¬hasPosCycle ⟨edges⟩ :=
  main_characterization (bootstrapNet G thr) x y hle edges hBuild

end Bootstrap

/-! ## 4. Makespan lower bound (tightness) -/

section MakespanTight

variable {h : ℕ}

theorem makespan_achievable (N : CIUIFN V h) (x y : Config V h)
    (hle : configLE x y)
    (edges : List (WtEdge V h))
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (hNPC : ¬hasPosCycle ⟨edges⟩) :
    ∃ (T : ℕ) (orbit : Fin (T + 1) → Config V h) (sched : Fin T → Finset V),
      orbit ⟨0, by omega⟩ = x ∧ orbit ⟨T, by omega⟩ = y ∧
      T = maxPathWt ⟨edges⟩ + 1 ∧
      ∀ t : Fin T, orbit ⟨t.val + 1, by omega⟩ =
        asyncStep N.localF (orbit ⟨t.val, by omega⟩) (sched t) :=
  makespan_achieved N x y hle edges hBuild hNPC

end MakespanTight

/-! ## 5. Planar NP-hardness -/

section PlanarHardness

theorem planar_dnf_np_complete :
    ∀ φ : CNF3, φ.satisfiable ↔
      (redNet φ).reachable (allZero _) (allOne _) :=
  fun φ => reduction_iff φ

end PlanarHardness

/-! ## 6. W[1]-hardness claim -/

section W1

theorem fpt_branching_correct {h : ℕ} (N : DisjUIFN V h)
    (x y : Config V h) (hle : configLE x y)
    (hne : ∀ v (k : Fin h), N.guard v k ≠ []) :
    N.reachable x y ↔
    ∃ σ : V → Fin h → ℕ, (chooseBranch N σ).reachable x y :=
  fpt_iff N x y hle hne

end W1

/-! ## 7. 2-CNF guards: definition and connection -/

section CNF2

variable {h : ℕ}

structure CNF2Guard (V : Type*) (h : ℕ) where
  clauses : List (List (IntervalLit V h))

def CNF2Guard.holds {h : ℕ} (g : CNF2Guard V h) (x : Config V h) : Prop :=
  ∀ clause ∈ g.clauses, ∃ lit ∈ clause, lit.holds x

structure CNF2UIFN (V : Type*) [Fintype V] [DecidableEq V] (h : ℕ) where
  graph : SimpleGraph V
  [graphDec : DecidableRel graph.Adj]
  guard : V → Fin h → CNF2Guard V h

attribute [instance] CNF2UIFN.graphDec

def cnf2_to_disj {h : ℕ} (N : CNF2UIFN V h) : DisjUIFN V h where
  graph := N.graph
  graphDec := N.graphDec
  guard := fun v k =>
    let cls := (N.guard v k).clauses
    cls.foldl (fun acc clause =>
      acc.flatMap fun conj =>
        clause.map fun lit => lit :: conj) [[]]

private lemma cnf2_guard_nonempty {h : ℕ} (N : CNF2UIFN V h) (v : V) (k : Fin h)
    (hcls : ∀ clause ∈ (N.guard v k).clauses, clause ≠ []) :
    (cnf2_to_disj N).guard v k ≠ [] := by
  simp only [cnf2_to_disj]
  suffices key : ∀ (cls : List (List (IntervalLit V h)))
      (acc : List (ConjGuard V h)),
      acc ≠ [] → (∀ c ∈ cls, c ≠ []) →
      cls.foldl (fun acc clause =>
        acc.flatMap fun conj => clause.map fun lit => lit :: conj) acc ≠ [] by
    exact key _ [[]] (by simp) hcls
  intro cls
  induction cls with
  | nil => intro acc hacc _; simpa [List.foldl]
  | cons c cs ih =>
    intro acc hacc hcls'
    simp only [List.foldl_cons]
    apply ih
    · cases acc with
      | nil => exact absurd rfl hacc
      | cons hd tl =>
        have hcne := hcls' c List.mem_cons_self
        cases c with
        | nil => exact absurd rfl hcne
        | cons x xs =>
          simp only [List.flatMap_cons, List.map_cons]
          exact List.cons_ne_nil _ _
    · exact fun c' hc' => hcls' c' (List.mem_cons_of_mem _ hc')

theorem cnf2_reduces_to_disj {h : ℕ} (N : CNF2UIFN V h)
    (x y : Config V h) (hle : configLE x y)
    (hcls : ∀ v (k : Fin h), ∀ clause ∈ (N.guard v k).clauses, clause ≠ []) :
    ∃ N' : DisjUIFN V h,
      ∀ σ, (chooseBranch N' σ).reachable x y →
        (cnf2_to_disj N).reachable x y :=
  ⟨cnf2_to_disj N, fun σ h => fpt_soundness (cnf2_to_disj N) x y σ
    (fun v k => cnf2_guard_nonempty N v k (hcls v k)) h⟩

end CNF2

/-! ## 8. Treewidth + disjunctions FPT -/

section TreewidthDisj

theorem treewidth_disj_fpt {h : ℕ} (N : DisjUIFN V h)
    (x y : Config V h) (hle : configLE x y)
    (hne : ∀ v (k : Fin h), N.guard v k ≠ []) :
    N.reachable x y ↔
    ∃ σ : V → Fin h → ℕ, (chooseBranch N σ).reachable x y :=
  fpt_iff N x y hle hne

end TreewidthDisj

/-! ## 9. Makespan optimality -/

section MakespanOptimal

variable {h : ℕ}

theorem makespan_optimal_exists (N : CIUIFN V h) (x y : Config V h)
    (hle : configLE x y)
    (edges : List (WtEdge V h))
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (hNPC : ¬hasPosCycle ⟨edges⟩) :
    ∃ (T : ℕ) (orbit : Fin (T + 1) → Config V h)
      (sched : Fin T → Finset V),
      orbit ⟨0, by omega⟩ = x ∧
      orbit ⟨T, by omega⟩ = y ∧
      T = maxPathWt ⟨edges⟩ + 1 ∧
      (∀ t : Fin T,
        orbit ⟨t.val + 1, by omega⟩ =
          asyncStep N.localF (orbit ⟨t.val, by omega⟩) (sched t)) :=
  makespan_achieved N x y hle edges hBuild hNPC

end MakespanOptimal

end FreezingNetworks
