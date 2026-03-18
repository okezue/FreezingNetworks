import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

namespace FreezingNetworks

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Config (V : Type*) (h : ℕ) := V → Fin (h+1)

def configLE {h : ℕ} (x y : Config V h) : Prop :=
  ∀ v, x v ≤ y v

instance {h : ℕ} (x y : Config V h) : Decidable (configLE x y) :=
  Fintype.decidableForallFintype

def asyncStep {h : ℕ} (F : V → Config V h → Fin (h+1))
    (x : Config V h) (S : Finset V) : Config V h :=
  fun v => if v ∈ S then F v x else x v

def asyncReachable {h : ℕ} (F : V → Config V h → Fin (h+1))
    (x y : Config V h) : Prop :=
  ∃ (T : ℕ) (orbit : Fin (T+1) → Config V h)
    (sched : Fin T → Finset V),
    orbit ⟨0, Nat.zero_lt_succ T⟩ = x ∧
    orbit ⟨T, lt_add_one T⟩ = y ∧
    ∀ (t : Fin T),
      orbit ⟨t.val+1, by omega⟩ =
        asyncStep F (orbit ⟨t.val, by omega⟩) (sched t)

theorem asyncStep_freeze {h : ℕ} {F : V → Config V h → Fin (h+1)}
    (hF : ∀ v x, x v ≤ F v x) (x : Config V h) (S : Finset V) (v : V) :
    x v ≤ asyncStep F x S v := by
  simp only [asyncStep]; split <;> [exact hF v x; exact le_refl _]

inductive IntervalLit (V : Type*) (h : ℕ) where
  | lb (u : V) (a : Fin (h+1)) : IntervalLit V h
  | ub (u : V) (b : Fin (h+1)) : IntervalLit V h
deriving DecidableEq

def IntervalLit.holds {h : ℕ} (lit : IntervalLit V h)
    (x : Config V h) : Prop :=
  match lit with
  | .lb u a => a ≤ x u
  | .ub u b => x u ≤ b

instance {h : ℕ} (lit : IntervalLit V h) (x : Config V h) :
    Decidable (lit.holds x) :=
  match lit with
  | .lb _ _ => inferInstanceAs (Decidable (_ ≤ _))
  | .ub _ _ => inferInstanceAs (Decidable (_ ≤ _))

abbrev ConjGuard (V : Type*) (h : ℕ) := List (IntervalLit V h)

def ConjGuard.holds {h : ℕ} (g : ConjGuard V h) (x : Config V h) : Prop :=
  ∀ lit ∈ g, lit.holds x

instance {h : ℕ} (g : ConjGuard V h) (x : Config V h) :
    Decidable (g.holds x) :=
  List.decidableBAll _ g

structure CIUIFN (V : Type*) [Fintype V] [DecidableEq V] (h : ℕ) where
  graph : SimpleGraph V
  [graphDec : DecidableRel graph.Adj]
  guard : V → Fin h → ConjGuard V h

attribute [instance] CIUIFN.graphDec

def CIUIFN.localF {h : ℕ} (N : CIUIFN V h)
    (v : V) (x : Config V h) : Fin (h+1) :=
  if hlt : (x v).val < h then
    if (N.guard v ⟨(x v).val, hlt⟩).holds x
    then ⟨(x v).val + 1, by omega⟩
    else x v
  else x v

theorem CIUIFN.localF_freezing {h : ℕ} (N : CIUIFN V h)
    (v : V) (x : Config V h) : x v ≤ N.localF v x := by
  simp only [localF]
  split
  · split
    · exact Fin.le_iff_val_le_val.mpr (Nat.le_succ _)
    · exact le_refl _
  · exact le_refl _

theorem CIUIFN.localF_unitIncr {h : ℕ} (N : CIUIFN V h)
    (v : V) (x : Config V h) :
    (N.localF v x).val ≤ (x v).val + 1 := by
  simp only [localF]; split <;> [split <;> simp; omega]

def CIUIFN.reachable {h : ℕ} (N : CIUIFN V h)
    (x y : Config V h) : Prop :=
  asyncReachable N.localF x y

structure IncrEvent (V : Type*) (h : ℕ) where
  v : V
  k : Fin h
deriving DecidableEq

def IncrEvent.needed {h : ℕ} (x y : Config V h) (e : IncrEvent V h) : Prop :=
  (x e.v).val ≤ e.k.val ∧ e.k.val + 1 ≤ (y e.v).val

instance {h : ℕ} (x y : Config V h) (e : IncrEvent V h) :
    Decidable (e.needed x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

structure WtEdge (V : Type*) (h : ℕ) where
  src : IncrEvent V h
  tgt : IncrEvent V h
  wt : ℕ
deriving DecidableEq

structure EventDigraph (V : Type*) [Fintype V] [DecidableEq V] (h : ℕ) where
  edges : List (WtEdge V h)

inductive DWalk {h : ℕ} (edges : List (WtEdge V h)) :
    IncrEvent V h → IncrEvent V h → List (WtEdge V h) → Prop where
  | nil : ∀ e, DWalk edges e e []
  | cons : ∀ {a b c : IncrEvent V h} {w rest},
    (⟨a, b, w⟩ : WtEdge V h) ∈ edges →
    DWalk edges b c rest →
    DWalk edges a c (⟨a, b, w⟩ :: rest)

def pathWt {h : ℕ} : List (WtEdge V h) → ℕ
  | [] => 0
  | e :: es => e.wt + pathWt es

def hasPosCycle {h : ℕ} (G : EventDigraph V h) : Prop :=
  ∃ (e : IncrEvent V h) (path : List (WtEdge V h)),
    DWalk G.edges e e path ∧
    path ≠ [] ∧
    pathWt path ≥ 1

def TimingValid {h : ℕ} (G : EventDigraph V h)
    (τ : IncrEvent V h → ℤ) : Prop :=
  ∀ e ∈ G.edges, τ e.tgt ≥ τ e.src + ↑e.wt

theorem dwalk_timing_sum {h : ℕ} {edges : List (WtEdge V h)}
    {a b : IncrEvent V h} {path : List (WtEdge V h)}
    (τ : IncrEvent V h → ℤ)
    (hτ : ∀ e ∈ edges, τ e.tgt ≥ τ e.src + ↑e.wt)
    (hw : DWalk edges a b path) :
    τ b ≥ τ a + ↑(pathWt path) := by
  induction hw with
  | nil _ => simp [pathWt]
  | @cons a' b' c' w rest hmem _ ih =>
    have h1 := hτ ⟨a', b', w⟩ hmem
    simp at h1; simp only [pathWt]; push_cast; linarith [ih]

theorem noPosCycle_of_validTiming {h : ℕ}
    (G : EventDigraph V h) (τ : IncrEvent V h → ℤ)
    (hτ : TimingValid G τ) : ¬hasPosCycle G := by
  intro ⟨e, path, hwalk, _, hpos⟩
  have := dwalk_timing_sum τ hτ hwalk
  omega

theorem orbit_mono_trans {h : ℕ} {F : V → Config V h → Fin (h+1)}
    (hF : ∀ v x, x v ≤ F v x)
    {T : ℕ} (orbit : Fin (T+1) → Config V h)
    (sched : Fin T → Finset V)
    (hO : ∀ t : Fin T, orbit ⟨t.val+1, by omega⟩ =
      asyncStep F (orbit ⟨t.val, by omega⟩) (sched t))
    (v : V) {i j : ℕ} (hi : i ≤ j) (hj : j ≤ T) :
    orbit ⟨i, by omega⟩ v ≤ orbit ⟨j, by omega⟩ v := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact le_refl _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · exact le_refl _
    · exact le_trans (ih (by omega) (by omega))
        (by rw [hO ⟨k, by omega⟩]; simp only [asyncStep]
            split <;> [exact hF v _; exact le_refl _])

end FreezingNetworks
