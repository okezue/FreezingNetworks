import FreezingNetworks.Defs
import FreezingNetworks.BellmanFord

namespace FreezingNetworks

variable {V : Type*} [Fintype V] [DecidableEq V]

section ECDBuild

variable {h : ℕ}

inductive BuildResult (V : Type*) [Fintype V] [DecidableEq V] (h : ℕ) where
  | impossible
  | ok (edges : List (WtEdge V h))

def processLit (x y : Config V h) (ev : IncrEvent V h)
    (lit : IntervalLit V h) : BuildResult V h :=
  match lit with
  | .lb u a =>
    if (y u).val < a.val then BuildResult.impossible
    else if a.val ≤ (x u).val then BuildResult.ok []
    else
      if ha : a.val ≥ 1 ∧ a.val - 1 < h then
        BuildResult.ok [⟨⟨u, ⟨a.val - 1, ha.2⟩⟩, ev, 1⟩]
      else BuildResult.ok []
  | .ub u b =>
    if (x u).val > b.val then BuildResult.impossible
    else if (y u).val ≤ b.val then BuildResult.ok []
    else
      if hb : b.val < h then
        BuildResult.ok [⟨ev, ⟨u, ⟨b.val, hb⟩⟩, 0⟩]
      else BuildResult.ok []

def processGuard (x y : Config V h) (ev : IncrEvent V h)
    (g : ConjGuard V h) : BuildResult V h :=
  g.foldl (fun (acc : BuildResult V h) lit =>
    match acc with
    | .impossible => .impossible
    | .ok es =>
      match processLit x y ev lit with
      | .impossible => .impossible
      | .ok es' => .ok (es ++ es')) (.ok [])

noncomputable def buildECD (N : CIUIFN V h) (x y : Config V h) :
    BuildResult V h :=
  (Fintype.elems : Finset V).val.toList.foldl (fun (acc : BuildResult V h) v =>
    match acc with
    | .impossible => .impossible
    | .ok edges =>
      let chainEs : List (WtEdge V h) :=
        (List.range h).filterMap fun ki =>
          if hk : ki < h ∧ ki + 1 < h then
            let e1 : IncrEvent V h := ⟨v, ⟨ki, hk.1⟩⟩
            let e2 : IncrEvent V h := ⟨v, ⟨ki + 1, hk.2⟩⟩
            if e1.needed x y ∧ e2.needed x y then
              some ⟨e1, e2, 1⟩
            else none
          else none
      let guardRes : BuildResult V h :=
        (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
          match acc2 with
          | .impossible => .impossible
          | .ok es =>
            if hk : ki < h then
              let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
              if ev.needed x y then
                match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
                | .impossible => .impossible
                | .ok es' => .ok (es ++ es')
              else .ok es
            else .ok es) (.ok [])
      match guardRes with
      | .impossible => .impossible
      | .ok gEs => .ok (edges ++ chainEs ++ gEs)) (.ok [])

end ECDBuild

section EdgeCharacterization

variable {h : ℕ}

inductive ECDEdgeKind (V : Type*) [Fintype V] [DecidableEq V] (h : ℕ)
    (N : CIUIFN V h) (x y : Config V h) : WtEdge V h → Prop where
  | chain (v : V) (ki : ℕ) (hk1 : ki < h) (hk2 : ki + 1 < h)
      (hn1 : IncrEvent.needed x y ⟨v, ⟨ki, hk1⟩⟩)
      (hn2 : IncrEvent.needed x y ⟨v, ⟨ki + 1, hk2⟩⟩) :
      ECDEdgeKind V h N x y ⟨⟨v, ⟨ki, hk1⟩⟩, ⟨v, ⟨ki + 1, hk2⟩⟩, 1⟩
  | lbGuard (v : V) (ki : ℕ) (hk : ki < h) (u : V) (a : Fin (h+1))
      (hn : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩)
      (hlit : IntervalLit.lb u a ∈ N.guard v ⟨ki, hk⟩)
      (hya : ¬(y u).val < a.val) (hxa : ¬a.val ≤ (x u).val)
      (ha : a.val ≥ 1 ∧ a.val - 1 < h) :
      ECDEdgeKind V h N x y ⟨⟨u, ⟨a.val - 1, ha.2⟩⟩, ⟨v, ⟨ki, hk⟩⟩, 1⟩
  | ubGuard (v : V) (ki : ℕ) (hk : ki < h) (u : V) (b : Fin (h+1))
      (hn : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩)
      (hlit : IntervalLit.ub u b ∈ N.guard v ⟨ki, hk⟩)
      (hxb : ¬(x u).val > b.val) (hyb : ¬(y u).val ≤ b.val)
      (hb : b.val < h) :
      ECDEdgeKind V h N x y ⟨⟨v, ⟨ki, hk⟩⟩, ⟨u, ⟨b.val, hb⟩⟩, 0⟩

private lemma processLit_edge {x y : Config V h} {ev : IncrEvent V h}
    {lit : IntervalLit V h} {es : List (WtEdge V h)}
    (hpl : processLit x y ev lit = BuildResult.ok es) {e : WtEdge V h} (he : e ∈ es)
    {N : CIUIFN V h} {v : V} {ki : ℕ} {hk : ki < h}
    (hev : ev = ⟨v, ⟨ki, hk⟩⟩)
    (hne : ev.needed x y) (hlit : lit ∈ N.guard v ⟨ki, hk⟩) :
    ECDEdgeKind V h N x y e := by
  subst hev
  cases lit with
  | lb u a =>
    simp only [processLit] at hpl
    split_ifs at hpl with h1 h2 h3 <;> (try cases hpl) <;>
      (try (simp [List.mem_singleton] at he)) <;> (try contradiction)
    subst he
    exact ECDEdgeKind.lbGuard v ki hk u a hne hlit h1 h2 h3
  | ub u b =>
    simp only [processLit] at hpl
    split_ifs at hpl with h1 h2 h3 <;> (try cases hpl) <;>
      (try (simp [List.mem_singleton] at he)) <;> (try contradiction)
    subst he
    exact ECDEdgeKind.ubGuard v ki hk u b hne hlit h1 h2 h3

private lemma processGuard_mem_sub {x y : Config V h} {ev : IncrEvent V h}
    {g : ConjGuard V h} {es : List (WtEdge V h)}
    (hpg : processGuard x y ev g = BuildResult.ok es) {e : WtEdge V h} (he : e ∈ es) :
    ∃ lit ∈ g, ∃ es', processLit x y ev lit = BuildResult.ok es' ∧ e ∈ es' := by
  simp only [processGuard] at hpg
  suffices key : ∀ (init : List (WtEdge V h)) (g' : ConjGuard V h) (hg' : g' ⊆ g),
      g'.foldl (fun (acc : BuildResult V h) lit =>
        match acc with
        | .impossible => .impossible
        | .ok es =>
          match processLit x y ev lit with
          | .impossible => .impossible
          | .ok es' => .ok (es ++ es')) (.ok init) = .ok es →
      e ∈ init ∨ ∃ lit ∈ g, ∃ es', processLit x y ev lit = .ok es' ∧ e ∈ es' by
    rcases key [] g (List.Subset.refl g) hpg with h1 | h2
    · exact absurd h1 (by simp)
    · exact h2
  intro init g' hg'
  induction g' generalizing init with
  | nil => intro h; simp [List.foldl] at h; cases h; exact Or.inl he
  | cons lit lits ih =>
    intro hfold; simp only [List.foldl_cons] at hfold
    have hlit_in : lit ∈ g := hg' (List.mem_cons.mpr (Or.inl rfl))
    have hlits_sub : lits ⊆ g := fun x hx => hg' (List.mem_cons.mpr (Or.inr hx))
    match hpl : processLit x y ev lit with
    | .impossible =>
      simp [hpl] at hfold
      exfalso
      have : ∀ (l : List (IntervalLit V h)) (r : BuildResult V h),
          r = BuildResult.impossible →
          l.foldl (fun (acc : BuildResult V h) (lit : IntervalLit V h) =>
            match acc with
            | .impossible => .impossible
            | .ok es =>
              match processLit x y ev lit with
              | .impossible => .impossible
              | .ok es' => .ok (es ++ es')) r = BuildResult.impossible := by
        intro l; induction l with
        | nil => intro r hr; simpa
        | cons _ _ ih => intro r hr; simp [List.foldl_cons, hr]; exact ih _ rfl
      rw [this lits _ rfl] at hfold; cases hfold
    | .ok es' =>
      simp [hpl] at hfold
      rcases ih (init ++ es') hlits_sub hfold with h1 | h2
      · rw [List.mem_append] at h1
        rcases h1 with h1l | h1r
        · exact Or.inl h1l
        · exact Or.inr ⟨lit, hlit_in, es', hpl, h1r⟩
      · exact Or.inr h2

private lemma guardRes_mem_sub {N : CIUIFN V h} {x y : Config V h}
    {v : V} {gEs : List (WtEdge V h)}
    (hgr : (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
      match acc2 with
      | .impossible => .impossible
      | .ok es =>
        if hk : ki < h then
          let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
          if ev.needed x y then
            match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
            | .impossible => .impossible
            | .ok es' => .ok (es ++ es')
          else .ok es
        else .ok es) (.ok []) = BuildResult.ok gEs)
    {e : WtEdge V h} (he : e ∈ gEs) :
    ECDEdgeKind V h N x y e := by
  suffices key : ∀ (init : List (WtEdge V h)) (ks : List ℕ),
      ks.foldl (fun (acc2 : BuildResult V h) ki =>
        match acc2 with
        | .impossible => .impossible
        | .ok es =>
          if hk : ki < h then
            let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
            if ev.needed x y then
              match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
              | .impossible => .impossible
              | .ok es' => .ok (es ++ es')
            else .ok es
          else .ok es) (.ok init) = .ok gEs →
      e ∈ init ∨ ECDEdgeKind V h N x y e by
    rcases key [] _ hgr with h1 | h2
    · exact absurd h1 (by simp)
    · exact h2
  intro init ks
  induction ks generalizing init with
  | nil => intro h; simp [List.foldl] at h; cases h; exact Or.inl he
  | cons ki ks ih =>
    intro hfold; simp only [List.foldl_cons] at hfold
    by_cases hk : ki < h
    · by_cases hne : (⟨v, ⟨ki, hk⟩⟩ : IncrEvent V h).needed x y
      · match hpg : processGuard x y ⟨v, ⟨ki, hk⟩⟩ (N.guard v ⟨ki, hk⟩) with
        | .impossible =>
          simp [dif_pos hk, if_pos hne, hpg] at hfold
          exfalso
          have : ∀ (l : List ℕ) (r : BuildResult V h),
              r = BuildResult.impossible →
              l.foldl (fun (acc2 : BuildResult V h) ki =>
                match acc2 with
                | .impossible => .impossible
                | .ok es =>
                  if hk : ki < h then
                    let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
                    if ev.needed x y then
                      match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
                      | .impossible => .impossible
                      | .ok es' => .ok (es ++ es')
                    else .ok es
                  else .ok es) r = BuildResult.impossible := by
            intro l; induction l with
            | nil => intro r hr; simpa
            | cons _ _ ih => intro r hr; simp [List.foldl_cons, hr]; exact ih _ rfl
          rw [this ks _ rfl] at hfold; cases hfold
        | .ok ges =>
          simp [dif_pos hk, if_pos hne, hpg] at hfold
          rcases ih (init ++ ges) hfold with h1 | h2
          · rw [List.mem_append] at h1
            rcases h1 with h1l | h1r
            · exact Or.inl h1l
            · rcases processGuard_mem_sub hpg h1r with ⟨lit, hlit, es', hpl, he'⟩
              exact Or.inr (processLit_edge hpl he' rfl hne hlit)
          · exact Or.inr h2
      · simp [dif_pos hk, if_neg hne] at hfold; exact ih init hfold
    · simp [dif_neg hk] at hfold; exact ih init hfold

private lemma outerFold_mem_sub {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : (Fintype.elems : Finset V).val.toList.foldl (fun (acc : BuildResult V h) v =>
      match acc with
      | .impossible => .impossible
      | .ok edges =>
        let chainEs := (List.range h).filterMap fun ki =>
          if hk : ki < h ∧ ki + 1 < h then
            let e1 : IncrEvent V h := ⟨v, ⟨ki, hk.1⟩⟩
            let e2 : IncrEvent V h := ⟨v, ⟨ki + 1, hk.2⟩⟩
            if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
          else none
        let guardRes := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
          match acc2 with
          | .impossible => .impossible
          | .ok es =>
            if hk : ki < h then
              let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
              if ev.needed x y then
                match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
                | .impossible => .impossible
                | .ok es' => .ok (es ++ es')
              else .ok es
            else .ok es) (.ok [])
        match guardRes with
        | .impossible => .impossible
        | .ok gEs => .ok (edges ++ chainEs ++ gEs)) (.ok []) = BuildResult.ok edges)
    {e : WtEdge V h} (he : e ∈ edges) :
    ECDEdgeKind V h N x y e := by
  set verts := (Fintype.elems : Finset V).val.toList
  suffices h : ∀ (init : List (WtEdge V h)),
      (∀ e ∈ init, ECDEdgeKind V h N x y e) →
      ∀ edges',
        verts.foldl (fun (acc : BuildResult V h) v =>
          match acc with
          | .impossible => .impossible
          | .ok edges =>
            let chainEs := (List.range h).filterMap fun ki =>
              if hk : ki < h ∧ ki + 1 < h then
                let e1 : IncrEvent V h := ⟨v, ⟨ki, hk.1⟩⟩
                let e2 : IncrEvent V h := ⟨v, ⟨ki + 1, hk.2⟩⟩
                if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
              else none
            let guardRes := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
              match acc2 with
              | .impossible => .impossible
              | .ok es =>
                if hk : ki < h then
                  let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
                  if ev.needed x y then
                    match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
                    | .impossible => .impossible
                    | .ok es' => .ok (es ++ es')
                  else .ok es
                else .ok es) (.ok [])
            match guardRes with
            | .impossible => .impossible
            | .ok gEs => .ok (edges ++ chainEs ++ gEs)) (.ok init)
          = BuildResult.ok edges' →
        ∀ e ∈ edges', ECDEdgeKind V h N x y e by
    exact h [] (fun _ h => absurd h (by simp)) edges hBuild e he
  intro init hinit
  induction verts generalizing init with
  | nil => simp [List.foldl]; exact fun _ h => hinit _ h
  | cons v vs ih =>
    intro edges'
    simp only [List.foldl_cons]
    set grv := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
      match acc2 with
      | .impossible => .impossible
      | .ok es =>
        if hk : ki < h then
          let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
          if ev.needed x y then
            match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
            | .impossible => .impossible
            | .ok es' => .ok (es ++ es')
          else .ok es
        else .ok es) (.ok [])
    intro hfold
    match hgr : grv with
    | .impossible =>
      exfalso
      simp only [hgr] at hfold
      have fold_imp : ∀ (l : List V) (r : BuildResult V h),
          r = BuildResult.impossible →
          l.foldl (fun (acc : BuildResult V h) v =>
            match acc with
            | .impossible => .impossible
            | .ok edges =>
              let chainEs := (List.range h).filterMap fun ki =>
                if hk : ki < h ∧ ki + 1 < h then
                  let e1 : IncrEvent V h := ⟨v, ⟨ki, hk.1⟩⟩
                  let e2 : IncrEvent V h := ⟨v, ⟨ki + 1, hk.2⟩⟩
                  if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
                else none
              let guardRes := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
                match acc2 with
                | .impossible => .impossible
                | .ok es =>
                  if hk : ki < h then
                    let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
                    if ev.needed x y then
                      match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
                      | .impossible => .impossible
                      | .ok es' => .ok (es ++ es')
                    else .ok es
                  else .ok es) (.ok [])
              match guardRes with
              | .impossible => .impossible
              | .ok gEs => .ok (edges ++ chainEs ++ gEs)) r = BuildResult.impossible := by
        intro l; induction l with
        | nil => intro r hr; simpa
        | cons _ _ ihfl => intro r hr; simp only [List.foldl_cons, hr]; exact ihfl _ rfl
      rw [fold_imp vs _ rfl] at hfold; cases hfold
    | .ok gEs =>
      simp only [hgr] at hfold
      have hinit' : ∀ e' ∈ init ++ (List.range h).filterMap (fun ki =>
          if hk : ki < h ∧ ki + 1 < h then
            let e1 : IncrEvent V h := ⟨v, ⟨ki, hk.1⟩⟩
            let e2 : IncrEvent V h := ⟨v, ⟨ki + 1, hk.2⟩⟩
            if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
          else none) ++ gEs, ECDEdgeKind V h N x y e' := by
        intro e' he'
        rw [List.mem_append, List.mem_append] at he'
        rcases he' with (h1 | h2) | h3
        · exact hinit e' h1
        · simp only [List.mem_filterMap] at h2
          obtain ⟨ki, _, hki⟩ := h2
          split_ifs at hki with hk hne
          · cases hki with | refl =>
            exact ECDEdgeKind.chain v ki hk.1 hk.2 hne.1 hne.2
          all_goals exact absurd hki (by simp)
        · exact guardRes_mem_sub hgr h3
      exact ih _ hinit' edges' hfold

lemma buildECD_edge_char (N : CIUIFN V h) (x y : Config V h)
    (edges : List (WtEdge V h))
    (hBuild : buildECD N x y = BuildResult.ok edges) :
    ∀ e ∈ edges, ECDEdgeKind V h N x y e := by
  intro e he
  exact outerFold_mem_sub (hBuild) he

end EdgeCharacterization

section OnlyIf

variable {h : ℕ} (N : CIUIFN V h) (x y : Config V h)

theorem orbit_monotone {T : ℕ}
    (orbit : Fin (T + 1) → Config V h)
    (sched : Fin T → Finset V)
    (hOrbit : ∀ (t : Fin T),
      orbit ⟨t.val + 1, by omega⟩ =
        asyncStep N.localF (orbit ⟨t.val, by omega⟩) (sched t))
    (v : V) (t : Fin T) :
    (orbit ⟨t.val, by omega⟩ v) ≤ (orbit ⟨t.val + 1, by omega⟩ v) := by
  rw [hOrbit t]
  exact asyncStep_freeze (CIUIFN.localF_freezing N) _ _ v

private lemma orbit_unitIncr_val {T : ℕ}
    (orbit : Fin (T + 1) → Config V h)
    (sched : Fin T → Finset V)
    (hOrbit : ∀ (t : Fin T),
      orbit ⟨t.val + 1, by omega⟩ =
        asyncStep N.localF (orbit ⟨t.val, by omega⟩) (sched t))
    (v : V) (t : Fin T) :
    (orbit ⟨t.val + 1, by omega⟩ v).val ≤ (orbit ⟨t.val, by omega⟩ v).val + 1 := by
  rw [hOrbit t]; simp only [asyncStep]
  split
  · exact CIUIFN.localF_unitIncr N v _
  · omega

private lemma event_fires_exists {T : ℕ}
    (orbit : Fin (T + 1) → Config V h)
    (sched : Fin T → Finset V)
    (hOrbit : ∀ (t : Fin T),
      orbit ⟨t.val + 1, by omega⟩ =
        asyncStep N.localF (orbit ⟨t.val, by omega⟩) (sched t))
    (hx : orbit ⟨0, by omega⟩ = x)
    (hy : orbit ⟨T, by omega⟩ = y)
    (e : IncrEvent V h) (hne : e.needed x y) :
    ∃ t : Fin T,
      (orbit ⟨t.val, by omega⟩ e.v).val ≤ e.k.val ∧
      (orbit ⟨t.val + 1, by omega⟩ e.v).val > e.k.val := by
  have hx_le : (x e.v).val ≤ e.k.val := hne.1
  have hy_gt : e.k.val + 1 ≤ (y e.v).val := hne.2
  have h0_le : (orbit ⟨0, by omega⟩ e.v).val ≤ e.k.val := by rw [hx]; exact hx_le
  have hT_gt : (orbit ⟨T, by omega⟩ e.v).val > e.k.val := by rw [hy]; omega
  have hT_pos : T > 0 := by
    by_contra h0; push_neg at h0
    have hT0 : T = 0 := Nat.le_zero.mp h0
    subst hT0; omega
  have key : ∀ n : ℕ, (hn : n ≤ T) →
      (orbit ⟨n, by omega⟩ e.v).val > e.k.val →
      ∃ t : Fin T, (orbit ⟨t.val, by omega⟩ e.v).val ≤ e.k.val ∧
        (orbit ⟨t.val + 1, by omega⟩ e.v).val > e.k.val := by
    intro n hn hgt
    induction n with
    | zero => omega
    | succ k ih =>
      by_cases hk_le : (orbit ⟨k, by omega⟩ e.v).val ≤ e.k.val
      · exact ⟨⟨k, by omega⟩, hk_le, hgt⟩
      · push_neg at hk_le
        exact ih (by omega) hk_le
  exact key T (le_refl T) hT_gt

noncomputable def eventTime {T : ℕ}
    (orbit : Fin (T + 1) → Config V h)
    (e : IncrEvent V h) : ℤ :=
  if h_ex : ∃ t : Fin T, (orbit ⟨t.val, by omega⟩ e.v).val ≤ e.k.val ∧
      (orbit ⟨t.val + 1, by omega⟩ e.v).val > e.k.val then
    let S := Finset.univ.filter (fun t : Fin T =>
      (orbit ⟨t.val, by omega⟩ e.v).val ≤ e.k.val ∧
      (orbit ⟨t.val + 1, by omega⟩ e.v).val > e.k.val)
    let hne : S.Nonempty := ⟨h_ex.choose, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, h_ex.choose_spec⟩⟩
    ↑(S.min' hne).val + 1
  else 0

private lemma eventTime_eq {T : ℕ}
    (orbit : Fin (T + 1) → Config V h)
    (e : IncrEvent V h)
    (t : Fin T)
    (ht_le : (orbit ⟨t.val, by omega⟩ e.v).val ≤ e.k.val)
    (ht_gt : (orbit ⟨t.val + 1, by omega⟩ e.v).val > e.k.val) :
    ∃ tmin : Fin T,
      eventTime orbit e = ↑tmin.val + 1 ∧
      (orbit ⟨tmin.val, by omega⟩ e.v).val ≤ e.k.val ∧
      (orbit ⟨tmin.val + 1, by omega⟩ e.v).val > e.k.val ∧
      tmin.val ≤ t.val := by
  have h_ex : ∃ t : Fin T, (orbit ⟨t.val, by omega⟩ e.v).val ≤ e.k.val ∧
      (orbit ⟨t.val + 1, by omega⟩ e.v).val > e.k.val := ⟨t, ht_le, ht_gt⟩
  simp only [eventTime, dif_pos h_ex]
  set S := Finset.univ.filter (fun t : Fin T =>
    (orbit ⟨t.val, by omega⟩ e.v).val ≤ e.k.val ∧
    (orbit ⟨t.val + 1, by omega⟩ e.v).val > e.k.val)
  have hne : S.Nonempty := ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨ht_le, ht_gt⟩⟩⟩
  set tmin := S.min' hne
  have htmin_mem := Finset.min'_mem S hne
  rw [Finset.mem_filter] at htmin_mem
  have htmin_le := Finset.min'_le S t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨ht_le, ht_gt⟩⟩)
  exact ⟨tmin, rfl, htmin_mem.2.1, htmin_mem.2.2, Fin.val_le_of_le htmin_le⟩

private lemma guard_holds_at_fire {T : ℕ}
    (orbit : Fin (T + 1) → Config V h)
    (sched : Fin T → Finset V)
    (hOrbit : ∀ (t : Fin T),
      orbit ⟨t.val + 1, by omega⟩ =
        asyncStep N.localF (orbit ⟨t.val, by omega⟩) (sched t))
    (v : V) (ki : ℕ) (hk : ki < h)
    (t : Fin T)
    (ht_le : (orbit ⟨t.val, by omega⟩ v).val ≤ ki)
    (ht_gt : (orbit ⟨t.val + 1, by omega⟩ v).val > ki) :
    (N.guard v ⟨ki, hk⟩).holds (orbit ⟨t.val, by omega⟩) := by
  have hval : (orbit ⟨t.val, by omega⟩ v).val = ki := by
    have h_unit := orbit_unitIncr_val N orbit sched hOrbit v t
    omega
  have hstep := congr_fun (hOrbit t) v
  simp only [asyncStep] at hstep
  split_ifs at hstep with hmem
  · simp only [CIUIFN.localF] at hstep
    split_ifs at hstep with hlt hg
    · have hfk : (⟨(orbit ⟨t.val, by omega⟩ v).val, hlt⟩ : Fin h) = ⟨ki, hk⟩ := by
        ext; exact hval
      rw [hfk] at hg; exact hg
    · exfalso
      have heq : (orbit ⟨t.val + 1, by omega⟩ v) = (orbit ⟨t.val, by omega⟩ v) := by
        exact hstep
      have := congr_arg Fin.val heq
      simp at this; omega
    · exfalso; rw [hval] at hlt; exact hlt hk
  · exfalso
    have heq : (orbit ⟨t.val + 1, by omega⟩ v) = (orbit ⟨t.val, by omega⟩ v) := by
      have := congr_fun (hOrbit t) v
      simp [asyncStep, hmem] at this; exact this
    have := congr_arg Fin.val heq
    simp at this; omega

theorem orbit_timing_valid
    {T : ℕ} (orbit : Fin (T + 1) → Config V h)
    (sched : Fin T → Finset V)
    (hx : orbit ⟨0, by omega⟩ = x)
    (hy : orbit ⟨T, by omega⟩ = y)
    (hOrbit : ∀ (t : Fin T),
      orbit ⟨t.val + 1, by omega⟩ =
        asyncStep N.localF (orbit ⟨t.val, by omega⟩) (sched t))
    (edges : List (WtEdge V h))
    (hBuild : buildECD N x y = BuildResult.ok edges) :
    ∃ τ : IncrEvent V h → ℤ, TimingValid ⟨edges⟩ τ := by
  refine ⟨eventTime orbit, ?_⟩
  intro e he
  have hchar := buildECD_edge_char N x y edges hBuild e he
  have hmono := orbit_mono_trans (CIUIFN.localF_freezing N) orbit sched hOrbit
  cases hchar with
  | chain v ki hk1 hk2 hn1 hn2 =>
    have ⟨t1, ht1_le, ht1_gt⟩ := event_fires_exists N x y orbit sched hOrbit hx hy
      ⟨v, ⟨ki, hk1⟩⟩ hn1
    have ⟨t2, ht2_le, ht2_gt⟩ := event_fires_exists N x y orbit sched hOrbit hx hy
      ⟨v, ⟨ki + 1, hk2⟩⟩ hn2
    obtain ⟨tm1, htm1_eq, htm1_le, htm1_gt, _⟩ :=
      eventTime_eq orbit ⟨v, ⟨ki, hk1⟩⟩ t1 ht1_le ht1_gt
    obtain ⟨tm2, htm2_eq, htm2_le, htm2_gt, _⟩ :=
      eventTime_eq orbit ⟨v, ⟨ki + 1, hk2⟩⟩ t2 ht2_le ht2_gt
    simp only [EventDigraph.mk] at *
    rw [htm1_eq, htm2_eq]; push_cast
    suffices tm1.val < tm2.val by linarith
    by_contra hle; push_neg at hle
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · have hval1 : (orbit ⟨tm1.val, by omega⟩ v).val = ki := by
        have := orbit_unitIncr_val N orbit sched hOrbit v tm1; omega
      have hval2 : (orbit ⟨tm2.val, by omega⟩ v).val = ki + 1 := by
        have := orbit_unitIncr_val N orbit sched hOrbit v tm2; omega
      have h_m := Fin.val_le_of_le (hmono v (show tm2.val ≤ tm1.val from hle)
        (show tm1.val ≤ T by omega))
      omega
    · have h_m := Fin.val_le_of_le (hmono v (show tm2.val + 1 ≤ tm1.val by omega)
        (show tm1.val ≤ T by omega))
      omega
  | lbGuard v ki hk u a hn hlit hya hxa ha =>
    have hne_ev : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩ := hn
    have hne_u : IncrEvent.needed x y ⟨u, ⟨a.val - 1, ha.2⟩⟩ := by
      simp only [IncrEvent.needed, IncrEvent.v, IncrEvent.k, Fin.val_mk]
      push_neg at hxa hya
      constructor <;> omega
    have ⟨tv, htv_le, htv_gt⟩ := event_fires_exists N x y orbit sched hOrbit hx hy
      ⟨v, ⟨ki, hk⟩⟩ hne_ev
    have ⟨tu, htu_le, htu_gt⟩ := event_fires_exists N x y orbit sched hOrbit hx hy
      ⟨u, ⟨a.val - 1, ha.2⟩⟩ hne_u
    obtain ⟨tmv, htmv_eq, htmv_le, htmv_gt, _⟩ :=
      eventTime_eq orbit ⟨v, ⟨ki, hk⟩⟩ tv htv_le htv_gt
    obtain ⟨tmu, htmu_eq, htmu_le, htmu_gt, _⟩ :=
      eventTime_eq orbit ⟨u, ⟨a.val - 1, ha.2⟩⟩ tu htu_le htu_gt
    simp only [EventDigraph.mk, IncrEvent.v, IncrEvent.k, Fin.val_mk] at *
    rw [htmv_eq, htmu_eq]; push_cast
    suffices h_lt : tmu.val < tmv.val by linarith
    by_contra hle; push_neg at hle
    have hguard := guard_holds_at_fire N orbit sched hOrbit v ki hk tmv htmv_le htmv_gt
    have hlit_holds := hguard (IntervalLit.lb u a) hlit
    simp only [IntervalLit.holds] at hlit_holds
    have hu_ge_a : a.val ≤ (orbit ⟨tmv.val, by omega⟩ u).val :=
      Fin.val_le_of_le hlit_holds
    have h_m := Fin.val_le_of_le (hmono u (show tmv.val ≤ tmu.val from hle)
      (show tmu.val ≤ T by omega))
    omega
  | ubGuard v ki hk u b hn hlit hxb hyb hb =>
    have hne_ev : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩ := hn
    have hne_u : IncrEvent.needed x y ⟨u, ⟨b.val, hb⟩⟩ := by
      simp only [IncrEvent.needed, IncrEvent.v, IncrEvent.k, Fin.val_mk]
      push_neg at hxb hyb
      constructor <;> omega
    have ⟨tv, htv_le, htv_gt⟩ := event_fires_exists N x y orbit sched hOrbit hx hy
      ⟨v, ⟨ki, hk⟩⟩ hne_ev
    have ⟨tu, htu_le, htu_gt⟩ := event_fires_exists N x y orbit sched hOrbit hx hy
      ⟨u, ⟨b.val, hb⟩⟩ hne_u
    obtain ⟨tmv, htmv_eq, htmv_le, htmv_gt, _⟩ :=
      eventTime_eq orbit ⟨v, ⟨ki, hk⟩⟩ tv htv_le htv_gt
    obtain ⟨tmu, htmu_eq, htmu_le, htmu_gt, _⟩ :=
      eventTime_eq orbit ⟨u, ⟨b.val, hb⟩⟩ tu htu_le htu_gt
    simp only [EventDigraph.mk, IncrEvent.v, IncrEvent.k, Fin.val_mk] at *
    rw [htmv_eq, htmu_eq]; push_cast
    suffices h_le : tmv.val ≤ tmu.val by linarith
    by_contra hgt; push_neg at hgt
    have hguard := guard_holds_at_fire N orbit sched hOrbit v ki hk tmv htmv_le htmv_gt
    have hlit_holds := hguard (IntervalLit.ub u b) hlit
    simp only [IntervalLit.holds] at hlit_holds
    have hu_le_b : (orbit ⟨tmv.val, by omega⟩ u).val ≤ b.val :=
      Fin.val_le_of_le hlit_holds
    have h_m := Fin.val_le_of_le (hmono u (show tmu.val + 1 ≤ tmv.val by omega)
        (show tmv.val ≤ T by omega))
    omega

theorem onlyIf_direction
    (hReach : N.reachable x y)
    (edges : List (WtEdge V h))
    (hBuild : buildECD N x y = BuildResult.ok edges) :
    ¬hasPosCycle ⟨edges⟩ := by
  obtain ⟨T, orbit, sched, hx, hy, hOrbit⟩ := hReach
  obtain ⟨τ, hτ⟩ := orbit_timing_valid N x y orbit sched hx hy hOrbit edges hBuild
  exact noPosCycle_of_validTiming ⟨edges⟩ τ hτ

end OnlyIf

section IfDir

variable {h : ℕ} (N : CIUIFN V h) (x y : Config V h)

theorem validTiming_of_noPosCycle_local
    (G : EventDigraph V h) (hG : ¬hasPosCycle G) :
    ∃ τ : IncrEvent V h → ℤ, TimingValid G τ ∧ ∀ e, τ e ≥ 1 :=
  FreezingNetworks.validTiming_of_noPosCycle G hG

private noncomputable def tMax (τ : IncrEvent V h → ℤ) : ℕ :=
  (Finset.univ.image (fun e : IncrEvent V h => (τ e).toNat)).sup id

private noncomputable def mkSched {h : ℕ} (N : CIUIFN V h)
    (x y : Config V h) (τ : IncrEvent V h → ℤ) (t : ℕ) : Finset V :=
  Finset.univ.filter fun v =>
    ∃ k : Fin h, (⟨v,k⟩ : IncrEvent V h).needed x y ∧ τ ⟨v,k⟩ = ↑(t+1)

instance {h : ℕ} {x y : Config V h} {τ : IncrEvent V h → ℤ} {v : V} {t : ℕ} :
    Decidable (∃ k : Fin h, (⟨v,k⟩ : IncrEvent V h).needed x y ∧ τ ⟨v,k⟩ = ↑(t+1)) :=
  Fintype.decidableExistsFintype

private noncomputable def mkOrbit {h : ℕ} (N : CIUIFN V h)
    (x y : Config V h) (τ : IncrEvent V h → ℤ) :
    (n : ℕ) → Config V h
  | 0 => x
  | n+1 => asyncStep N.localF (mkOrbit N x y τ n) (mkSched N x y τ n)

private lemma mkOrbit_zero {h : ℕ} (N : CIUIFN V h)
    (x y : Config V h) (τ : IncrEvent V h → ℤ) :
    mkOrbit N x y τ 0 = x := rfl

private lemma mkOrbit_succ {h : ℕ} (N : CIUIFN V h)
    (x y : Config V h) (τ : IncrEvent V h → ℤ) (n : ℕ) :
    mkOrbit N x y τ (n+1) = asyncStep N.localF (mkOrbit N x y τ n) (mkSched N x y τ n) := rfl

private lemma mkOrbit_mono {h : ℕ} (N : CIUIFN V h)
    (x y : Config V h) (τ : IncrEvent V h → ℤ) (v : V) (n : ℕ) :
    mkOrbit N x y τ n v ≤ mkOrbit N x y τ (n+1) v := by
  rw [mkOrbit_succ]; exact asyncStep_freeze (CIUIFN.localF_freezing N) _ _ v

private lemma mkOrbit_mono_trans {h : ℕ} (N : CIUIFN V h)
    (x y : Config V h) (τ : IncrEvent V h → ℤ) (v : V) {i j : ℕ} (hij : i ≤ j) :
    mkOrbit N x y τ i v ≤ mkOrbit N x y τ j v := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst hi; exact le_refl _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact le_refl _
    · exact le_trans (ih (by omega)) (mkOrbit_mono N x y τ v k)

private lemma τ_le_tMax (τ : IncrEvent V h → ℤ) (hPos : ∀ e, τ e ≥ 1)
    (e : IncrEvent V h) : (τ e).toNat ≤ tMax τ := by
  simp only [tMax]
  exact Finset.le_sup (f := id) (Finset.mem_image_of_mem _ (Finset.mem_univ e))

private lemma tMax_pos (τ : IncrEvent V h → ℤ) (hPos : ∀ e, τ e ≥ 1)
    [Nonempty V] [hn : Fact (h > 0)] : tMax τ ≥ 1 := by
  have hv := Classical.arbitrary V
  have hk : (0 : ℕ) < h := hn.out
  have he : IncrEvent V h := ⟨hv, ⟨0, hk⟩⟩
  have h1 := τ_le_tMax τ hPos he
  have h2 : (τ he).toNat ≥ 1 := by
    have := hPos he; omega
  omega

private lemma chain_edge_mem {h : ℕ} {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (v : V) (ki : ℕ) (hk1 : ki < h) (hk2 : ki + 1 < h)
    (hn1 : IncrEvent.needed x y ⟨v, ⟨ki, hk1⟩⟩)
    (hn2 : IncrEvent.needed x y ⟨v, ⟨ki + 1, hk2⟩⟩) :
    (⟨⟨v, ⟨ki, hk1⟩⟩, ⟨v, ⟨ki + 1, hk2⟩⟩, 1⟩ : WtEdge V h) ∈ edges := by
  simp only [buildECD] at hBuild
  set e := (⟨⟨v, ⟨ki, hk1⟩⟩, ⟨v, ⟨ki + 1, hk2⟩⟩, 1⟩ : WtEdge V h)
  have fold_imp_propagate : ∀ (l : List V) (r : BuildResult V h),
      r = BuildResult.impossible →
      l.foldl (fun (acc : BuildResult V h) v =>
        match acc with
        | .impossible => .impossible
        | .ok edges =>
          let chainEs := (List.range h).filterMap fun ki =>
            if hk : ki < h ∧ ki + 1 < h then
              let e1 : IncrEvent V h := ⟨v, ⟨ki, hk.1⟩⟩
              let e2 : IncrEvent V h := ⟨v, ⟨ki + 1, hk.2⟩⟩
              if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
            else none
          let guardRes := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
            match acc2 with
            | .impossible => .impossible
            | .ok es =>
              if hk : ki < h then
                let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
                if ev.needed x y then
                  match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
                  | .impossible => .impossible
                  | .ok es' => .ok (es ++ es')
                else .ok es
              else .ok es) (.ok [])
          match guardRes with
          | .impossible => .impossible
          | .ok gEs => .ok (edges ++ chainEs ++ gEs)) r = BuildResult.impossible := by
    intro l; induction l with
    | nil => intro r hr; simpa
    | cons _ _ ihfl => intro r hr; simp only [List.foldl_cons, hr]; exact ihfl _ rfl
  suffices fold_preserves : ∀ (verts : List V) (init result : List (WtEdge V h)),
      verts.foldl (fun (acc : BuildResult V h) v =>
        match acc with
        | .impossible => .impossible
        | .ok edges =>
          let chainEs := (List.range h).filterMap fun ki =>
            if hk : ki < h ∧ ki + 1 < h then
              let e1 : IncrEvent V h := ⟨v, ⟨ki, hk.1⟩⟩
              let e2 : IncrEvent V h := ⟨v, ⟨ki + 1, hk.2⟩⟩
              if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
            else none
          let guardRes := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
            match acc2 with
            | .impossible => .impossible
            | .ok es =>
              if hk : ki < h then
                let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
                if ev.needed x y then
                  match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
                  | .impossible => .impossible
                  | .ok es' => .ok (es ++ es')
                else .ok es
              else .ok es) (.ok [])
          match guardRes with
          | .impossible => .impossible
          | .ok gEs => .ok (edges ++ chainEs ++ gEs)) (.ok init) = .ok result →
      e ∈ init → e ∈ result by
    have he_chain : e ∈ (List.range h).filterMap fun ki' =>
        if hk : ki' < h ∧ ki' + 1 < h then
          let e1 : IncrEvent V h := ⟨v, ⟨ki', hk.1⟩⟩
          let e2 : IncrEvent V h := ⟨v, ⟨ki' + 1, hk.2⟩⟩
          if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
        else none := by
      rw [List.mem_filterMap]
      refine ⟨ki, List.mem_range.mpr hk1, ?_⟩
      simp only [e, dif_pos (And.intro hk1 hk2), if_pos (And.intro hn1 hn2)]
    suffices h2 : ∀ (verts : List V) (init result : List (WtEdge V h)),
        v ∈ verts →
        verts.foldl (fun (acc : BuildResult V h) v =>
          match acc with
          | .impossible => .impossible
          | .ok edges =>
            let chainEs := (List.range h).filterMap fun ki =>
              if hk : ki < h ∧ ki + 1 < h then
                let e1 : IncrEvent V h := ⟨v, ⟨ki, hk.1⟩⟩
                let e2 : IncrEvent V h := ⟨v, ⟨ki + 1, hk.2⟩⟩
                if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
              else none
            let guardRes := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
              match acc2 with
              | .impossible => .impossible
              | .ok es =>
                if hk : ki < h then
                  let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
                  if ev.needed x y then
                    match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
                    | .impossible => .impossible
                    | .ok es' => .ok (es ++ es')
                  else .ok es
                else .ok es) (.ok [])
            match guardRes with
            | .impossible => .impossible
            | .ok gEs => .ok (edges ++ chainEs ++ gEs)) (.ok init) = .ok result →
        e ∈ result by
      exact h2 _ [] edges (Finset.mem_toList.mpr (Fintype.complete v)) hBuild
    intro verts
    induction verts with
    | nil => intro _ _ hv; exact absurd hv (by simp)
    | cons w ws ih =>
      intro init result hv hfold
      simp only [List.foldl_cons] at hfold
      rcases List.mem_cons.mp hv with rfl | hv'
      · set grv := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
            match acc2 with
            | .impossible => .impossible
            | .ok es =>
              if hk : ki < h then
                let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
                if ev.needed x y then
                  match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
                  | .impossible => .impossible
                  | .ok es' => .ok (es ++ es')
                else .ok es
              else .ok es) (.ok [])
        match hgr : grv with
        | .impossible =>
          simp only [hgr] at hfold
          rw [fold_imp_propagate ws _ rfl] at hfold; cases hfold
        | .ok gEs =>
          simp only [hgr] at hfold
          exact fold_preserves ws _ _ hfold
            (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr he_chain))))
      · set grv := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
            match acc2 with
            | .impossible => .impossible
            | .ok es =>
              if hk : ki < h then
                let ev : IncrEvent V h := ⟨w, ⟨ki, hk⟩⟩
                if ev.needed x y then
                  match processGuard x y ev (N.guard w ⟨ki, hk⟩) with
                  | .impossible => .impossible
                  | .ok es' => .ok (es ++ es')
                else .ok es
              else .ok es) (.ok [])
        match hgr : grv with
        | .impossible =>
          simp only [hgr] at hfold
          rw [fold_imp_propagate ws _ rfl] at hfold; cases hfold
        | .ok gEs =>
          simp only [hgr] at hfold
          exact ih _ result hv' hfold
  intro verts
  induction verts with
  | nil => intro init result hfold he; simp [List.foldl] at hfold; cases hfold; exact he
  | cons w ws ih =>
    intro init result hfold he
    simp only [List.foldl_cons] at hfold
    set grv := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
      match acc2 with
      | .impossible => .impossible
      | .ok es =>
        if hk : ki < h then
          let ev : IncrEvent V h := ⟨w, ⟨ki, hk⟩⟩
          if ev.needed x y then
            match processGuard x y ev (N.guard w ⟨ki, hk⟩) with
            | .impossible => .impossible
            | .ok es' => .ok (es ++ es')
          else .ok es
        else .ok es) (.ok [])
    match hgr : grv with
    | .impossible =>
      simp only [hgr] at hfold
      rw [fold_imp_propagate ws _ rfl] at hfold; cases hfold
    | .ok gEs =>
      simp only [hgr] at hfold
      exact ih _ _ hfold
        (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl he))))

private lemma lb_edge_mem {h : ℕ} {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (v : V) (ki : ℕ) (hk : ki < h) (u : V) (a : Fin (h+1))
    (hn : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩)
    (hlit : IntervalLit.lb u a ∈ N.guard v ⟨ki, hk⟩)
    (hya : ¬(y u).val < a.val) (hxa : ¬a.val ≤ (x u).val)
    (ha : a.val ≥ 1 ∧ a.val - 1 < h) :
    (⟨⟨u, ⟨a.val - 1, ha.2⟩⟩, ⟨v, ⟨ki, hk⟩⟩, 1⟩ : WtEdge V h) ∈ edges := by
  set e := (⟨⟨u, ⟨a.val - 1, ha.2⟩⟩, ⟨v, ⟨ki, hk⟩⟩, 1⟩ : WtEdge V h)
  have hprocLit : processLit x y ⟨v, ⟨ki, hk⟩⟩ (IntervalLit.lb u a) =
      BuildResult.ok [e] := by
    simp only [processLit, if_neg hya, if_neg hxa, dif_pos ha, e]
  have lit_fold_imp : ∀ (l : List (IntervalLit V h)) (r : BuildResult V h),
      r = BuildResult.impossible →
      l.foldl (fun (acc : BuildResult V h) (lit : IntervalLit V h) =>
        match acc with
        | .impossible => .impossible
        | .ok es =>
          match processLit x y ⟨v, ⟨ki, hk⟩⟩ lit with
          | .impossible => .impossible
          | .ok es' => .ok (es ++ es')) r = BuildResult.impossible := by
    intro l; induction l with
    | nil => intro r hr; simpa
    | cons _ _ ih3 => intro r hr; simp [List.foldl_cons, hr]; exact ih3 _ rfl
  have lit_fold_preserves : ∀ (l : ConjGuard V h) (init2 result2 : List (WtEdge V h)),
      e ∈ init2 →
      l.foldl (fun (acc : BuildResult V h) lit =>
        match acc with
        | .impossible => .impossible
        | .ok es =>
          match processLit x y ⟨v, ⟨ki, hk⟩⟩ lit with
          | .impossible => .impossible
          | .ok es' => .ok (es ++ es')) (.ok init2) = .ok result2 →
      e ∈ result2 := by
    intro l
    induction l with
    | nil => intro init2 result2 he2 hf2; simp [List.foldl] at hf2; cases hf2; exact he2
    | cons l2 ls2 ih2 =>
      intro init2 result2 he2 hf2; simp only [List.foldl_cons] at hf2
      match hpl2 : processLit x y ⟨v, ⟨ki, hk⟩⟩ l2 with
      | .impossible =>
        simp [hpl2] at hf2; rw [lit_fold_imp ls2 _ rfl] at hf2; cases hf2
      | .ok es2 =>
        simp [hpl2] at hf2
        exact ih2 _ result2 (List.mem_append.mpr (Or.inl he2)) hf2
  have he_in_guard_result : ∀ (ges : List (WtEdge V h)),
      processGuard x y ⟨v, ⟨ki, hk⟩⟩ (N.guard v ⟨ki, hk⟩) = .ok ges → e ∈ ges := by
    simp only [processGuard]
    intro ges hpg
    suffices key : ∀ (g' : ConjGuard V h) (init : List (WtEdge V h)),
        (IntervalLit.lb u a) ∈ g' →
        g'.foldl (fun (acc : BuildResult V h) lit =>
          match acc with
          | .impossible => .impossible
          | .ok es =>
            match processLit x y ⟨v, ⟨ki, hk⟩⟩ lit with
            | .impossible => .impossible
            | .ok es' => .ok (es ++ es')) (.ok init) = .ok ges →
        e ∈ ges by
      exact key _ [] hlit hpg
    intro g'
    induction g' with
    | nil => intro _ hmem; exact absurd hmem (by simp)
    | cons lit' lits' ih =>
      intro init hmem hfold
      simp only [List.foldl_cons] at hfold
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · rw [hprocLit] at hfold
        exact lit_fold_preserves lits' _ ges
          (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))) hfold
      · match hpl2 : processLit x y ⟨v, ⟨ki, hk⟩⟩ lit' with
        | .impossible =>
          simp [hpl2] at hfold; rw [lit_fold_imp lits' _ rfl] at hfold; cases hfold
        | .ok es2 =>
          simp [hpl2] at hfold; exact ih (init ++ es2) hmem' hfold
  simp only [buildECD] at hBuild
  have fold_imp_propagate : ∀ (l : List V) (r : BuildResult V h),
      r = BuildResult.impossible →
      l.foldl (fun (acc : BuildResult V h) v =>
        match acc with
        | .impossible => .impossible
        | .ok edges =>
          let chainEs := (List.range h).filterMap fun ki =>
            if hk : ki < h ∧ ki + 1 < h then
              let e1 : IncrEvent V h := ⟨v, ⟨ki, hk.1⟩⟩
              let e2 : IncrEvent V h := ⟨v, ⟨ki + 1, hk.2⟩⟩
              if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
            else none
          let guardRes := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
            match acc2 with
            | .impossible => .impossible
            | .ok es =>
              if hk : ki < h then
                let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
                if ev.needed x y then
                  match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
                  | .impossible => .impossible
                  | .ok es' => .ok (es ++ es')
                else .ok es
              else .ok es) (.ok [])
          match guardRes with
          | .impossible => .impossible
          | .ok gEs => .ok (edges ++ chainEs ++ gEs)) r = BuildResult.impossible := by
    intro l; induction l with
    | nil => intro r hr; simpa
    | cons _ _ ihfl => intro r hr; simp only [List.foldl_cons, hr]; exact ihfl _ rfl
  suffices fold_preserves : ∀ (verts : List V) (init result : List (WtEdge V h)),
      verts.foldl (fun (acc : BuildResult V h) v =>
        match acc with
        | .impossible => .impossible
        | .ok edges =>
          let chainEs := (List.range h).filterMap fun ki =>
            if hk : ki < h ∧ ki + 1 < h then
              let e1 : IncrEvent V h := ⟨v, ⟨ki, hk.1⟩⟩
              let e2 : IncrEvent V h := ⟨v, ⟨ki + 1, hk.2⟩⟩
              if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
            else none
          let guardRes := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
            match acc2 with
            | .impossible => .impossible
            | .ok es =>
              if hk : ki < h then
                let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
                if ev.needed x y then
                  match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
                  | .impossible => .impossible
                  | .ok es' => .ok (es ++ es')
                else .ok es
              else .ok es) (.ok [])
          match guardRes with
          | .impossible => .impossible
          | .ok gEs => .ok (edges ++ chainEs ++ gEs)) (.ok init) = .ok result →
      e ∈ init → e ∈ result by
    have guard_fold_preserves : ∀ (ks : List ℕ) (init2 result2 : List (WtEdge V h)),
        ks.foldl (fun (acc2 : BuildResult V h) ki =>
          match acc2 with
          | .impossible => .impossible
          | .ok es =>
            if hk2 : ki < h then
              let ev : IncrEvent V h := ⟨v, ⟨ki, hk2⟩⟩
              if ev.needed x y then
                match processGuard x y ev (N.guard v ⟨ki, hk2⟩) with
                | .impossible => .impossible
                | .ok es' => .ok (es ++ es')
              else .ok es
            else .ok es) (.ok init2) = .ok result2 →
        e ∈ init2 → e ∈ result2 := by
      intro ks
      induction ks with
      | nil => intro init2 result2 hf he2; simp [List.foldl] at hf; cases hf; exact he2
      | cons kj ks2 ih2 =>
        intro init2 result2 hf he2; simp only [List.foldl_cons] at hf
        by_cases hkj : kj < h
        · by_cases hnej : (⟨v, ⟨kj, hkj⟩⟩ : IncrEvent V h).needed x y
          · match hpgj : processGuard x y ⟨v, ⟨kj, hkj⟩⟩ (N.guard v ⟨kj, hkj⟩) with
            | .impossible =>
              simp [dif_pos hkj, if_pos hnej, hpgj] at hf
              have : ∀ (l : List ℕ) (r : BuildResult V h),
                  r = BuildResult.impossible →
                  l.foldl (fun (acc2 : BuildResult V h) ki =>
                    match acc2 with
                    | .impossible => .impossible
                    | .ok es =>
                      if hk2 : ki < h then
                        let ev : IncrEvent V h := ⟨v, ⟨ki, hk2⟩⟩
                        if ev.needed x y then
                          match processGuard x y ev (N.guard v ⟨ki, hk2⟩) with
                          | .impossible => .impossible
                          | .ok es' => .ok (es ++ es')
                        else .ok es
                      else .ok es) r = BuildResult.impossible := by
                intro l; induction l with
                | nil => intro r hr; simpa
                | cons _ _ ih3 => intro r hr; simp [List.foldl_cons, hr]; exact ih3 _ rfl
              rw [this ks2 _ rfl] at hf; cases hf
            | .ok gesj =>
              simp [dif_pos hkj, if_pos hnej, hpgj] at hf
              exact ih2 _ result2 hf (List.mem_append.mpr (Or.inl he2))
          · simp [dif_pos hkj, if_neg hnej] at hf; exact ih2 _ result2 hf he2
        · simp [dif_neg hkj] at hf; exact ih2 _ result2 hf he2
    have he_in_gEs : ∀ (ks : List ℕ) (init2 result2 : List (WtEdge V h)),
        ki ∈ ks →
        ks.foldl (fun (acc2 : BuildResult V h) kj =>
          match acc2 with
          | .impossible => .impossible
          | .ok es =>
            if hk2 : kj < h then
              let ev : IncrEvent V h := ⟨v, ⟨kj, hk2⟩⟩
              if ev.needed x y then
                match processGuard x y ev (N.guard v ⟨kj, hk2⟩) with
                | .impossible => .impossible
                | .ok es' => .ok (es ++ es')
              else .ok es
            else .ok es) (.ok init2) = .ok result2 →
        e ∈ result2 := by
      intro ks
      induction ks with
      | nil => intro _ _ hki; exact absurd hki (by simp)
      | cons kj ks2 ih2 =>
        intro init2 result2 hki hf; simp only [List.foldl_cons] at hf
        rcases List.mem_cons.mp hki with rfl | hki'
        · simp [dif_pos hk, if_pos hn] at hf
          match hpg : processGuard x y ⟨v, ⟨ki, hk⟩⟩ (N.guard v ⟨ki, hk⟩) with
          | .impossible =>
            simp [hpg] at hf
            have : ∀ (l : List ℕ) (r : BuildResult V h),
                r = BuildResult.impossible →
                l.foldl (fun (acc2 : BuildResult V h) ki =>
                  match acc2 with
                  | .impossible => .impossible
                  | .ok es =>
                    if hk2 : ki < h then
                      let ev : IncrEvent V h := ⟨v, ⟨ki, hk2⟩⟩
                      if ev.needed x y then
                        match processGuard x y ev (N.guard v ⟨ki, hk2⟩) with
                        | .impossible => .impossible
                        | .ok es' => .ok (es ++ es')
                      else .ok es
                    else .ok es) r = BuildResult.impossible := by
              intro l; induction l with
              | nil => intro r hr; simpa
              | cons _ _ ih3 => intro r hr; simp [List.foldl_cons, hr]; exact ih3 _ rfl
            rw [this ks2 _ rfl] at hf; cases hf
          | .ok ges =>
            simp [hpg] at hf
            have hmem := he_in_guard_result ges hpg
            exact guard_fold_preserves ks2 _ result2 hf (List.mem_append.mpr (Or.inr hmem))
        · by_cases hkj : kj < h
          · by_cases hnej : (⟨v, ⟨kj, hkj⟩⟩ : IncrEvent V h).needed x y
            · match hpgj : processGuard x y ⟨v, ⟨kj, hkj⟩⟩ (N.guard v ⟨kj, hkj⟩) with
              | .impossible =>
                simp [dif_pos hkj, if_pos hnej, hpgj] at hf
                have : ∀ (l : List ℕ) (r : BuildResult V h),
                    r = BuildResult.impossible →
                    l.foldl (fun (acc2 : BuildResult V h) ki =>
                      match acc2 with
                      | .impossible => .impossible
                      | .ok es =>
                        if hk2 : ki < h then
                          let ev : IncrEvent V h := ⟨v, ⟨ki, hk2⟩⟩
                          if ev.needed x y then
                            match processGuard x y ev (N.guard v ⟨ki, hk2⟩) with
                            | .impossible => .impossible
                            | .ok es' => .ok (es ++ es')
                          else .ok es
                        else .ok es) r = BuildResult.impossible := by
                  intro l; induction l with
                  | nil => intro r hr; simpa
                  | cons _ _ ih3 => intro r hr; simp [List.foldl_cons, hr]; exact ih3 _ rfl
                rw [this ks2 _ rfl] at hf; cases hf
              | .ok gesj =>
                simp [dif_pos hkj, if_pos hnej, hpgj] at hf
                exact ih2 _ result2 hki' hf
            · simp [dif_pos hkj, if_neg hnej] at hf; exact ih2 _ result2 hki' hf
          · simp [dif_neg hkj] at hf; exact ih2 _ result2 hki' hf
    suffices h2 : ∀ (verts : List V) (init result : List (WtEdge V h)),
        v ∈ verts →
        verts.foldl (fun (acc : BuildResult V h) v =>
          match acc with
          | .impossible => .impossible
          | .ok edges =>
            let chainEs := (List.range h).filterMap fun ki =>
              if hk2 : ki < h ∧ ki + 1 < h then
                let e1 : IncrEvent V h := ⟨v, ⟨ki, hk2.1⟩⟩
                let e2 : IncrEvent V h := ⟨v, ⟨ki + 1, hk2.2⟩⟩
                if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
              else none
            let guardRes := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
              match acc2 with
              | .impossible => .impossible
              | .ok es =>
                if hk2 : ki < h then
                  let ev : IncrEvent V h := ⟨v, ⟨ki, hk2⟩⟩
                  if ev.needed x y then
                    match processGuard x y ev (N.guard v ⟨ki, hk2⟩) with
                    | .impossible => .impossible
                    | .ok es' => .ok (es ++ es')
                  else .ok es
                else .ok es) (.ok [])
            match guardRes with
            | .impossible => .impossible
            | .ok gEs => .ok (edges ++ chainEs ++ gEs)) (.ok init) = .ok result →
        e ∈ result by
      exact h2 _ [] edges (Finset.mem_toList.mpr (Fintype.complete v)) hBuild
    intro verts
    induction verts with
    | nil => intro _ _ hv; exact absurd hv (by simp)
    | cons w ws ih =>
      intro init result hv hfold
      simp only [List.foldl_cons] at hfold
      rcases List.mem_cons.mp hv with rfl | hv'
      · set grv := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
            match acc2 with
            | .impossible => .impossible
            | .ok es =>
              if hk2 : ki < h then
                let ev : IncrEvent V h := ⟨v, ⟨ki, hk2⟩⟩
                if ev.needed x y then
                  match processGuard x y ev (N.guard v ⟨ki, hk2⟩) with
                  | .impossible => .impossible
                  | .ok es' => .ok (es ++ es')
                else .ok es
              else .ok es) (.ok [])
        match hgr : grv with
        | .impossible =>
          simp only [hgr] at hfold
          rw [fold_imp_propagate ws _ rfl] at hfold; cases hfold
        | .ok gEs =>
          simp only [hgr] at hfold
          have he_gEs : e ∈ gEs := he_in_gEs (List.range h) [] gEs (List.mem_range.mpr hk) hgr
          exact fold_preserves ws _ _ hfold
            (List.mem_append.mpr (Or.inr he_gEs))
      · set grv := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
            match acc2 with
            | .impossible => .impossible
            | .ok es =>
              if hk2 : ki < h then
                let ev : IncrEvent V h := ⟨w, ⟨ki, hk2⟩⟩
                if ev.needed x y then
                  match processGuard x y ev (N.guard w ⟨ki, hk2⟩) with
                  | .impossible => .impossible
                  | .ok es' => .ok (es ++ es')
                else .ok es
              else .ok es) (.ok [])
        match hgr : grv with
        | .impossible =>
          simp only [hgr] at hfold
          rw [fold_imp_propagate ws _ rfl] at hfold; cases hfold
        | .ok gEs =>
          simp only [hgr] at hfold
          exact ih _ result hv' hfold
  intro verts
  induction verts with
  | nil => intro init result hfold he; simp [List.foldl] at hfold; cases hfold; exact he
  | cons w ws ih =>
    intro init result hfold he
    simp only [List.foldl_cons] at hfold
    set grv := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
      match acc2 with
      | .impossible => .impossible
      | .ok es =>
        if hk2 : ki < h then
          let ev : IncrEvent V h := ⟨w, ⟨ki, hk2⟩⟩
          if ev.needed x y then
            match processGuard x y ev (N.guard w ⟨ki, hk2⟩) with
            | .impossible => .impossible
            | .ok es' => .ok (es ++ es')
          else .ok es
        else .ok es) (.ok [])
    match hgr : grv with
    | .impossible =>
      simp only [hgr] at hfold
      rw [fold_imp_propagate ws _ rfl] at hfold; cases hfold
    | .ok gEs =>
      simp only [hgr] at hfold
      exact ih _ _ hfold
        (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl he))))

private lemma ub_edge_mem {h : ℕ} {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (v : V) (ki : ℕ) (hk : ki < h) (u : V) (b : Fin (h+1))
    (hn : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩)
    (hlit : IntervalLit.ub u b ∈ N.guard v ⟨ki, hk⟩)
    (hxb : ¬(x u).val > b.val) (hyb : ¬(y u).val ≤ b.val)
    (hb : b.val < h) :
    (⟨⟨v, ⟨ki, hk⟩⟩, ⟨u, ⟨b.val, hb⟩⟩, 0⟩ : WtEdge V h) ∈ edges := by
  set e := (⟨⟨v, ⟨ki, hk⟩⟩, ⟨u, ⟨b.val, hb⟩⟩, 0⟩ : WtEdge V h)
  have hprocLit : processLit x y ⟨v, ⟨ki, hk⟩⟩ (IntervalLit.ub u b) =
      BuildResult.ok [e] := by
    simp only [processLit, if_neg (show ¬(x u).val > b.val from hxb),
      if_neg (show ¬(y u).val ≤ b.val from hyb), dif_pos hb, e]
  have lit_fold_imp : ∀ (l : List (IntervalLit V h)) (r : BuildResult V h),
      r = BuildResult.impossible →
      l.foldl (fun (acc : BuildResult V h) (lit : IntervalLit V h) =>
        match acc with
        | .impossible => .impossible
        | .ok es =>
          match processLit x y ⟨v, ⟨ki, hk⟩⟩ lit with
          | .impossible => .impossible
          | .ok es' => .ok (es ++ es')) r = BuildResult.impossible := by
    intro l; induction l with
    | nil => intro r hr; simpa
    | cons _ _ ih3 => intro r hr; simp [List.foldl_cons, hr]; exact ih3 _ rfl
  have lit_fold_preserves : ∀ (l : ConjGuard V h) (init2 result2 : List (WtEdge V h)),
      e ∈ init2 →
      l.foldl (fun (acc : BuildResult V h) lit =>
        match acc with
        | .impossible => .impossible
        | .ok es =>
          match processLit x y ⟨v, ⟨ki, hk⟩⟩ lit with
          | .impossible => .impossible
          | .ok es' => .ok (es ++ es')) (.ok init2) = .ok result2 →
      e ∈ result2 := by
    intro l
    induction l with
    | nil => intro init2 result2 he2 hf2; simp [List.foldl] at hf2; cases hf2; exact he2
    | cons l2 ls2 ih2 =>
      intro init2 result2 he2 hf2; simp only [List.foldl_cons] at hf2
      match hpl2 : processLit x y ⟨v, ⟨ki, hk⟩⟩ l2 with
      | .impossible =>
        simp [hpl2] at hf2; rw [lit_fold_imp ls2 _ rfl] at hf2; cases hf2
      | .ok es2 =>
        simp [hpl2] at hf2
        exact ih2 _ result2 (List.mem_append.mpr (Or.inl he2)) hf2
  have he_in_guard_result : ∀ (ges : List (WtEdge V h)),
      processGuard x y ⟨v, ⟨ki, hk⟩⟩ (N.guard v ⟨ki, hk⟩) = .ok ges → e ∈ ges := by
    simp only [processGuard]
    intro ges hpg
    suffices key : ∀ (g' : ConjGuard V h) (init : List (WtEdge V h)),
        (IntervalLit.ub u b) ∈ g' →
        g'.foldl (fun (acc : BuildResult V h) lit =>
          match acc with
          | .impossible => .impossible
          | .ok es =>
            match processLit x y ⟨v, ⟨ki, hk⟩⟩ lit with
            | .impossible => .impossible
            | .ok es' => .ok (es ++ es')) (.ok init) = .ok ges →
        e ∈ ges by
      exact key _ [] hlit hpg
    intro g'
    induction g' with
    | nil => intro _ hmem; exact absurd hmem (by simp)
    | cons lit' lits' ih =>
      intro init hmem hfold
      simp only [List.foldl_cons] at hfold
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · rw [hprocLit] at hfold
        exact lit_fold_preserves lits' _ ges
          (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))) hfold
      · match hpl2 : processLit x y ⟨v, ⟨ki, hk⟩⟩ lit' with
        | .impossible =>
          simp [hpl2] at hfold; rw [lit_fold_imp lits' _ rfl] at hfold; cases hfold
        | .ok es2 =>
          simp [hpl2] at hfold; exact ih (init ++ es2) hmem' hfold
  simp only [buildECD] at hBuild
  have fold_imp_propagate : ∀ (l : List V) (r : BuildResult V h),
      r = BuildResult.impossible →
      l.foldl (fun (acc : BuildResult V h) v =>
        match acc with
        | .impossible => .impossible
        | .ok edges =>
          let chainEs := (List.range h).filterMap fun ki =>
            if hk : ki < h ∧ ki + 1 < h then
              let e1 : IncrEvent V h := ⟨v, ⟨ki, hk.1⟩⟩
              let e2 : IncrEvent V h := ⟨v, ⟨ki + 1, hk.2⟩⟩
              if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
            else none
          let guardRes := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
            match acc2 with
            | .impossible => .impossible
            | .ok es =>
              if hk : ki < h then
                let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
                if ev.needed x y then
                  match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
                  | .impossible => .impossible
                  | .ok es' => .ok (es ++ es')
                else .ok es
              else .ok es) (.ok [])
          match guardRes with
          | .impossible => .impossible
          | .ok gEs => .ok (edges ++ chainEs ++ gEs)) r = BuildResult.impossible := by
    intro l; induction l with
    | nil => intro r hr; simpa
    | cons _ _ ihfl => intro r hr; simp only [List.foldl_cons, hr]; exact ihfl _ rfl
  suffices fold_preserves : ∀ (verts : List V) (init result : List (WtEdge V h)),
      verts.foldl (fun (acc : BuildResult V h) v =>
        match acc with
        | .impossible => .impossible
        | .ok edges =>
          let chainEs := (List.range h).filterMap fun ki =>
            if hk : ki < h ∧ ki + 1 < h then
              let e1 : IncrEvent V h := ⟨v, ⟨ki, hk.1⟩⟩
              let e2 : IncrEvent V h := ⟨v, ⟨ki + 1, hk.2⟩⟩
              if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
            else none
          let guardRes := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
            match acc2 with
            | .impossible => .impossible
            | .ok es =>
              if hk : ki < h then
                let ev : IncrEvent V h := ⟨v, ⟨ki, hk⟩⟩
                if ev.needed x y then
                  match processGuard x y ev (N.guard v ⟨ki, hk⟩) with
                  | .impossible => .impossible
                  | .ok es' => .ok (es ++ es')
                else .ok es
              else .ok es) (.ok [])
          match guardRes with
          | .impossible => .impossible
          | .ok gEs => .ok (edges ++ chainEs ++ gEs)) (.ok init) = .ok result →
      e ∈ init → e ∈ result by
    have guard_fold_preserves : ∀ (ks : List ℕ) (init2 result2 : List (WtEdge V h)),
        ks.foldl (fun (acc2 : BuildResult V h) ki =>
          match acc2 with
          | .impossible => .impossible
          | .ok es =>
            if hk2 : ki < h then
              let ev : IncrEvent V h := ⟨v, ⟨ki, hk2⟩⟩
              if ev.needed x y then
                match processGuard x y ev (N.guard v ⟨ki, hk2⟩) with
                | .impossible => .impossible
                | .ok es' => .ok (es ++ es')
              else .ok es
            else .ok es) (.ok init2) = .ok result2 →
        e ∈ init2 → e ∈ result2 := by
      intro ks
      induction ks with
      | nil => intro init2 result2 hf he2; simp [List.foldl] at hf; cases hf; exact he2
      | cons kj ks2 ih2 =>
        intro init2 result2 hf he2; simp only [List.foldl_cons] at hf
        by_cases hkj : kj < h
        · by_cases hnej : (⟨v, ⟨kj, hkj⟩⟩ : IncrEvent V h).needed x y
          · match hpgj : processGuard x y ⟨v, ⟨kj, hkj⟩⟩ (N.guard v ⟨kj, hkj⟩) with
            | .impossible =>
              simp [dif_pos hkj, if_pos hnej, hpgj] at hf
              have : ∀ (l : List ℕ) (r : BuildResult V h),
                  r = BuildResult.impossible →
                  l.foldl (fun (acc2 : BuildResult V h) ki =>
                    match acc2 with
                    | .impossible => .impossible
                    | .ok es =>
                      if hk2 : ki < h then
                        let ev : IncrEvent V h := ⟨v, ⟨ki, hk2⟩⟩
                        if ev.needed x y then
                          match processGuard x y ev (N.guard v ⟨ki, hk2⟩) with
                          | .impossible => .impossible
                          | .ok es' => .ok (es ++ es')
                        else .ok es
                      else .ok es) r = BuildResult.impossible := by
                intro l; induction l with
                | nil => intro r hr; simpa
                | cons _ _ ih3 => intro r hr; simp [List.foldl_cons, hr]; exact ih3 _ rfl
              rw [this ks2 _ rfl] at hf; cases hf
            | .ok gesj =>
              simp [dif_pos hkj, if_pos hnej, hpgj] at hf
              exact ih2 _ result2 hf (List.mem_append.mpr (Or.inl he2))
          · simp [dif_pos hkj, if_neg hnej] at hf; exact ih2 _ result2 hf he2
        · simp [dif_neg hkj] at hf; exact ih2 _ result2 hf he2
    have he_in_gEs : ∀ (ks : List ℕ) (init2 result2 : List (WtEdge V h)),
        ki ∈ ks →
        ks.foldl (fun (acc2 : BuildResult V h) kj =>
          match acc2 with
          | .impossible => .impossible
          | .ok es =>
            if hk2 : kj < h then
              let ev : IncrEvent V h := ⟨v, ⟨kj, hk2⟩⟩
              if ev.needed x y then
                match processGuard x y ev (N.guard v ⟨kj, hk2⟩) with
                | .impossible => .impossible
                | .ok es' => .ok (es ++ es')
              else .ok es
            else .ok es) (.ok init2) = .ok result2 →
        e ∈ result2 := by
      intro ks
      induction ks with
      | nil => intro _ _ hki; exact absurd hki (by simp)
      | cons kj ks2 ih2 =>
        intro init2 result2 hki hf; simp only [List.foldl_cons] at hf
        rcases List.mem_cons.mp hki with rfl | hki'
        · simp [dif_pos hk, if_pos hn] at hf
          match hpg : processGuard x y ⟨v, ⟨ki, hk⟩⟩ (N.guard v ⟨ki, hk⟩) with
          | .impossible =>
            simp [hpg] at hf
            have : ∀ (l : List ℕ) (r : BuildResult V h),
                r = BuildResult.impossible →
                l.foldl (fun (acc2 : BuildResult V h) ki =>
                  match acc2 with
                  | .impossible => .impossible
                  | .ok es =>
                    if hk2 : ki < h then
                      let ev : IncrEvent V h := ⟨v, ⟨ki, hk2⟩⟩
                      if ev.needed x y then
                        match processGuard x y ev (N.guard v ⟨ki, hk2⟩) with
                        | .impossible => .impossible
                        | .ok es' => .ok (es ++ es')
                      else .ok es
                    else .ok es) r = BuildResult.impossible := by
              intro l; induction l with
              | nil => intro r hr; simpa
              | cons _ _ ih3 => intro r hr; simp [List.foldl_cons, hr]; exact ih3 _ rfl
            rw [this ks2 _ rfl] at hf; cases hf
          | .ok ges =>
            simp [hpg] at hf
            have hmem := he_in_guard_result ges hpg
            exact guard_fold_preserves ks2 _ result2 hf (List.mem_append.mpr (Or.inr hmem))
        · by_cases hkj : kj < h
          · by_cases hnej : (⟨v, ⟨kj, hkj⟩⟩ : IncrEvent V h).needed x y
            · match hpgj : processGuard x y ⟨v, ⟨kj, hkj⟩⟩ (N.guard v ⟨kj, hkj⟩) with
              | .impossible =>
                simp [dif_pos hkj, if_pos hnej, hpgj] at hf
                have : ∀ (l : List ℕ) (r : BuildResult V h),
                    r = BuildResult.impossible →
                    l.foldl (fun (acc2 : BuildResult V h) ki =>
                      match acc2 with
                      | .impossible => .impossible
                      | .ok es =>
                        if hk2 : ki < h then
                          let ev : IncrEvent V h := ⟨v, ⟨ki, hk2⟩⟩
                          if ev.needed x y then
                            match processGuard x y ev (N.guard v ⟨ki, hk2⟩) with
                            | .impossible => .impossible
                            | .ok es' => .ok (es ++ es')
                          else .ok es
                        else .ok es) r = BuildResult.impossible := by
                  intro l; induction l with
                  | nil => intro r hr; simpa
                  | cons _ _ ih3 => intro r hr; simp [List.foldl_cons, hr]; exact ih3 _ rfl
                rw [this ks2 _ rfl] at hf; cases hf
              | .ok gesj =>
                simp [dif_pos hkj, if_pos hnej, hpgj] at hf
                exact ih2 _ result2 hki' hf
            · simp [dif_pos hkj, if_neg hnej] at hf; exact ih2 _ result2 hki' hf
          · simp [dif_neg hkj] at hf; exact ih2 _ result2 hki' hf
    suffices h2 : ∀ (verts : List V) (init result : List (WtEdge V h)),
        v ∈ verts →
        verts.foldl (fun (acc : BuildResult V h) v =>
          match acc with
          | .impossible => .impossible
          | .ok edges =>
            let chainEs := (List.range h).filterMap fun ki =>
              if hk2 : ki < h ∧ ki + 1 < h then
                let e1 : IncrEvent V h := ⟨v, ⟨ki, hk2.1⟩⟩
                let e2 : IncrEvent V h := ⟨v, ⟨ki + 1, hk2.2⟩⟩
                if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
              else none
            let guardRes := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
              match acc2 with
              | .impossible => .impossible
              | .ok es =>
                if hk2 : ki < h then
                  let ev : IncrEvent V h := ⟨v, ⟨ki, hk2⟩⟩
                  if ev.needed x y then
                    match processGuard x y ev (N.guard v ⟨ki, hk2⟩) with
                    | .impossible => .impossible
                    | .ok es' => .ok (es ++ es')
                  else .ok es
                else .ok es) (.ok [])
            match guardRes with
            | .impossible => .impossible
            | .ok gEs => .ok (edges ++ chainEs ++ gEs)) (.ok init) = .ok result →
        e ∈ result by
      exact h2 _ [] edges (Finset.mem_toList.mpr (Fintype.complete v)) hBuild
    intro verts
    induction verts with
    | nil => intro _ _ hv; exact absurd hv (by simp)
    | cons w ws ih =>
      intro init result hv hfold
      simp only [List.foldl_cons] at hfold
      rcases List.mem_cons.mp hv with rfl | hv'
      · set grv := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
            match acc2 with
            | .impossible => .impossible
            | .ok es =>
              if hk2 : ki < h then
                let ev : IncrEvent V h := ⟨v, ⟨ki, hk2⟩⟩
                if ev.needed x y then
                  match processGuard x y ev (N.guard v ⟨ki, hk2⟩) with
                  | .impossible => .impossible
                  | .ok es' => .ok (es ++ es')
                else .ok es
              else .ok es) (.ok [])
        match hgr : grv with
        | .impossible =>
          simp only [hgr] at hfold
          rw [fold_imp_propagate ws _ rfl] at hfold; cases hfold
        | .ok gEs =>
          simp only [hgr] at hfold
          have he_gEs : e ∈ gEs := he_in_gEs (List.range h) [] gEs (List.mem_range.mpr hk) hgr
          exact fold_preserves ws _ _ hfold
            (List.mem_append.mpr (Or.inr he_gEs))
      · set grv := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
            match acc2 with
            | .impossible => .impossible
            | .ok es =>
              if hk2 : ki < h then
                let ev : IncrEvent V h := ⟨w, ⟨ki, hk2⟩⟩
                if ev.needed x y then
                  match processGuard x y ev (N.guard w ⟨ki, hk2⟩) with
                  | .impossible => .impossible
                  | .ok es' => .ok (es ++ es')
                else .ok es
              else .ok es) (.ok [])
        match hgr : grv with
        | .impossible =>
          simp only [hgr] at hfold
          rw [fold_imp_propagate ws _ rfl] at hfold; cases hfold
        | .ok gEs =>
          simp only [hgr] at hfold
          exact ih _ result hv' hfold
  intro verts
  induction verts with
  | nil => intro init result hfold he; simp [List.foldl] at hfold; cases hfold; exact he
  | cons w ws ih =>
    intro init result hfold he
    simp only [List.foldl_cons] at hfold
    set grv := (List.range h).foldl (fun (acc2 : BuildResult V h) ki =>
      match acc2 with
      | .impossible => .impossible
      | .ok es =>
        if hk2 : ki < h then
          let ev : IncrEvent V h := ⟨w, ⟨ki, hk2⟩⟩
          if ev.needed x y then
            match processGuard x y ev (N.guard w ⟨ki, hk2⟩) with
            | .impossible => .impossible
            | .ok es' => .ok (es ++ es')
          else .ok es
        else .ok es) (.ok [])
    match hgr : grv with
    | .impossible =>
      simp only [hgr] at hfold
      rw [fold_imp_propagate ws _ rfl] at hfold; cases hfold
    | .ok gEs =>
      simp only [hgr] at hfold
      exact ih _ _ hfold
        (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl he))))

private lemma needed_intermediate {h : ℕ}
    {x y : Config V h} {v : V} {k1 k2 : ℕ}
    {hk1 : k1 < h} {hk2 : k2 < h}
    (hn1 : IncrEvent.needed x y ⟨v, ⟨k1, hk1⟩⟩)
    (hn2 : IncrEvent.needed x y ⟨v, ⟨k2, hk2⟩⟩)
    (ki : ℕ) (hge : ki ≥ k1) (hle : ki ≤ k2) (hlt : ki < h) :
    IncrEvent.needed x y ⟨v, ⟨ki, hlt⟩⟩ := by
  simp only [IncrEvent.needed, IncrEvent.v, IncrEvent.k] at *; constructor <;> omega

private lemma needed_events_chain_τ {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (τ : IncrEvent V h → ℤ)
    (hτ : TimingValid ⟨edges⟩ τ)
    (v : V) (k1 k2 : ℕ) (hk1 : k1 < h) (hk2 : k2 < h)
    (hle12 : k1 ≤ k2)
    (hn1 : IncrEvent.needed x y ⟨v, ⟨k1, hk1⟩⟩)
    (hn2 : IncrEvent.needed x y ⟨v, ⟨k2, hk2⟩⟩) :
    τ ⟨v, ⟨k1, hk1⟩⟩ ≤ τ ⟨v, ⟨k2, hk2⟩⟩ := by
  suffices key : ∀ d : ℕ, ∀ a b : ℕ, (ha : a < h) → (hb : b < h) →
      b = a + d → a ≥ k1 → b ≤ k2 →
      IncrEvent.needed x y ⟨v, ⟨a, ha⟩⟩ →
      IncrEvent.needed x y ⟨v, ⟨b, hb⟩⟩ →
      τ ⟨v, ⟨a, ha⟩⟩ ≤ τ ⟨v, ⟨b, hb⟩⟩ by
    exact key (k2 - k1) k1 k2 hk1 hk2 (by omega) (le_refl _) (le_refl _) hn1 hn2
  intro d
  induction d with
  | zero =>
    intro a b ha hb hab _ _ hna _
    have : a = b := by omega
    subst this; have : ha = hb := rfl; exact le_refl _
  | succ d ih =>
    intro a b ha hb hab hage hble hna hnb
    have hb' : a + d < h := by omega
    have hnm : IncrEvent.needed x y ⟨v, ⟨a + d, hb'⟩⟩ := by
      simp only [IncrEvent.needed, IncrEvent.v, IncrEvent.k] at *; constructor <;> omega
    have h1 := ih a (a + d) ha hb' rfl hage (by omega) hna hnm
    have h2 : τ ⟨v, ⟨a + d, hb'⟩⟩ + 1 ≤ τ ⟨v, ⟨b, hb⟩⟩ := by
      have hbd : b = (a + d) + 1 := by omega
      subst hbd
      have he := chain_edge_mem hBuild v (a + d) hb' hb hnm hnb
      have := hτ ⟨⟨v, ⟨a + d, hb'⟩⟩, ⟨v, ⟨(a + d) + 1, hb⟩⟩, 1⟩ he
      simp at this; linarith
    linarith

private lemma imp_foldl_imp {h : ℕ}
    {x y : Config V h} {ev : IncrEvent V h}
    (lits : List (IntervalLit V h)) :
    lits.foldl (fun (acc : BuildResult V h) l => match acc with
      | .impossible => .impossible
      | .ok es => match processLit x y ev l with
        | .impossible => .impossible
        | .ok es' => .ok (es ++ es')) (.impossible) = BuildResult.impossible := by
  induction lits with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl_cons]; exact ih

private lemma processGuard_lit_imp {h : ℕ}
    {x y : Config V h} {ev : IncrEvent V h}
    (g : ConjGuard V h) (lit : IntervalLit V h)
    (hlit : lit ∈ g)
    (himp : processLit x y ev lit = BuildResult.impossible) :
    ∀ init : List (WtEdge V h),
    g.foldl (fun (acc : BuildResult V h) l => match acc with
      | .impossible => .impossible
      | .ok es => match processLit x y ev l with
        | .impossible => .impossible
        | .ok es' => .ok (es ++ es')) (.ok init) = BuildResult.impossible := by
  induction g with
  | nil => exact absurd hlit (by simp)
  | cons l ls ihl =>
    intro init; simp only [List.foldl_cons]
    rcases List.mem_cons.mp hlit with rfl | hm'
    · rw [himp]; exact imp_foldl_imp ls
    · match hpl : processLit x y ev l with
      | .impossible => exact imp_foldl_imp ls
      | .ok es' =>
        show ls.foldl _ (BuildResult.ok (init ++ es')) = _
        exact ihl hm' _

private lemma ki_imp_foldl_imp {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h} {v : V}
    (ks : List ℕ) :
    ks.foldl (fun (acc2 : BuildResult V h) kj => match acc2 with
      | .impossible => .impossible
      | .ok es => if hkj : kj < h then
          let ev : IncrEvent V h := ⟨v, ⟨kj, hkj⟩⟩
          if ev.needed x y then match processGuard x y ev (N.guard v ⟨kj, hkj⟩) with
            | .impossible => .impossible
            | .ok es' => .ok (es ++ es')
          else .ok es
        else .ok es) (.impossible) = BuildResult.impossible := by
  induction ks with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl_cons]; exact ih

private lemma guardRes_foldl_ki_imp {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h} {v : V}
    {ki : ℕ} {hk : ki < h}
    (hn : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩)
    (himp : processGuard x y ⟨v, ⟨ki, hk⟩⟩ (N.guard v ⟨ki, hk⟩) = BuildResult.impossible)
    (init : List (WtEdge V h)) :
    (List.range h).foldl (fun (acc2 : BuildResult V h) kj => match acc2 with
      | .impossible => .impossible
      | .ok es => if hkj : kj < h then
          let ev : IncrEvent V h := ⟨v, ⟨kj, hkj⟩⟩
          if ev.needed x y then match processGuard x y ev (N.guard v ⟨kj, hkj⟩) with
            | .impossible => .impossible
            | .ok es' => .ok (es ++ es')
          else .ok es
        else .ok es) (.ok init) = BuildResult.impossible := by
  suffices key : ∀ (ks : List ℕ), ki ∈ ks →
      ∀ init : List (WtEdge V h),
      ks.foldl (fun (acc2 : BuildResult V h) kj => match acc2 with
        | .impossible => .impossible
        | .ok es => if hkj : kj < h then
            let ev : IncrEvent V h := ⟨v, ⟨kj, hkj⟩⟩
            if ev.needed x y then match processGuard x y ev (N.guard v ⟨kj, hkj⟩) with
              | .impossible => .impossible
              | .ok es' => .ok (es ++ es')
            else .ok es
          else .ok es) (.ok init) = BuildResult.impossible from
    key _ (List.mem_range.mpr hk) init
  intro ks
  induction ks with
  | nil => intro hm; exact absurd hm (by simp)
  | cons kj ks2 ih2 =>
    intro hm init; simp only [List.foldl_cons]
    rcases List.mem_cons.mp hm with rfl | hm'
    · simp only [dif_pos hk, if_pos hn, himp]; exact ki_imp_foldl_imp ks2
    · by_cases hkj2 : kj < h
      · by_cases hnej : (⟨v, ⟨kj, hkj2⟩⟩ : IncrEvent V h).needed x y
        · match hpg2 : processGuard x y ⟨v, ⟨kj, hkj2⟩⟩ (N.guard v ⟨kj, hkj2⟩) with
          | .impossible =>
            simp [dif_pos hkj2, if_pos hnej, hpg2]; exact ki_imp_foldl_imp ks2
          | .ok gs2 => simp [dif_pos hkj2, if_pos hnej, hpg2]; exact ih2 hm' _
        · simp [dif_pos hkj2, if_neg hnej]; exact ih2 hm' _
      · simp [dif_neg hkj2]; exact ih2 hm' _

private lemma v_imp_foldl_imp {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    (verts : List V) :
    verts.foldl (fun (acc : BuildResult V h) v' => match acc with
      | .impossible => .impossible
      | .ok edges =>
        let chainEs := (List.range h).filterMap fun ki' =>
          if hk' : ki' < h ∧ ki' + 1 < h then
            let e1 : IncrEvent V h := ⟨v', ⟨ki', hk'.1⟩⟩
            let e2 : IncrEvent V h := ⟨v', ⟨ki' + 1, hk'.2⟩⟩
            if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
          else none
        let guardRes := (List.range h).foldl (fun (acc2 : BuildResult V h) kj => match acc2 with
          | .impossible => .impossible
          | .ok es => if hkj : kj < h then
              let ev : IncrEvent V h := ⟨v', ⟨kj, hkj⟩⟩
              if ev.needed x y then match processGuard x y ev (N.guard v' ⟨kj, hkj⟩) with
                | .impossible => .impossible
                | .ok es' => .ok (es ++ es')
              else .ok es
            else .ok es) (.ok [])
        match guardRes with
        | .impossible => .impossible
        | .ok gEs => .ok (edges ++ chainEs ++ gEs)) (.impossible) = BuildResult.impossible := by
  induction verts with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl_cons]; exact ih

private lemma buildECD_v_ki_imp {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    {v : V} {ki : ℕ} {hk : ki < h}
    (hn : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩)
    (himp : processGuard x y ⟨v, ⟨ki, hk⟩⟩ (N.guard v ⟨ki, hk⟩) = BuildResult.impossible) :
    False := by
  simp only [buildECD] at hBuild
  set verts := (Fintype.elems : Finset V).val.toList
  have hv_mem : v ∈ verts := Finset.mem_toList.mpr (Fintype.complete v)
  suffices key : ∀ (vs : List V) (init : List (WtEdge V h)),
      v ∈ vs →
      vs.foldl (fun (acc : BuildResult V h) v' => match acc with
        | .impossible => .impossible
        | .ok edges =>
          let chainEs := (List.range h).filterMap fun ki' =>
            if hk' : ki' < h ∧ ki' + 1 < h then
              let e1 : IncrEvent V h := ⟨v', ⟨ki', hk'.1⟩⟩
              let e2 : IncrEvent V h := ⟨v', ⟨ki' + 1, hk'.2⟩⟩
              if e1.needed x y ∧ e2.needed x y then some ⟨e1, e2, 1⟩ else none
            else none
          let guardRes := (List.range h).foldl (fun (acc2 : BuildResult V h) kj => match acc2 with
            | .impossible => .impossible
            | .ok es => if hkj : kj < h then
                let ev : IncrEvent V h := ⟨v', ⟨kj, hkj⟩⟩
                if ev.needed x y then match processGuard x y ev (N.guard v' ⟨kj, hkj⟩) with
                  | .impossible => .impossible
                  | .ok es' => .ok (es ++ es')
                else .ok es
              else .ok es) (.ok [])
          match guardRes with
          | .impossible => .impossible
          | .ok gEs => .ok (edges ++ chainEs ++ gEs)) (.ok init)
        = BuildResult.impossible by
    have := key verts [] hv_mem
    rw [this] at hBuild; cases hBuild
  intro vs
  induction vs with
  | nil => intro _ hm; exact absurd hm (by simp)
  | cons w ws ih =>
    intro init hm
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hm with rfl | hm'
    · have hgr := guardRes_foldl_ki_imp hn himp ([] : List (WtEdge V h))
      rw [hgr]; exact v_imp_foldl_imp ws
    · match hgrv :
        (List.range h).foldl (fun (acc2 : BuildResult V h) kj => match acc2 with
          | .impossible => .impossible
          | .ok es => if hkj : kj < h then
              let ev : IncrEvent V h := ⟨w, ⟨kj, hkj⟩⟩
              if ev.needed x y then match processGuard x y ev (N.guard w ⟨kj, hkj⟩) with
                | .impossible => .impossible
                | .ok es' => .ok (es ++ es')
              else .ok es
            else .ok es) (BuildResult.ok []) with
      | .impossible =>
        show ws.foldl _ (BuildResult.impossible) = _
        exact v_imp_foldl_imp ws
      | .ok gEs =>
        show ws.foldl _ (BuildResult.ok (init ++ _ ++ gEs)) = _
        exact ih _ hm'

private lemma build_ok_lit_lb {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (v : V) (ki : ℕ) (hk : ki < h)
    (hn : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩)
    (u : V) (a : Fin (h+1))
    (hlit : IntervalLit.lb u a ∈ N.guard v ⟨ki, hk⟩)
    (hxa : a.val > (x u).val) :
    ¬(y u).val < a.val := by
  intro hylt
  have himp : processLit x y ⟨v, ⟨ki, hk⟩⟩ (IntervalLit.lb u a) = BuildResult.impossible := by
    simp only [processLit, if_pos hylt]
  have hpg : processGuard x y ⟨v, ⟨ki, hk⟩⟩ (N.guard v ⟨ki, hk⟩) = BuildResult.impossible := by
    simp only [processGuard]
    exact processGuard_lit_imp (N.guard v ⟨ki, hk⟩) (IntervalLit.lb u a) hlit himp []
  exact buildECD_v_ki_imp hBuild hn hpg

private lemma build_ok_lit_ub {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (v : V) (ki : ℕ) (hk : ki < h)
    (hn : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩)
    (u : V) (b : Fin (h+1))
    (hlit : IntervalLit.ub u b ∈ N.guard v ⟨ki, hk⟩)
    (hxb : (x u).val > b.val) :
    False := by
  have himp : processLit x y ⟨v, ⟨ki, hk⟩⟩ (IntervalLit.ub u b) = BuildResult.impossible := by
    simp only [processLit, if_pos hxb]
  have hpg : processGuard x y ⟨v, ⟨ki, hk⟩⟩ (N.guard v ⟨ki, hk⟩) = BuildResult.impossible := by
    simp only [processGuard]
    exact processGuard_lit_imp (N.guard v ⟨ki, hk⟩) (IntervalLit.ub u b) hlit himp []
  exact buildECD_v_ki_imp hBuild hn hpg

private lemma orbit_le_before_τ {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (τ : IncrEvent V h → ℤ)
    (hτ : TimingValid ⟨edges⟩ τ)
    (hPos : ∀ e, τ e ≥ 1)
    (hle : configLE x y)
    (v : V) (ki : ℕ) (hk : ki < h)
    (hn : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩)
    (n : ℕ) (hn_lt : n < (τ ⟨v, ⟨ki, hk⟩⟩).toNat) :
    (mkOrbit N x y τ n v).val ≤ ki := by
  suffices key : ∀ (n : ℕ), ∀ (v : V) (ki : ℕ) (hk : ki < h),
      IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩ →
      n < (τ ⟨v, ⟨ki, hk⟩⟩).toNat →
      (mkOrbit N x y τ n v).val ≤ ki from key n v ki hk hn hn_lt
  intro n
  induction n with
  | zero => intro v' ki' hk' hn' _; simp [mkOrbit]; exact hn'.1
  | succ m ihm =>
    intro v' ki' hk' hn' hlt
    have ihm' : (mkOrbit N x y τ m v').val ≤ ki' := ihm v' ki' hk' hn' (by omega)
    rw [mkOrbit_succ]; simp only [asyncStep]
    split_ifs with hmem
    · have hunit := CIUIFN.localF_unitIncr N v' (mkOrbit N x y τ m)
      by_cases hlt2 : (mkOrbit N x y τ m v').val < ki'
      · omega
      · have heq : (mkOrbit N x y τ m v').val = ki' := by omega
        simp only [mkSched, Finset.mem_filter] at hmem
        obtain ⟨_, k', hk'n, hk'τ⟩ := hmem
        exfalso
        by_cases hlt3 : k'.val < ki'
        · have hle_k' := ihm v' k'.val k'.isLt hk'n (by omega : m < (τ ⟨v', k'⟩).toNat)
          omega
        · have hge : k'.val ≥ ki' := by omega
          have hτ_le := needed_events_chain_τ hBuild τ hτ v' ki' k'.val hk' k'.isLt hge hn' hk'n
          have hτ_k'_eq : τ ⟨v', k'⟩ = ↑(m + 1) := hk'τ
          have hp1 := hPos ⟨v', ⟨ki', hk'⟩⟩
          have : (τ ⟨v', ⟨ki', hk'⟩⟩) ≤ ↑(m + 1) := by linarith
          have : (τ ⟨v', ⟨ki', hk'⟩⟩).toNat ≤ m + 1 := by
            have : 0 ≤ τ ⟨v', ⟨ki', hk'⟩⟩ := by linarith
            omega
          omega
    · exact ihm'

private lemma mkOrbit_in_sched {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    (τ : IncrEvent V h → ℤ)
    (v : V) (ki : ℕ) (hk : ki < h)
    (hn : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩)
    (t : ℕ) (ht : t + 1 = (τ ⟨v, ⟨ki, hk⟩⟩).toNat)
    (hPos : τ ⟨v, ⟨ki, hk⟩⟩ ≥ 1) :
    v ∈ mkSched N x y τ t := by
  simp only [mkSched, Finset.mem_filter]
  constructor
  · exact Finset.mem_univ v
  · exact ⟨⟨ki, hk⟩, hn, by omega⟩

private lemma mkOrbit_val_le_y {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (τ : IncrEvent V h → ℤ)
    (hτ : TimingValid ⟨edges⟩ τ)
    (hPos : ∀ e, τ e ≥ 1)
    (hle : configLE x y) (n : ℕ) (v : V) :
    (mkOrbit N x y τ n v).val ≤ (y v).val := by
  induction n with
  | zero => simp [mkOrbit]; exact Fin.val_le_of_le (hle v)
  | succ m ihm =>
    rw [mkOrbit_succ]; simp only [asyncStep]
    split_ifs with hmem
    · have hunit := CIUIFN.localF_unitIncr N v (mkOrbit N x y τ m)
      by_cases hlt2 : (mkOrbit N x y τ m v).val < (y v).val
      · omega
      · have heq : (mkOrbit N x y τ m v).val = (y v).val := by omega
        simp only [mkSched, Finset.mem_filter] at hmem
        obtain ⟨_, k', hk'n, hk'τ⟩ := hmem
        exfalso
        have hk'v : k'.val + 1 ≤ (y v).val := hk'n.2
        have hfin : (⟨k'.val, k'.isLt⟩ : Fin h) = k' := Fin.eta k' k'.isLt
        have hτ_k' : (τ ⟨v, ⟨k'.val, k'.isLt⟩⟩).toNat = m + 1 := by
          rw [show (⟨v, ⟨k'.val, k'.isLt⟩⟩ : IncrEvent V h) = ⟨v, k'⟩ from
            congrArg (IncrEvent.mk v) hfin]
          rw [hk'τ]; exact Int.toNat_natCast (m + 1)
        have hle_k' := orbit_le_before_τ hBuild τ hτ hPos hle v k'.val k'.isLt hk'n m (by omega)
        omega
    · exact ihm

private lemma orbit_ge_at_τ {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (τ : IncrEvent V h → ℤ)
    (hτ : TimingValid ⟨edges⟩ τ)
    (hPos : ∀ e, τ e ≥ 1)
    (hle : configLE x y)
    (v : V) (ki : ℕ) (hk : ki < h)
    (hn : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩)
    (n : ℕ) (hn_ge : n ≥ (τ ⟨v, ⟨ki, hk⟩⟩).toNat) :
    (mkOrbit N x y τ n v).val ≥ ki + 1 := by
  suffices key : ∀ T : ℕ, ∀ v : V, ∀ ki : ℕ, (hk : ki < h) →
      IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩ →
      (τ ⟨v, ⟨ki, hk⟩⟩).toNat = T →
      (mkOrbit N x y τ T v).val ≥ ki + 1 by
    have hbase := key _ v ki hk hn rfl
    have hmono := mkOrbit_mono_trans N x y τ v hn_ge
    have := Fin.val_le_of_le hmono; omega
  intro T
  induction T using Nat.strongRecOn with
  | _ T ihT =>
    intro v' ki' hk' hn' hτ_eq
    have hτ_pos : T ≥ 1 := by have := hPos ⟨v', ⟨ki', hk'⟩⟩; omega
    have ht_eq : T = (T - 1) + 1 := by omega
    have h_exact_before : (mkOrbit N x y τ (T - 1) v').val = ki' := by
      apply Nat.le_antisymm
      · rw [← hτ_eq]
        exact orbit_le_before_τ hBuild τ hτ hPos hle v' ki' hk' hn' _ (by omega)
      · by_cases hki' : ki' = (x v').val
        · have h0 : (mkOrbit N x y τ 0 v').val = (x v').val := by simp [mkOrbit]
          have hmv := mkOrbit_mono_trans N x y τ v' (Nat.zero_le (T - 1))
          have := Fin.val_le_of_le hmv; omega
        · have hki'_gt : ki' > (x v').val := by
            simp only [IncrEvent.needed, IncrEvent.v, IncrEvent.k] at hn'; omega
          have hprev : ki' - 1 < h := by omega
          have hprev2 : ki' - 1 + 1 < h := by omega
          have hn_prev : IncrEvent.needed x y ⟨v', ⟨ki' - 1, hprev⟩⟩ := by
            simp only [IncrEvent.needed, IncrEvent.v, IncrEvent.k] at *; constructor <;> omega
          have hn_ki_as_succ : IncrEvent.needed x y ⟨v', ⟨ki' - 1 + 1, hprev2⟩⟩ := by
            have : ki' - 1 + 1 = ki' := by omega
            simp only [this]; exact hn'
          have hτ_prev_le : (τ ⟨v', ⟨ki' - 1, hprev⟩⟩).toNat ≤ T - 1 := by
            have hle_τ := needed_events_chain_τ hBuild τ hτ v' (ki' - 1) ki' hprev hk' (by omega)
              hn_prev hn'
            have he := chain_edge_mem hBuild v' (ki' - 1) hprev hprev2 hn_prev hn_ki_as_succ
            have htv := hτ ⟨⟨v', ⟨ki' - 1, hprev⟩⟩, ⟨v', ⟨ki' - 1 + 1, hprev2⟩⟩, 1⟩ he
            simp only [WtEdge.src, WtEdge.tgt, WtEdge.wt] at htv
            have : τ ⟨v', ⟨ki' - 1 + 1, hprev2⟩⟩ = τ ⟨v', ⟨ki', hk'⟩⟩ :=
              congrArg τ (congrArg (IncrEvent.mk v') (Fin.ext (by omega : (ki' - 1 + 1 : ℕ) = ki')))
            rw [this] at htv; omega
          have hτ_prev_lt : (τ ⟨v', ⟨ki' - 1, hprev⟩⟩).toNat < T := by omega
          have hge_prev := ihT _ hτ_prev_lt v' (ki' - 1) hprev hn_prev rfl
          have hmono := mkOrbit_mono_trans N x y τ v' hτ_prev_le
          have := Fin.val_le_of_le hmono; omega
    have h_guard : (N.guard v' ⟨ki', hk'⟩).holds
        (mkOrbit N x y τ (T - 1)) := by
      intro lit hlit
      cases lit with
      | lb u a =>
        simp only [IntervalLit.holds]
        by_cases hxa : a.val ≤ (x u).val
        · have h0 : (mkOrbit N x y τ 0 u).val = (x u).val := by simp [mkOrbit]
          have hmv := mkOrbit_mono_trans N x y τ u (Nat.zero_le (T - 1))
          exact Fin.le_iff_val_le_val.mpr (by have := Fin.val_le_of_le hmv; omega)
        · push_neg at hxa
          have hya : ¬(y u).val < a.val :=
            build_ok_lit_lb hBuild v' ki' hk' hn' u a hlit hxa
          push_neg at hya
          have ha1 : a.val ≥ 1 := by omega
          have ha2 : a.val - 1 < h := by have := a.isLt; omega
          have hn_u : IncrEvent.needed x y ⟨u, ⟨a.val - 1, ha2⟩⟩ := by
            simp only [IncrEvent.needed, IncrEvent.v, IncrEvent.k]; constructor <;> omega
          have he := lb_edge_mem hBuild v' ki' hk' u a hn' hlit (by omega) (by omega) ⟨ha1, ha2⟩
          have htv := hτ ⟨⟨u, ⟨a.val - 1, ha2⟩⟩, ⟨v', ⟨ki', hk'⟩⟩, 1⟩ he
          simp only [WtEdge.src, WtEdge.tgt, WtEdge.wt] at htv
          have hτ_u_lt : (τ ⟨u, ⟨a.val - 1, ha2⟩⟩).toNat < T := by rw [← hτ_eq]; omega
          have hge_u := ihT _ hτ_u_lt u (a.val - 1) ha2 hn_u rfl
          have hmono := mkOrbit_mono_trans N x y τ u (show (τ ⟨u, ⟨a.val - 1, ha2⟩⟩).toNat ≤ T - 1 by omega)
          exact Fin.le_iff_val_le_val.mpr (by have := Fin.val_le_of_le hmono; omega)
      | ub u b =>
        simp only [IntervalLit.holds]
        by_cases hyb : (y u).val ≤ b.val
        · have hle_y := mkOrbit_val_le_y hBuild τ hτ hPos hle (T - 1) u
          exact Fin.le_iff_val_le_val.mpr (by omega)
        · push_neg at hyb
          have hxb : (x u).val ≤ b.val := by
            by_contra hc; push_neg at hc
            exact build_ok_lit_ub hBuild v' ki' hk' hn' u b hlit hc
          have hb_lt : b.val < h := by have := b.isLt; omega
          have hn_u : IncrEvent.needed x y ⟨u, ⟨b.val, hb_lt⟩⟩ := by
            simp only [IncrEvent.needed, IncrEvent.v, IncrEvent.k]; constructor <;> omega
          have he := ub_edge_mem hBuild v' ki' hk' u b hn' hlit (by omega) (by omega) hb_lt
          have htv := hτ ⟨⟨v', ⟨ki', hk'⟩⟩, ⟨u, ⟨b.val, hb_lt⟩⟩, 0⟩ he
          simp only [WtEdge.src, WtEdge.tgt, WtEdge.wt] at htv
          have hτ_ub_nat : T ≤ (τ ⟨u, ⟨b.val, hb_lt⟩⟩).toNat := by
            rw [← hτ_eq]; have := hPos ⟨u, ⟨b.val, hb_lt⟩⟩; omega
          have hle_b := orbit_le_before_τ hBuild τ hτ hPos hle u b.val hb_lt hn_u (T - 1) (by omega)
          exact Fin.le_iff_val_le_val.mpr hle_b
    rw [ht_eq, mkOrbit_succ]; simp only [asyncStep]
    have h_in : v' ∈ mkSched N x y τ (T - 1) :=
      mkOrbit_in_sched τ v' ki' hk' hn' (T - 1) (by omega) (hPos _)
    rw [if_pos h_in]
    simp only [CIUIFN.localF]
    have hlt : (mkOrbit N x y τ (T - 1) v').val < h := by rw [h_exact_before]; exact hk'
    rw [dif_pos hlt]
    have hfk : (⟨(mkOrbit N x y τ (T - 1) v').val, hlt⟩ : Fin h) = ⟨ki', hk'⟩ := by
      ext; exact h_exact_before
    rw [hfk]
    rw [if_pos h_guard]
    simp only [Fin.val_mk]; rw [h_exact_before]

private lemma mkOrbit_val_exact_before {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (τ : IncrEvent V h → ℤ)
    (hτ : TimingValid ⟨edges⟩ τ)
    (hPos : ∀ e, τ e ≥ 1)
    (hle : configLE x y)
    (v : V) (ki : ℕ) (hk : ki < h)
    (hn : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩) :
    (mkOrbit N x y τ ((τ ⟨v, ⟨ki, hk⟩⟩).toNat - 1) v).val = ki := by
  have hτ_pos : (τ ⟨v, ⟨ki, hk⟩⟩).toNat ≥ 1 := by have := hPos ⟨v, ⟨ki, hk⟩⟩; omega
  apply Nat.le_antisymm
  · exact orbit_le_before_τ hBuild τ hτ hPos hle v ki hk hn _ (by omega)
  · by_cases hki : ki = (x v).val
    · have h0 : (mkOrbit N x y τ 0 v).val = (x v).val := by simp [mkOrbit]
      have hmv := mkOrbit_mono_trans N x y τ v (Nat.zero_le ((τ ⟨v, ⟨ki, hk⟩⟩).toNat - 1))
      have := Fin.val_le_of_le hmv; omega
    · have hxv_le : (x v).val ≤ ki := hn.1
      have hki_gt : ki > (x v).val := by omega
      have hprev : ki - 1 < h := by omega
      have hyv : ki + 1 ≤ (y v).val := hn.2
      have hn_prev : IncrEvent.needed x y ⟨v, ⟨ki - 1, hprev⟩⟩ := by
        simp only [IncrEvent.needed, IncrEvent.v, IncrEvent.k]; constructor <;> omega
      have hprev2 : ki - 1 + 1 < h := by omega
      have hn_ki_as_succ : IncrEvent.needed x y ⟨v, ⟨ki - 1 + 1, hprev2⟩⟩ := by
        have : ki - 1 + 1 = ki := by omega
        simp only [this]; exact hn
      have hτ_prev_le : (τ ⟨v, ⟨ki - 1, hprev⟩⟩).toNat ≤ (τ ⟨v, ⟨ki, hk⟩⟩).toNat - 1 := by
        have he := chain_edge_mem hBuild v (ki - 1) hprev hprev2 hn_prev hn_ki_as_succ
        have htv := hτ ⟨⟨v, ⟨ki - 1, hprev⟩⟩, ⟨v, ⟨ki - 1 + 1, hprev2⟩⟩, 1⟩ he
        simp only [WtEdge.src, WtEdge.tgt, WtEdge.wt] at htv
        have : τ ⟨v, ⟨ki - 1 + 1, hprev2⟩⟩ = τ ⟨v, ⟨ki, hk⟩⟩ :=
          congrArg τ (congrArg (IncrEvent.mk v) (Fin.ext (by omega : (ki - 1 + 1 : ℕ) = ki)))
        rw [this] at htv; omega
      have hge := orbit_ge_at_τ hBuild τ hτ hPos hle v (ki - 1) hprev hn_prev
        ((τ ⟨v, ⟨ki, hk⟩⟩).toNat - 1) hτ_prev_le
      omega

private lemma guard_holds_at_timing_round {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (τ : IncrEvent V h → ℤ)
    (hτ : TimingValid ⟨edges⟩ τ)
    (hPos : ∀ e, τ e ≥ 1)
    (hle : configLE x y)
    (v : V) (ki : ℕ) (hk : ki < h)
    (hn : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩) :
    (N.guard v ⟨ki, hk⟩).holds
      (mkOrbit N x y τ ((τ ⟨v, ⟨ki, hk⟩⟩).toNat - 1)) := by
  intro lit hlit
  set T := (τ ⟨v, ⟨ki, hk⟩⟩).toNat
  cases lit with
  | lb u a =>
    simp only [IntervalLit.holds]
    by_cases hxa : a.val ≤ (x u).val
    · have hmv := mkOrbit_mono_trans N x y τ u (Nat.zero_le (T - 1))
      exact Fin.le_iff_val_le_val.mpr (by simp [mkOrbit] at hmv; have := Fin.val_le_of_le hmv; omega)
    · push_neg at hxa
      have hya : ¬(y u).val < a.val := build_ok_lit_lb hBuild v ki hk hn u a hlit hxa
      push_neg at hya
      have ha2 : a.val - 1 < h := by have := a.isLt; omega
      have hn_u : IncrEvent.needed x y ⟨u, ⟨a.val - 1, ha2⟩⟩ := by
        simp only [IncrEvent.needed, IncrEvent.v, IncrEvent.k]; constructor <;> omega
      have he := lb_edge_mem hBuild v ki hk u a hn hlit (by omega) (by omega) ⟨by omega, ha2⟩
      have htv := hτ ⟨⟨u, ⟨a.val - 1, ha2⟩⟩, ⟨v, ⟨ki, hk⟩⟩, 1⟩ he
      simp only [WtEdge.src, WtEdge.tgt, WtEdge.wt] at htv
      have hge := orbit_ge_at_τ hBuild τ hτ hPos hle u (a.val - 1) ha2 hn_u (T - 1) (by omega)
      exact Fin.le_iff_val_le_val.mpr (by omega)
  | ub u b =>
    simp only [IntervalLit.holds]
    by_cases hyb : (y u).val ≤ b.val
    · have hle_y := mkOrbit_val_le_y hBuild τ hτ hPos hle (T - 1) u
      exact Fin.le_iff_val_le_val.mpr (by omega)
    · push_neg at hyb
      have hxb : (x u).val ≤ b.val := by
        by_contra hc; push_neg at hc
        exact build_ok_lit_ub hBuild v ki hk hn u b hlit hc
      have hb_lt : b.val < h := by have := b.isLt; omega
      have hn_u : IncrEvent.needed x y ⟨u, ⟨b.val, hb_lt⟩⟩ := by
        simp only [IncrEvent.needed, IncrEvent.v, IncrEvent.k]; constructor <;> omega
      have he := ub_edge_mem hBuild v ki hk u b hn hlit (by omega) (by omega) hb_lt
      have htv := hτ ⟨⟨v, ⟨ki, hk⟩⟩, ⟨u, ⟨b.val, hb_lt⟩⟩, 0⟩ he
      simp only [WtEdge.src, WtEdge.tgt, WtEdge.wt] at htv
      have hle_b := orbit_le_before_τ hBuild τ hτ hPos hle u b.val hb_lt hn_u (T - 1) (by
        have := hPos ⟨u, ⟨b.val, hb_lt⟩⟩; omega)
      exact Fin.le_iff_val_le_val.mpr hle_b

private lemma mkOrbit_val_at_τ {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (τ : IncrEvent V h → ℤ)
    (hτ : TimingValid ⟨edges⟩ τ)
    (hPos : ∀ e, τ e ≥ 1)
    (hle : configLE x y)
    (v : V) (ki : ℕ) (hk : ki < h)
    (hn : IncrEvent.needed x y ⟨v, ⟨ki, hk⟩⟩) :
    (mkOrbit N x y τ ((τ ⟨v, ⟨ki, hk⟩⟩).toNat) v).val ≥ ki + 1 :=
  orbit_ge_at_τ hBuild τ hτ hPos hle v ki hk hn _ (le_refl _)

private lemma mkOrbit_le_y {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (τ : IncrEvent V h → ℤ)
    (hτ : TimingValid ⟨edges⟩ τ)
    (hPos : ∀ e, τ e ≥ 1)
    (hle : configLE x y) (n : ℕ) (v : V) :
    mkOrbit N x y τ n v ≤ y v := by
  exact Fin.le_iff_val_le_val.mpr (mkOrbit_val_le_y hBuild τ hτ hPos hle n v)

private lemma mkOrbit_ge_y {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (τ : IncrEvent V h → ℤ)
    (hτ : TimingValid ⟨edges⟩ τ)
    (hPos : ∀ e, τ e ≥ 1)
    (hle : configLE x y) (T : ℕ)
    (hT : ∀ e : IncrEvent V h, (τ e).toNat ≤ T) (v : V) :
    y v ≤ mkOrbit N x y τ T v := by
  by_cases hvy : (x v).val = (y v).val
  · have hmono := mkOrbit_mono_trans N x y τ v (Nat.zero_le T)
    simp only [mkOrbit] at hmono
    have hxv : x v = y v := Fin.ext hvy
    rw [← hxv]; exact hmono
  · have hlt : (x v).val < (y v).val := by
      have := hle v; omega
    have hmax : (y v).val - 1 < h := by omega
    have hn_last : IncrEvent.needed x y ⟨v, ⟨(y v).val - 1, hmax⟩⟩ := by
      simp only [IncrEvent.needed, IncrEvent.v, IncrEvent.k]; omega
    have hge := mkOrbit_val_at_τ hBuild τ hτ hPos hle v ((y v).val - 1) hmax hn_last
    have hτ_le := hT ⟨v, ⟨(y v).val - 1, hmax⟩⟩
    have hmono := mkOrbit_mono_trans N x y τ v
      (show (τ ⟨v, ⟨(y v).val - 1, hmax⟩⟩).toNat ≤ T by omega)
    have hge_T : (mkOrbit N x y τ T v).val ≥ (y v).val := by
      have := Fin.val_le_of_le hmono; omega
    exact Fin.le_iff_val_le_val.mpr hge_T

private lemma mkOrbit_reaches_y {h : ℕ}
    {N : CIUIFN V h} {x y : Config V h}
    {edges : List (WtEdge V h)}
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (τ : IncrEvent V h → ℤ)
    (hτ : TimingValid ⟨edges⟩ τ)
    (hPos : ∀ e, τ e ≥ 1)
    (hle : configLE x y) (T : ℕ)
    (hT : ∀ e : IncrEvent V h, (τ e).toNat ≤ T) :
    mkOrbit N x y τ T = y := by
  funext v
  exact le_antisymm
    (mkOrbit_le_y hBuild τ hτ hPos hle T v)
    (mkOrbit_ge_y hBuild τ hτ hPos hle T hT v)

theorem timing_to_orbit
    (hle : configLE x y)
    (edges : List (WtEdge V h))
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (τ : IncrEvent V h → ℤ)
    (hτ : TimingValid ⟨edges⟩ τ)
    (hPos : ∀ e, τ e ≥ 1) :
    N.reachable x y := by
  set T := tMax τ
  refine ⟨T, fun i => mkOrbit N x y τ i.val, fun t => mkSched N x y τ t.val, ?_, ?_, ?_⟩
  · simp [mkOrbit]
  · exact mkOrbit_reaches_y hBuild τ hτ hPos hle T (τ_le_tMax τ hPos)
  · intro t; simp [mkOrbit_succ]

theorem if_direction
    (hle : configLE x y)
    (edges : List (WtEdge V h))
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (hNPC : ¬hasPosCycle ⟨edges⟩) :
    N.reachable x y := by
  obtain ⟨τ, hτ, hPos⟩ := validTiming_of_noPosCycle_local ⟨edges⟩ hNPC
  exact timing_to_orbit N x y hle edges hBuild τ hτ hPos

end IfDir

section Main

variable {h : ℕ} (N : CIUIFN V h) (x y : Config V h)

theorem main_characterization
    (hle : configLE x y)
    (edges : List (WtEdge V h))
    (hBuild : buildECD N x y = BuildResult.ok edges) :
    N.reachable x y ↔ ¬hasPosCycle ⟨edges⟩ :=
  ⟨fun hR => onlyIf_direction N x y hR edges hBuild,
   fun hNPC => if_direction N x y hle edges hBuild hNPC⟩

end Main

section Makespan

variable {h : ℕ}

noncomputable def maxPathWt (G : EventDigraph V h) : ℕ :=
  Finset.univ.sup (fun v => maxPW G (Fintype.card (IncrEvent V h)) v)

theorem makespan_achieved (N : CIUIFN V h) (x y : Config V h)
    (hle : configLE x y)
    (edges : List (WtEdge V h))
    (hBuild : buildECD N x y = BuildResult.ok edges)
    (hNPC : ¬hasPosCycle ⟨edges⟩) :
    ∃ (T : ℕ) (orbit : Fin (T + 1) → Config V h)
      (sched : Fin T → Finset V),
      orbit ⟨0, by omega⟩ = x ∧
      orbit ⟨T, by omega⟩ = y ∧
      T = maxPathWt ⟨edges⟩ + 1 ∧
      (∀ (t : Fin T),
        orbit ⟨t.val + 1, by omega⟩ =
          asyncStep N.localF (orbit ⟨t.val, by omega⟩) (sched t)) := by
  set n := Fintype.card (IncrEvent V h)
  set τ0 : IncrEvent V h → ℤ := fun v => ↑(maxPW ⟨edges⟩ n v) + 1
  have hτ0 : TimingValid ⟨edges⟩ τ0 := by
    intro e he
    have := maxPW_succ_ge_add ⟨edges⟩ n he
    have h2 := maxPW_stabilizes ⟨edges⟩ hNPC e.tgt
    push_cast; linarith
  have hPos0 : ∀ e, τ0 e ≥ 1 := by intro e; simp only [τ0]; push_cast; omega
  set T := maxPathWt ⟨edges⟩ + 1
  refine ⟨T, fun i => mkOrbit N x y τ0 i.val, fun t => mkSched N x y τ0 t.val,
    ?_, ?_, ?_, ?_⟩
  · simp [mkOrbit]
  · apply mkOrbit_reaches_y hBuild τ0 hτ0 hPos0 hle T
    intro e
    simp only [T, maxPathWt, τ0, n, Int.toNat_natCast_add_one]
    exact Nat.add_le_add_right (Finset.le_sup (Finset.mem_univ e)) 1
  · rfl
  · intro t; simp [mkOrbit_succ]

end Makespan

end FreezingNetworks
