import WideGraphLift
import CompactClosure

open private back_chain from CompactClosure

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph
open CompactOmission (six_tree_absurd chain_from_chart trace_of_middle_replacement)

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
private theorem outside_core {n : ℕ} (f : Fin (n+1) ↪ V) (p : PathOn G {v | v ≠ f (Fin.last n)})
    {L R : List V} (split : p.vertices = L ++ (block f ++ R))
    {v : V} (hv : v ∈ L ∨ v ∈ R) (i : Fin (n+1)) : v ≠ f i := by
  intro eq
  have nd : (L ++ (block f ++ R)).Nodup := split ▸ p.nodup
  rcases block_cases f i with here|isLast
  · rcases hv with left|right
    · exact (List.nodup_append.mp nd).2.2 left (List.mem_append_left _ (eq.symm ▸ here))
    · exact (List.nodup_append.mp (List.nodup_append.mp nd).2.1).2.2 (eq.symm ▸ here) right
  · have h : v ∈ p.vertices := by rw [split]; simp only [List.mem_append]; tauto
    exact (p.covers _).mp h (eq.trans (congrArg f isLast))

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
private theorem between_flanks {n : ℕ} {f : Fin (n+1) ↪ V} (p : PathOn G {v | v ≠ f (Fin.last n)})
    {L R : List V} (split : p.vertices = L ++ (block f ++ R)) {l r : V}
    (lm : l ∈ L) (rm : r ∈ R) : l ≠ r := by
  have nd : (L ++ (block f ++ R)).Nodup := split ▸ p.nodup
  intro e
  exact (List.nodup_append.mp nd).2.2 lm (List.mem_append_right _ (e.symm ▸ rm))

private theorem pair_step (budget : Catalogue.treeNumber G ≤ 5)
    (noTrace : ¬ Catalogue.Traceable G)
    {n : ℕ} {f : Fin (n+1) ↪ V} {mate : Fin (n+1)} {e : Fin (n+1) → Fin (n+1) → Bool}
    (rules : FlankRules n e mate) (p : PathOn G {v | v ≠ f (Fin.last n)})
    (core : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true)
    (external : ∀ v, (∀ i, v ≠ f i) → ¬ G.Adj v (f (Fin.last n)) ∧ ¬ G.Adj v (f mate))
    (pos : 0 < n) {U R : List V} {l r : V} (split : p.vertices = (U ++ [l]) ++ (block f ++ r :: R)) :
    ProfileAt G f l rules.boundary ∧ ProfileAt G f r rules.boundary ∧ G.Adj l r := by
  have outsideL := outside_core f p split (v := l) (Or.inl (by simp))
  have outsideR := outside_core f p split (v := r) (Or.inr (by simp))
  have distinct := between_flanks p split (l := l) (r := r) (by simp) (by simp)
  obtain ⟨m,hm,hml⟩ := external_profile budget rules core outsideL (external _ outsideL).1 (external _ outsideL).2
  obtain ⟨q,hq,hqr⟩ := external_profile budget rules core outsideR (external _ outsideR).1 (external _ outsideR).2
  let b := decide (G.Adj l r)
  let x : Fin 2 ↪ V :=
    ⟨![l,r], by intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩
  have off (i : Fin (n+1)) (j : Fin 2) : x j ≠ f i := by
    fin_cases j
    · exact outsideL i
    · exact outsideR i
  let g := extend f x off
  have chart : ∀ i j, G.Adj (g i) (g j) ↔ pairEdge e m q b i j = true := by
    apply extension_chart core
    · intro j
      fin_cases j
      · exact hml
      · exact hqr
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [x,b,pairLinks,G.adj_comm r l]
  have seg : p.vertices = U ++ (l :: block f ++ [r]) ++ R := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
  have old : (l :: block f ++ [r]).Chain' G.Adj := (seg ▸ p.chain).left_of_append.right_of_append
  have lp : G.Adj l (f 0) := by
    apply (List.chain'_cons'.mp old).1
    simp [List.head?_append,block_head f pos]
  have qr : G.Adj r (f (rightEnd n)) := by
    have ch : ((l :: block f) ++ [r]).Chain' G.Adj := old
    apply G.symm
    apply (List.chain'_append.mp ch).2.2
    · have ne : block f ≠ [] := by
        intro nil
        have h := block_length f
        rw [nil] at h
        simp at h
        omega
      change (l :: block f).getLast? = some (f (rightEnd n))
      change ([l] ++ block f).getLast? = _
      rw [List.getLast?_append_of_ne_nil _ ne,block_last f pos]
    · rfl
  rcases rules.pair m q b hm hq ((hml _).mp lp) ((hqr _).mp qr) with
    ⟨T,tree⟩|⟨P,perm,route⟩|⟨eqM,eqN,link⟩
  · exact (six_tree_absurd budget chart tree).elim
  · have ch0 := chain_from_chart chart route
    have simpLeft : g ∘ Fin.castAdd 2 = (f : Fin (n+1) → V) := by
      funext i
      exact extend_left f x off i
    have e8 : g (Fin.natAdd (n+1) 0) = l := extend_right f x off 0
    have e9 : g (Fin.natAdd (n+1) 1) = r := extend_right f x off 1
    have ch : (l :: P.map f ++ [r]).Chain' G.Adj := by
      simpa only [pairOrder,List.map_cons,List.map_append,List.map_nil,List.map_map,simpLeft,e8,e9] using ch0
    have per : (l :: P.map f ++ [r]).Perm (f (Fin.last n) :: (l :: block f ++ [r])) := by
      exact ((block_perm f perm).append_right [r]).cons l |>.trans (List.Perm.swap (f (Fin.last n)) l _)
    exact (noTrace (trace_of_middle_replacement p seg (by simp) (by simp) (by simp)
      (by simp only [← List.cons_append,List.getLast?_append,List.getLast?_singleton,Option.some_or]) per ch)).elim
  · exact ⟨eqM ▸ hml,eqN ▸ hqr,of_decide_eq_true link⟩

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
private theorem front_chain {n : ℕ} {f : Fin (n+1) ↪ V} {mask : ℕ} {y l r : V} {H : List V}
    {P : List (Fin (n+1))} (same : ∀ v ∈ l :: H, ProfileAt G f v mask ∧ G.Adj v r)
    (preChain : (y :: l :: H).Chain' G.Adj)
    (ch : (y :: l :: P.map f ++ [r]).Chain' G.Adj) :
    ((y :: l :: H) ++ (P.map f ++ [r])).Chain' G.Adj := by
  apply preChain.append
  · exact ((List.chain'_cons'.mp ch).2).tail
  · intro u hu v hv
    have uH : u ∈ l :: H := List.mem_of_getLast? (by
      have eq := Option.mem_def.mp hu
      simpa only [List.getLast?_cons_cons] using eq)
    have join := (List.chain'_cons'.mp (List.chain'_cons'.mp ch).2).1 v hv
    rcases List.mem_append.mp (List.mem_of_mem_head? hv) with inner|right
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp inner
      exact ((same u uH).1 i).mpr (((same l (by simp)).1 i).mp join)
    · have eq : v = r := by simpa only [List.mem_singleton] using right
      exact eq ▸ (same u uH).2

private theorem advance_step (budget : Catalogue.treeNumber G ≤ 5)
    (noTrace : ¬ Catalogue.Traceable G)
    {n : ℕ} {f : Fin (n+1) ↪ V} {mate : Fin (n+1)} {e : Fin (n+1) → Fin (n+1) → Bool}
    (rules : FlankRules n e mate) (p : PathOn G {v | v ≠ f (Fin.last n)})
    (core : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true)
    (external : ∀ v, (∀ i, v ≠ f i) → ¬ G.Adj v (f (Fin.last n)) ∧ ¬ G.Adj v (f mate))
    {U H R : List V} {y l r : V}
    (split : p.vertices = (U ++ (y :: l :: H)) ++ (block f ++ r :: R))
    (same : ∀ v ∈ l :: H, ProfileAt G f v rules.boundary ∧ G.Adj v r)
    (right : ProfileAt G f r rules.boundary) :
    ProfileAt G f y rules.boundary ∧ G.Adj y r := by
  have offL := outside_core f p split (v := l) (Or.inl (by simp))
  have offR := outside_core f p split (v := r) (Or.inr (by simp))
  have offY := outside_core f p split (v := y) (Or.inl (by simp))
  have lr := between_flanks p split (l := l) (r := r) (by simp) (by simp)
  have yr := between_flanks p split (l := y) (r := r) (by simp) (by simp)
  have ly : l ≠ y := by
    have nd : (y :: l :: H).Nodup := by
      have nd' : ((U ++ (y :: l :: H)) ++ (block f ++ r :: R)).Nodup := split ▸ p.nodup
      exact (List.nodup_append.mp (List.nodup_append.mp nd').1).2.1
    exact fun e => (List.nodup_cons.mp nd).1 (by simp [e])
  obtain ⟨m,hm,hy⟩ := external_profile budget rules core offY (external _ offY).1 (external _ offY).2
  have hl := same l (by simp)
  have pre : (y :: l :: H).Chain' G.Adj := (split ▸ p.chain).left_of_append.right_of_append
  have lyEdge : G.Adj l y := (List.chain'_cons.mp pre).1.symm
  let b := decide (G.Adj y r)
  let x : Fin 3 ↪ V :=
    ⟨![l,r,y], by intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩
  have off (i : Fin (n+1)) (j : Fin 3) : x j ≠ f i := by
    fin_cases j
    · exact offL i
    · exact offR i
    · exact offY i
  let g := extend f x off
  have chart : ∀ i j, G.Adj (g i) (g j) ↔ stepEdge e rules.boundary m b i j = true := by
    apply extension_chart core
    · intro j
      fin_cases j
      · exact hl.1
      · exact right
      · exact hy
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [x,b,stepLinks,hl.2,lyEdge,G.adj_comm r l,G.adj_comm y l,
        G.adj_comm r y]
  rcases rules.step m b hm with ⟨T,tree⟩|⟨P,front,perm,route⟩|⟨eq,link⟩
  · exact (six_tree_absurd budget chart tree).elim
  · have segment : p.vertices = U ++ ((y :: l :: H) ++ block f ++ [r]) ++ R := by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
    let W := P.map f
    have pW : W.Perm (f (Fin.last n) :: block f) := block_perm f perm
    have onFront : ((y :: l :: H) ++ W ++ [r]).Perm
        (f (Fin.last n) :: ((y :: l :: H) ++ block f ++ [r])) := by
      exact ((pW.append_left (y :: l :: H)).append_right [r]).trans (by
        simpa only [List.append_assoc,List.cons_append] using
          (List.perm_middle (a := f (Fin.last n)) (l₁ := y :: l :: H) (l₂ := block f ++ [r])))
    have sameMap : g ∘ Fin.castAdd 3 = (f : Fin (n+1) → V) := by
      funext i
      exact extend_left f x off i
    have e8 : g (Fin.natAdd (n+1) 0) = l := extend_right f x off 0
    have e9 : g (Fin.natAdd (n+1) 1) = r := extend_right f x off 1
    have e10 : g (Fin.natAdd (n+1) 2) = y := extend_right f x off 2
    cases front
    · have ch : ((y :: W) ++ [l,r]).Chain' G.Adj := by
        simpa only [stepOrder,Bool.false_eq_true,if_false,List.map_cons,List.map_append,List.map_nil,
          List.map_map,sameMap,e8,e9,e10,List.cons_append,W] using chain_from_chart chart route
      have full := back_chain (fun v hv => (same v hv).2) pre.tail ch
      have move : (((y :: W) ++ (l :: H)) ++ [r]).Perm ((y :: l :: H) ++ W ++ [r]) := by
        simpa only [List.cons_append] using
          (((List.perm_append_comm (l₁ := W) (l₂ := l :: H)).cons y).append_right [r])
      exact (noTrace (trace_of_middle_replacement p segment (by simp) (by simp) (by simp)
        (by simp only [← List.cons_append,List.getLast?_append,List.getLast?_singleton,Option.some_or]) (move.trans onFront) full)).elim
    · have ch : (y :: l :: W ++ [r]).Chain' G.Adj := by
        simpa only [stepOrder,if_true,List.map_cons,List.map_append,List.map_nil,List.map_map,
          sameMap,e8,e9,e10,W] using chain_from_chart chart route
      have full := front_chain same pre ch
      exact (noTrace (trace_of_middle_replacement p segment (by simp) (by simp) (by simp)
        (by simp only [← List.cons_append,List.getLast?_append,List.getLast?_singleton,Option.some_or]) onFront
        (by simpa only [List.append_assoc] using full))).elim
  · exact ⟨eq ▸ hy,of_decide_eq_true link⟩

/-- Generalized form of the compact argument. The two flanks may have arbitrary length. -/
theorem traceable_of_flank_rules {n : ℕ} (pos : 0 < n)
    (budget : Catalogue.treeNumber G ≤ 5)
    {f : Fin (n+1) ↪ V} {mate : Fin (n+1)} {e : Fin (n+1) → Fin (n+1) → Bool}
    (rules : FlankRules n e mate) (p : PathOn G {v | v ≠ f (Fin.last n)})
    (core : ∀ i j, G.Adj (f i) (f j) ↔ e i j = true)
    (external : ∀ v, (∀ i, v ≠ f i) → ¬ G.Adj v (f (Fin.last n)) ∧ ¬ G.Adj v (f mate))
    (preP : f 0 ∈ p.predecessors) (succQ : f (rightEnd n) ∈ p.rev.predecessors)
    (L R : List V) (split : p.vertices = L ++ block f ++ R) :
    Catalogue.Traceable G := by
  classical
  by_contra noTrace
  have chord := (core _ _).mpr rules.outerChord
  have lNe : L ≠ [] := by
    rintro rfl
    have opt : p.vertices.head? = some (f 0) := by simp [split,List.head?_append,block_head f pos]
    rw [List.head?_eq_head p.nonempty] at opt
    have first : p.first = f 0 := Option.some.inj opt
    apply p.rev.terminalFlanks_independent noTrace (f 0) _ _
      (Finset.mem_insert_of_mem succQ) chord
    rw [PathOn.terminalFlanks,p.rev_last,first]
    exact Finset.mem_insert_self _ _
  have rNe : R ≠ [] := by
    rintro rfl
    have opt : p.vertices.getLast? = some (f (rightEnd n)) := by
      simp [split,List.getLast?_append,block_last f pos]
    rw [List.getLast?_eq_getLast p.nonempty] at opt
    have last : p.last = f (rightEnd n) := Option.some.inj opt
    apply p.terminalFlanks_independent noTrace (f 0) (Finset.mem_insert_of_mem preP)
      (f (rightEnd n)) _ chord
    rw [PathOn.terminalFlanks,last]
    exact Finset.mem_insert_self _ _
  obtain ⟨r,tail,rfl⟩ := List.exists_cons_of_ne_nil rNe
  have leftForm : ∃ U l, L = U ++ [l] :=
    ⟨L.dropLast,L.getLast lNe,(List.dropLast_append_getLast lNe).symm⟩
  obtain ⟨U,l,rfl⟩ := leftForm
  have normalized : p.vertices = (U ++ [l]) ++ (block f ++ r :: tail) := by
    simpa only [List.append_assoc] using split
  obtain ⟨lh,rh,link⟩ := pair_step budget noTrace rules p core external pos normalized
  have eliminate (A : List V) (v : V) (S : List V)
      (form : p.vertices = (A ++ (v :: S)) ++ (block f ++ r :: tail))
      (common : ∀ w ∈ v :: S, ProfileAt G f w rules.boundary ∧ G.Adj w r) : False := by
    induction A using List.reverseRecOn generalizing v S with
    | nil =>
      have eq : p.first = v := by
        have hh : p.vertices.head? = some v := by simp [form]
        rw [List.head?_eq_head p.nonempty] at hh
        exact Option.some.inj hh
      have start : v ∈ p.rev.terminalFlanks := by
        rw [PathOn.terminalFlanks,PathOn.rev_last,eq]
        exact Finset.mem_insert_self _ _
      exact p.rev.terminalFlanks_independent noTrace v start _
        (Finset.mem_insert_of_mem succQ) (((common v (by simp)).1 _).mpr rules.boundaryRight)
    | append_singleton B y ih =>
      have nn : p.vertices = (B ++ (y :: v :: S)) ++ (block f ++ r :: tail) := by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using form
      have good := advance_step budget noTrace rules p core external nn common rh
      apply ih y (v :: S) nn
      intro w wm
      rcases List.mem_cons.mp wm with rfl|hs
      · exact good
      · exact common w hs
  exact eliminate U l [] normalized (by simpa only [List.mem_singleton,forall_eq] using And.intro lh link)

#print axioms traceable_of_flank_rules

end Graffiti199Depleted.WiderOmission
