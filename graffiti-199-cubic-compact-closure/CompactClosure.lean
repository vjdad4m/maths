import CompactExtensionLift
import CompactPairRows
import CompactStepRows

open private succ_mem from CompactOmission
open private middle_cases from CompactGraphLifts

namespace Graffiti199Depleted.CompactOmission

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
private theorem outside_core (f : Fin 8 ↪ V) (p : PathOn G {v | v ≠ f 7})
    {L R : List V} (split : p.vertices = L ++ (middle f ++ R))
    {v : V} (hv : v ∈ L ∨ v ∈ R) (i : Fin 8) : v ≠ f i := by
  intro eq
  have nd : (L ++ (middle f ++ R)).Nodup := split ▸ p.nodup
  rcases middle_cases f i with here|isLast
  · rcases hv with left|right
    · exact (List.nodup_append.mp nd).2.2 left (List.mem_append_left _ (eq.symm ▸ here))
    · exact (List.nodup_append.mp (List.nodup_append.mp nd).2.1).2.2 (eq.symm ▸ here) right
  · have h : v ∈ p.vertices := by rw [split]; simp only [List.mem_append]; tauto
    exact (p.covers _).mp h (eq.trans (congrArg f isLast))

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
private theorem between_flanks {f : Fin 8 ↪ V} (p : PathOn G {v | v ≠ f 7})
    {L R : List V} (split : p.vertices = L ++ (middle f ++ R)) {l r : V}
    (lm : l ∈ L) (rm : r ∈ R) : l ≠ r := by
  have nd : (L ++ (middle f ++ R)).Nodup := split ▸ p.nodup
  intro e
  exact (List.nodup_append.mp nd).2.2 lm (List.mem_append_right _ (e.symm ▸ rm))

private theorem pair_step (budget : Catalogue.treeNumber G ≤ 5)
    (noTrace : ¬ Catalogue.Traceable G)
    {f : Fin 8 ↪ V} {k : Fin 6} (p : PathOn G {v | v ≠ f 7})
    (core : ∀ i j, G.Adj (f i) (f j) ↔ adjacent (coreRows k) i j = true)
    (dz : G.degree (f 7) = 3) (dm : G.degree (f (mate k)) = 3)
    {U R : List V} {l r : V} (split : p.vertices = (U ++ [l]) ++ (middle f ++ r :: R)) :
    ProfileAt G f l (boundary k) ∧ ProfileAt G f r (boundary k) ∧ G.Adj l r := by
  have outsideL := outside_core f p split (v := l) (Or.inl (by simp))
  have outsideR := outside_core f p split (v := r) (Or.inr (by simp))
  have distinct := between_flanks p split (l := l) (r := r) (by simp) (by simp)
  obtain ⟨m,hm,hml⟩ := external_profile budget core dz dm outsideL
  obtain ⟨n,hn,hnr⟩ := external_profile budget core dz dm outsideR
  let b := decide (G.Adj l r)
  let x : Fin 2 ↪ V :=
    ⟨![l,r], by intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩
  have off (i : Fin 8) (j : Fin 2) : x j ≠ f i := by
    fin_cases j
    · exact outsideL i
    · exact outsideR i
  let g := extend f x off
  have chart : ∀ i j, G.Adj (g i) (g j) ↔ pairEdge k m n b i j = true := by
    apply extension_chart core
    · intro j
      fin_cases j
      · exact hml
      · exact hnr
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [x,b,G.adj_comm r l]
  have seg : p.vertices = U ++ (l :: middle f ++ [r]) ++ R := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
  have old : (l :: middle f ++ [r]).Chain' G.Adj := (seg ▸ p.chain).left_of_append.right_of_append
  have lp : G.Adj l (f 0) := by
    exact (List.chain'_cons.mp (show
      (l :: f 0 :: ([f 1,f 2,f 3,f 4,f 5,f 6,r] : List V)).Chain' G.Adj from old)).1
  have qr : G.Adj r (f 6) := by
    have tail : ([f 6,r] : List V).Chain' G.Adj := by
      exact (show ([l,f 0,f 1,f 2,f 3,f 4,f 5] ++ [f 6,r]).Chain' G.Adj from old).right_of_append
    exact (List.chain'_pair.mp tail).symm
  rcases paired_extension k m n b hm hn ((hml _).mp lp) ((hnr _).mp qr) with
    ⟨T,tree⟩|⟨P,perm,route⟩|⟨eqM,eqN,link⟩
  · exact (six_tree_absurd budget chart tree).elim
  · have ch0 := chain_from_chart chart route
    have simpLeft : g ∘ Fin.castAdd 2 = (f : Fin 8 → V) := by
      funext i
      exact extend_left f x off i
    have e8 : g 8 = l := extend_right f x off 0
    have e9 : g 9 = r := extend_right f x off 1
    have ch : (l :: P.map f ++ [r]).Chain' G.Adj := by
      simpa only [List.map_cons,List.map_append,List.map_nil,List.map_map,simpLeft,e8,e9] using ch0
    have per : (l :: P.map f ++ [r]).Perm (f 7 :: (l :: middle f ++ [r])) := by
      exact ((core_perm f perm).append_right [r]).cons l |>.trans (List.Perm.swap (f 7) l _)
    exact (noTrace (trace_of_middle_replacement p seg (by simp) (by simp) (by simp)
      (by simp only [← List.cons_append,List.getLast?_append,List.getLast?_singleton,Option.some_or]) per ch)).elim
  · exact ⟨eqM ▸ hml,eqN ▸ hnr,of_decide_eq_true link⟩

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
private theorem front_chain {f : Fin 8 ↪ V} {k : Fin 6} {y l r : V} {H : List V}
    {P : List (Fin 8)} (same : ∀ v ∈ l :: H, ProfileAt G f v (boundary k) ∧ G.Adj v r)
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

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
private theorem back_chain {y l r : V} {H W : List V}
    (same : ∀ v ∈ l :: H, G.Adj v r)
    (left : (l :: H).Chain' G.Adj) (ch : ((y :: W) ++ [l,r]).Chain' G.Adj) :
    ((y :: W) ++ (l :: H) ++ [r]).Chain' G.Adj := by
  have j := (List.chain'_append.mp ch).2.2
  have built : ((y :: W) ++ (l :: H)).Chain' G.Adj := ch.left_of_append.append left (by
    intro u hu v hv
    have eq : l = v := by simpa using hv
    exact eq ▸ j u hu l rfl)
  apply built.append (List.chain'_singleton r)
  intro u hu v hv
  have eq : r = v := by simpa using hv
  have mem : u ∈ l :: H := by
    apply List.mem_of_getLast?
    change _ = some u at hu
    rw [List.getLast?_append_of_ne_nil _ (by simp)] at hu
    exact hu
  exact eq ▸ same u mem

private theorem advance_step (budget : Catalogue.treeNumber G ≤ 5)
    (noTrace : ¬ Catalogue.Traceable G)
    {f : Fin 8 ↪ V} {k : Fin 6} (p : PathOn G {v | v ≠ f 7})
    (core : ∀ i j, G.Adj (f i) (f j) ↔ adjacent (coreRows k) i j = true)
    (dz : G.degree (f 7) = 3) (dm : G.degree (f (mate k)) = 3)
    {U H R : List V} {y l r : V}
    (split : p.vertices = (U ++ (y :: l :: H)) ++ (middle f ++ r :: R))
    (same : ∀ v ∈ l :: H, ProfileAt G f v (boundary k) ∧ G.Adj v r)
    (right : ProfileAt G f r (boundary k)) :
    ProfileAt G f y (boundary k) ∧ G.Adj y r := by
  have offL := outside_core f p split (v := l) (Or.inl (by simp))
  have offR := outside_core f p split (v := r) (Or.inr (by simp))
  have offY := outside_core f p split (v := y) (Or.inl (by simp))
  have lr := between_flanks p split (l := l) (r := r) (by simp) (by simp)
  have yr := between_flanks p split (l := y) (r := r) (by simp) (by simp)
  have ly : l ≠ y := by
    have nd : (y :: l :: H).Nodup := by
      have nd' : ((U ++ (y :: l :: H)) ++ (middle f ++ r :: R)).Nodup := split ▸ p.nodup
      exact (List.nodup_append.mp (List.nodup_append.mp nd').1).2.1
    exact fun e => (List.nodup_cons.mp nd).1 (by simp [e])
  obtain ⟨m,hm,hy⟩ := external_profile budget core dz dm offY
  have hl := same l (by simp)
  have pre : (y :: l :: H).Chain' G.Adj := (split ▸ p.chain).left_of_append.right_of_append
  have lyEdge : G.Adj l y := (List.chain'_cons.mp pre).1.symm
  let b := decide (G.Adj y r)
  let x : Fin 3 ↪ V :=
    ⟨![l,r,y], by intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩
  have off (i : Fin 8) (j : Fin 3) : x j ≠ f i := by
    fin_cases j
    · exact offL i
    · exact offR i
    · exact offY i
  let g := extend f x off
  have chart : ∀ i j, G.Adj (g i) (g j) ↔ stepEdge k m b i j = true := by
    apply extension_chart core
    · intro j
      fin_cases j
      · exact hl.1
      · exact right
      · exact hy
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [x,b,hl.2,lyEdge,G.adj_comm r l,G.adj_comm y l,
        G.adj_comm r y]
  rcases next_extension k m b hm with ⟨T,tree⟩|⟨P,front,perm,route⟩|⟨eq,link⟩
  · exact (six_tree_absurd budget chart tree).elim
  · have segment : p.vertices = U ++ ((y :: l :: H) ++ middle f ++ [r]) ++ R := by
      simpa only [List.append_assoc,List.cons_append,List.nil_append] using split
    let W := P.map f
    have pW : W.Perm (f 7 :: middle f) := core_perm f perm
    have onFront : ((y :: l :: H) ++ W ++ [r]).Perm
        (f 7 :: ((y :: l :: H) ++ middle f ++ [r])) := by
      exact ((pW.append_left (y :: l :: H)).append_right [r]).trans (by
        simpa only [List.append_assoc,List.cons_append] using
          (List.perm_middle (a := f 7) (l₁ := y :: l :: H) (l₂ := middle f ++ [r])))
    have sameMap : g ∘ Fin.castAdd 3 = (f : Fin 8 → V) := by
      funext i
      exact extend_left f x off i
    have e8 : g 8 = l := extend_right f x off 0
    have e9 : g 9 = r := extend_right f x off 1
    have e10 : g 10 = y := extend_right f x off 2
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

/-- With the three independent neighbors of the omitted cubic vertex in
alternate positions of a seven-vertex block, one cubic neighbor suffices
to force traceability under the induced-tree bound. -/
theorem traceable_of_compact_cubic_omission
    (budget : Catalogue.treeNumber G ≤ 5) (f : Fin 8 ↪ V)
    (p : PathOn G {v | v ≠ f 7}) (L R : List V)
    (split : p.vertices = L ++ middle f ++ R)
    (z1 : G.Adj (f 7) (f 1)) (z3 : G.Adj (f 7) (f 3)) (z5 : G.Adj (f 7) (f 5))
    (off13 : ¬ G.Adj (f 1) (f 3)) (off15 : ¬ G.Adj (f 1) (f 5))
    (off35 : ¬ G.Adj (f 3) (f 5)) (dz : G.degree (f 7) = 3)
    (cubic : G.degree (f 1) = 3 ∨ G.degree (f 3) = 3 ∨ G.degree (f 5) = 3) :
    Catalogue.Traceable G := by
  classical
  by_contra noTrace
  obtain ⟨_,lNe,rNe,row,rowOk,H⟩ :=
    compact_cubic_omission_rows noTrace budget f p L R split z1 z3 z5 off13 off15 off35 cubic
  obtain ⟨k,rfl⟩ := allowed_core_row row rowOk
  have dm := cubic_on_core f H cubic
  have succQ : f 6 ∈ p.rev.predecessors := succ_mem
    (L := L ++ [f 0,f 1,f 2,f 3,f 4]) (R := R)
    (by simpa only [middle,List.append_assoc,List.cons_append,List.nil_append] using split) z5
  obtain ⟨r,tail,rfl⟩ := List.exists_cons_of_ne_nil rNe
  have leftForm : ∃ U l, L = U ++ [l] :=
    ⟨L.dropLast,L.getLast lNe,(List.dropLast_append_getLast lNe).symm⟩
  obtain ⟨U,l,rfl⟩ := leftForm
  have normalized : p.vertices = (U ++ [l]) ++ (middle f ++ r :: tail) := by
    simpa only [List.append_assoc] using split
  obtain ⟨lh,rh,link⟩ := pair_step budget noTrace p H dz dm normalized
  have eliminate (A : List V) (v : V) (S : List V)
      (form : p.vertices = (A ++ (v :: S)) ++ (middle f ++ r :: tail))
      (common : ∀ w ∈ v :: S, ProfileAt G f w (boundary k) ∧ G.Adj w r) : False := by
    induction A using List.reverseRecOn generalizing v S with
    | nil =>
      have eq : p.first = v := by
        have hh : p.vertices.head? = some v := by simp [form]
        rw [List.head?_eq_head p.nonempty] at hh
        exact Option.some.inj hh
      have start : v ∈ p.rev.terminalFlanks := by
        rw [PathOn.terminalFlanks,PathOn.rev_last,eq]
        exact Finset.mem_insert_self _ _
      exact p.rev.terminalFlanks_independent noTrace v start (f 6)
        (Finset.mem_insert_of_mem succQ) (((common v (by simp)).1 6).mpr (boundary_outer k))
    | append_singleton B y ih =>
      have nn : p.vertices = (B ++ (y :: v :: S)) ++ (middle f ++ r :: tail) := by
        simpa only [List.append_assoc,List.cons_append,List.nil_append] using form
      have good := advance_step budget noTrace p H dz dm nn common rh
      apply ih y (v :: S) nn
      intro w wm
      rcases List.mem_cons.mp wm with rfl|hs
      · exact good
      · exact common w hs
  exact eliminate U l [] normalized (by simpa only [List.mem_singleton,forall_eq] using And.intro lh link)

#print axioms traceable_of_compact_cubic_omission

end Graffiti199Depleted.CompactOmission
