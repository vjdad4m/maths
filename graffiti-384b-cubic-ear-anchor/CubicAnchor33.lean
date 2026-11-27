import AnchorCut33

namespace Graffiti384b.EarAnchor
open Finset SimpleGraph CliquePivot33 EarExchange33
open private Repair.triangles_le_choose Repair.full_nbr Repair.nbr_mono from Repair384b
open private EarExchange33.count_insert from Exchange33
open private TrianglePrune.triangle_iff from TrianglePrune384b
open private OneEar.deg2 from OneEarFinish384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

theorem full_neighbors {v : V} (d : H.degree v=3) (s : trianglesAt H v=3)
    {p q : V} (vp : H.Adj v p) (vq : H.Adj v q) (ne : p≠q) : H.Adj p q := by
  let S := (H.neighborFinset v).powersetCard 2
  let T := S.filter (fun k => ∀ x∈k,∀ y∈k,x≠y → H.Adj x y)
  have st : S.card=3 := by simp only [S,card_powersetCard,card_neighborFinset_eq_degree,d]; decide
  have tt : T.card=3 := s
  have eq : T=S := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have pair : ({p,q} : Finset V)∈S := mem_powersetCard.mpr
    ⟨insert_subset ((H.mem_neighborFinset _ _).mpr vp) (singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr vq)),card_pair ne⟩
  have all := (mem_filter.mp (show ({p,q} : Finset V)∈T from eq ▸ pair)).2
  exact all p (mem_insert_self ..) q (mem_insert_of_mem (mem_singleton_self _)) ne

theorem diamond {e a c : V} (de : H.degree e=2) (da : H.degree a=3) (ea : H.Adj e a)
    (ec : H.Adj e c) (ac : H.Adj a c) (pos : ∀ v,0<trianglesAt H v)
    (inj : Function.Injective (trianglesAt H)) :
    ∃ w,w∈outside e a c ∧ H.Adj a w ∧ H.Adj c w ∧ H.neighborFinset e={a,c} ∧
      H.neighborFinset a={e,c,w} ∧ trianglesAt H e=1 ∧ trianglesAt H a=2 := by
  have sub : ({a,c} : Finset V)⊆H.neighborFinset e :=
    insert_subset ((H.mem_neighborFinset _ _).mpr ea) (singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr ec))
  have ear := (eq_of_subset_of_card_le sub (by rw [card_neighborFinset_eq_degree,de,card_pair ac.ne])).symm
  obtain ⟨w,wm,miss⟩ := exists_mem_not_mem_of_card_lt_card (show ({e,c} : Finset V).card<(H.neighborFinset a).card by
    rw [card_pair ec.ne,card_neighborFinset_eq_degree,da]; decide)
  have aw := (H.mem_neighborFinset _ _).mp wm
  have ne : w≠e ∧ w≠c := by simpa [not_or] using miss
  have no : ¬H.Adj w e := by
    intro rel
    have h := (H.mem_neighborFinset _ _).mpr rel.symm
    rw [ear] at h; simp [aw.ne.symm,ne.2] at h
  have subA : ({e,c,w} : Finset V)⊆H.neighborFinset a :=
    insert_subset ((H.mem_neighborFinset _ _).mpr ea.symm) (insert_subset ((H.mem_neighborFinset _ _).mpr ac) (singleton_subset_iff.mpr wm))
  have root := (eq_of_subset_of_card_le subA (by simp [card_neighborFinset_eq_degree,da,ec.ne,ne.1.symm,ne.2.symm])).symm
  have low := Repair.triangles_le_choose H e
  rw [de,Nat.choose_self] at low
  have one : trianglesAt H e=1 := by have := pos e; omega
  have diff : trianglesAt H a≠1 := fun h => ea.ne (inj (one.trans h.symm))
  have two : 2≤trianglesAt H a := by have := pos a; omega
  obtain ⟨u,au,wu⟩ := PositiveCore33.cubic_supported H da two aw
  have m := (H.mem_neighborFinset _ _).mpr au
  rw [root] at m
  have cw : H.Adj c w := by
    rcases (show u=e ∨ u=c ∨ u=w by simpa using m) with rfl|rfl|rfl
    · exact (no wu).elim
    · exact wu.symm
    · exact (H.loopless _ wu).elim
  have cap := Repair.triangles_le_choose H a
  rw [da] at cap
  have cap' : trianglesAt H a≤3 := cap
  have nthree : trianglesAt H a≠3 := fun s => no (full_neighbors H da s aw ea.symm ne.1)
  exact ⟨w,outside_mem.mpr ⟨ne.1,aw.ne.symm,ne.2⟩,aw,cw,ear,root,one,by omega⟩

private theorem sees_in_clique {C : Finset V} {k : ℕ} (cl : H.IsNClique k C) {v : V} (m : v∈C) :
    k-1≤H.degree v := by
  have sub : C.erase v⊆H.neighborFinset v := fun u um =>
    (H.mem_neighborFinset _ _).mpr (cl.1 m (erase_subset _ _ um) (mem_erase.mp um).1.symm)
  have le := card_le_card sub
  rwa [card_erase_of_mem m,cl.2,card_neighborFinset_eq_degree] at le

omit [Fintype V] [DecidableEq V] in
theorem induced_degree {W : Finset V} (v : W) :
    (H.induce (W : Set V)).degree v=nbr H v.val W := by
  let J := H.induce (W : Set V)
  let emb : W ↪ V := Function.Embedding.subtype _
  change (J.neighborFinset v).card=(W.filter (H.Adj v.val)).card
  rw [← card_map (f:=emb)]
  apply congrArg Finset.card
  ext u
  constructor
  · intro m; obtain ⟨x,xm,rfl⟩ := mem_map.mp m
    exact mem_filter.mpr ⟨x.property,(J.mem_neighborFinset _ _).mp xm⟩
  · intro m
    let x : W := ⟨u,(mem_filter.mp m).1⟩
    exact mem_map.mpr ⟨x,(J.mem_neighborFinset _ _).mpr (mem_filter.mp m).2,rfl⟩

private theorem part {e a c w : V} (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (ear : H.neighborFinset e={a,c}) (root : H.neighborFinset a={e,c,w})
    {v : V} (vm : v∈outside e a c) :
    nbr H v (outside e a c)+(if v=w then 1 else 0)+(if H.Adj v c then 1 else 0)=H.degree v := by
  classical
  obtain ⟨_,va,vc⟩ := outside_mem.mp vm
  have en : ¬H.Adj v e := by
    intro rel; have h := (H.mem_neighborFinset _ _).mpr rel.symm
    rw [ear] at h; simp [va,vc] at h
  have iffA : H.Adj v a ↔ v=w := by
    rw [adj_comm,← H.mem_neighborFinset,root]; simp [(outside_mem.mp vm).1,vc]
  have split := Repair.full_nbr H v (outside e a c)
  have endset : (outside e a c)ᶜ={e,a,c} := compl_compl _
  rw [endset] at split
  have p := EarExchange33.count_insert H e v (S:={a,c}) (by simp [ea.ne,ec.ne])
  have q := EarExchange33.count_insert H a v (S:={c}) (by simp [ac.ne])
  have z := EarExchange33.count_insert H c v (S:=∅) (not_mem_empty _)
  simp only [nbr,filter_empty,card_empty,Nat.zero_add] at z
  simp only [if_neg en,Nat.add_zero] at p
  simp only [iffA] at q
  change nbr H v {c}=(if H.Adj v c then 1 else 0) at z
  omega

/-- A failed attachment at a cubic ear anchor forces a specific second cubic
at the opposite anchor. Deleting the original ear triangle gives an induced
29-vertex graph with ordinary 2-domination number exactly 15. -/
theorem cubic_failure {e a c : V} (de : H.degree e=2) (da : H.degree a=3)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (n : Fintype.card V=32) (g : gamma H=16) (tight : Tight H {a})
    {C : Finset V} (cl : H.IsNClique 5 C) :
    let W := outside e a c
    W.card=29 ∧ gamma (H.induce (W : Set V))=15 ∧
    ∃ v∈W,H.degree v=3 ∧ trianglesAt H v=3 ∧ H.Adj c v ∧ nbr H v W=2 ∧
      (∀ u∈W,u≠v → 3≤nbr H u W) ∧ (∀ u∈W,H.Adj v u → H.Adj c u) := by
  classical
  let W := outside e a c
  change W.card=29 ∧ gamma (H.induce (W : Set V))=15 ∧ _
  obtain ⟨w,wm,_,cw,ear,root,one,two⟩ := diamond H de da ea ec ac pos inj
  have sz : W.card=29 := by simp [W,outside,card_compl,ea.ne,ec.ne,ac.ne,n]
  have an : a∉C := fun m => by have := sees_in_clique H cl m; omega
  have en : e∉C := fun m => by have := sees_in_clique H cl m; omega
  have can := (EarOnClique33.cubic_root_cliques H da de ac.ne ea ec pos inj tight cl).2 w
    (outside_mem.mp wm).1 ((H.mem_neighborFinset _ _).mp (root ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))) cw
  have wc := can.1
  have cc := can.2.resolve_left an
  let K := C.erase c
  have kc : H.IsNClique 4 K := ⟨fun _ u _ v ne => cl.1 (erase_subset _ _ u) (erase_subset _ _ v) ne,
    by rw [show K=C.erase c from rfl,card_erase_of_mem cc,cl.2]⟩
  have kw : K⊆W := by
    intro x xm; have mc := erase_subset _ _ xm
    exact outside_mem.mpr ⟨fun h => en (h ▸ mc),fun h => an (h ▸ mc),(mem_erase.mp xm).1⟩
  have allc (u : V) (um : u∈K) : H.Adj c u := cl.1 cc (erase_subset _ _ um) (mem_erase.mp um).1.symm
  have wk : w∈K := mem_erase.mpr ⟨cw.ne.symm,wc⟩
  have wbig : 3≤nbr H w W := by
    have inc : K.erase w⊆W.filter (H.Adj w) := fun x xm => mem_filter.mpr
      ⟨kw (erase_subset _ _ xm),kc.1 wk (erase_subset _ _ xm) (mem_erase.mp xm).1.symm⟩
    have le := card_le_card inc; rw [card_erase_of_mem wk,kc.2] at le; exact le
  have fail : ¬∃ D,Exchange H a D := fun h => (EarExchange33.exchange_iff H a (by omega)).mpr h tight
  have existsLow : ∃ v∈W,nbr H v W≤2 := by
    apply Classical.byContradiction; intro none
    have minimum (v : V) (vm : v∈W) : 3≤nbr H v W := by
      have no : ¬nbr H v W≤2 := fun h => none ⟨v,vm,h⟩; omega
    obtain ⟨X,cov,meet,sm⟩ := guarded_cut H kc kw allc minimum
    exact fail ((exchange_iff_guarded H ear ea ec ac n g).mpr ⟨X,cov,meet,by omega⟩)
  have low {u : V} (um : u∈W) (small : nbr H u W≤2) :
      H.degree u=3 ∧ trianglesAt H u=3 ∧ H.Adj c u ∧ nbr H u W=2 := by
    have uw : u≠w := fun h => by subst u; omega
    have par := part H ea ec ac ear root um
    change nbr H u W+(if u=w then 1 else 0)+(if H.Adj u c then 1 else 0)=H.degree u at par
    rw [if_neg uw,Nat.add_zero] at par
    obtain ⟨i,j,ui,uj,ij⟩ := (TrianglePrune.triangle_iff H u).mp (pos u)
    have d2 := OneEar.deg2 H ij.ne ui uj
    have uone : trianglesAt H u≠1 := fun h => (outside_mem.mp um).1 (inj (h.trans one.symm))
    have utwo : trianglesAt H u≠2 := fun h => (outside_mem.mp um).2.1 (inj (h.trans two.symm))
    have not2 : H.degree u≠2 := by
      intro d; have cap := Repair.triangles_le_choose H u; rw [d,Nat.choose_self] at cap; have := pos u; omega
    have uc : H.Adj u c := by
      apply Classical.byContradiction; intro no; rw [if_neg no] at par; omega
    rw [if_pos uc] at par
    have d : H.degree u=3 := by omega
    have cap := Repair.triangles_le_choose H u
    rw [d] at cap; have up : trianglesAt H u≤3 := cap
    have := pos u
    exact ⟨d,by omega,uc.symm,by omega⟩
  obtain ⟨v,vm,sm⟩ := existsLow
  obtain ⟨d,score,cv,dw⟩ := low vm sm
  have rest (u : V) (um : u∈W) (ne : u≠v) : 3≤nbr H u W := by
    have no : ¬nbr H u W≤2 := fun h => ne (inj ((low um h).2.1.trans score.symm)); omega
  have sees (u : V) (um : u∈W) (vu : H.Adj v u) : H.Adj c u :=
    full_neighbors H d score cv.symm vu (outside_mem.mp um).2.2.symm
  have none : (W\H.neighborFinset c).filter (H.Adj v)=∅ := eq_empty_of_forall_not_mem (by
    intro u h; obtain ⟨m,vu⟩ := mem_filter.mp h
    exact (mem_sdiff.mp m).2 ((H.mem_neighborFinset _ _).mpr (sees u (mem_sdiff.mp m).1 vu)))
  have guarded := exchange_iff_ordinary H ear ea ec ac n g ⟨v,vm,cv,by change ((W\H.neighborFinset c).filter (H.Adj v)).card≤1; simp [none]⟩
  have lower : ¬gamma (H.induce (W : Set V))≤14 := fun h => fail (guarded.mpr h)
  obtain ⟨X,cov,up⟩ := single_low H vm rest
  have upper : gamma (H.induce (W : Set V))≤15 := (gamma_induced_iff H).mpr ⟨X,cov,by omega⟩
  exact ⟨sz,by omega,v,vm,d,score,cv,dw,rest,sees⟩

end Graffiti384b.EarAnchor
#print axioms Graffiti384b.EarAnchor.diamond
#print axioms Graffiti384b.EarAnchor.cubic_failure
