import DominoGadget
import DominoRepair

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open DominoGadget HandleExtension FourRingCutAux FourRingCyclicEquivalence
noncomputable section
universe u

private theorem factor_transport {U V : Type*} [Fintype U] [DecidableEq U]
    [Fintype V] [DecidableEq V] {G : SimpleGraph U} {H : SimpleGraph V} (e : U≃V)
    (carry : ∀ x y,G.Adj x y→H.Adj (e x) (e y))
    (fact : KelmansStarter.HasP3Factor G) : KelmansStarter.HasP3Factor H := by
  obtain ⟨P,tile,disjoint,cover⟩ := fact
  let emb : Finset U↪Finset V := ⟨Finset.map e.toEmbedding,Finset.map_injective _⟩
  let Q := P.map emb
  refine ⟨Q,?_,?_,?_⟩
  · intro t tm
    obtain ⟨s,sm,rfl⟩ := mem_map.mp tm
    obtain ⟨card,c,cm,links⟩ := tile _ sm
    refine ⟨(card_map _).trans card,e c,mem_map.mpr ⟨c,cm,rfl⟩,?_⟩
    intro y ym neq
    obtain ⟨x,xm,rfl⟩ := mem_map.mp ym
    exact carry _ _ (links x xm (fun h=>neq (congrArg e h)))
  · intro t tm u um ne
    obtain ⟨s,sm,rfl⟩ := mem_map.mp tm
    obtain ⟨r,rm,rfl⟩ := mem_map.mp um
    apply disjoint_left.mpr
    intro y yt yu
    obtain ⟨v,vs,rfl⟩ := mem_map.mp yt
    obtain ⟨w,wr,we⟩ := mem_map.mp yu
    have q : w=v := e.injective we
    exact disjoint_left.mp (disjoint _ sm _ rm (fun h=>ne (congrArg emb h))) vs (q ▸ wr)
  · apply eq_univ_of_forall
    intro v
    let u := e.symm v
    have mem : u∈P.biUnion id := by rw [cover]; exact mem_univ _
    obtain ⟨s,sm,us⟩ := mem_biUnion.mp mem
    refine mem_biUnion.mpr ⟨emb s,mem_map.mpr ⟨s,sm,rfl⟩,?_⟩
    exact mem_map.mpr ⟨u,us,e.apply_symm_apply _⟩

private theorem seed_exists {U : Type u} [Fintype U] [DecidableEq U] {G : SimpleGraph U}
    [DecidableRel G.Adj] (cub : ∀ x,G.degree x=3) (tri : TriangleFree G) (x : U) :
    Nonempty (Seed G x) := by
  classical
  obtain ⟨a,d,c,adx,_,_,eqX⟩ :=
    card_eq_three.mp (show (G.neighborFinset x).card=3 by rw [card_neighborFinset_eq_degree,cub])
  have xa : G.Adj x a := (mem_neighborFinset _ _ _).mp (by simp [eqX])
  have xd : G.Adj x d := (mem_neighborFinset _ _ _).mp (by simp [eqX])
  let F := (G.neighborFinset a).erase x
  have xIn : x∈G.neighborFinset a := (mem_neighborFinset _ _ _).mpr xa.symm
  have nc : F.card=2 := by
    change ((G.neighborFinset a).erase x).card=2
    rw [card_erase_of_mem xIn,card_neighborFinset_eq_degree,cub]
  obtain ⟨b,w,bw,split⟩ := card_eq_two.mp nc
  have nb : b∈F := by rw [split]; simp
  have nw : w∈F := by rw [split]; simp
  have ab : G.Adj a b := (mem_neighborFinset _ _ _).mp (mem_erase.mp nb).2
  have aw : G.Adj a w := (mem_neighborFinset _ _ _).mp (mem_erase.mp nw).2
  have dw : d≠w := fun e=>tri x a d xa (e.symm ▸ aw) xd.symm
  refine ⟨⟨a,b,d,w,xa,xd,ab,aw,xd.ne.symm,adx.symm,dw,
    (mem_erase.mp nw).1,(mem_erase.mp nb).1,bw,?_⟩⟩
  intro y ay
  by_cases yx : y=x
  · exact Or.inl yx
  · have ym : y∈F := mem_erase.mpr ⟨yx,(mem_neighborFinset _ _ _).mpr ay⟩
    rw [split] at ym
    exact Or.inr (by simpa using ym)

private theorem factor_after_small_root {U : Type u} [Fintype U] [DecidableEq U]
    {G : SimpleGraph U} [DecidableRel G.Adj]
    (cub : ∀ x,G.degree x=3) (n4 : Fintype.card U=4) (x : U) :
    KelmansStarter.HasP3Factor (oldGraph G x) := by
  classical
  have edges (v w : U) (ne : v≠w) : G.Adj v w := by
    have sub : G.neighborFinset v ⊆ (univ:Finset U).erase v := fun a ah=>
      mem_erase.mpr ⟨((mem_neighborFinset _ _ _).mp ah).ne.symm,mem_univ _⟩
    have eq : G.neighborFinset v=(univ:Finset U).erase v := by
      apply eq_of_subset_of_card_le sub
      rw [card_erase_of_mem (mem_univ v),card_univ,n4,card_neighborFinset_eq_degree,cub]
    exact (mem_neighborFinset _ _ _).mp (eq.symm ▸ mem_erase.mpr ⟨ne.symm,mem_univ _⟩)
  have size : Fintype.card (Rest x)=3 := by
    rw [Fintype.card_subtype]
    have eq : ({z | z≠x}:Finset U)=(univ:Finset U).erase x := by
      ext z
      simp
    rw [eq,card_erase_of_mem (mem_univ x),card_univ,n4]
  obtain ⟨u⟩ := Fintype.card_pos_iff.mp (by omega : 0<Fintype.card (Rest x))
  refine ⟨{univ},?_,?_,by simp⟩
  · intro s sm
    rw [mem_singleton.mp sm]
    exact ⟨by simpa using size,u,mem_univ _,fun y _ ne=>edges _ _ (fun h=>ne (Subtype.ext h).symm)⟩
  · intro a am b bm ne
    exact (ne ((mem_singleton.mp am).trans (mem_singleton.mp bm).symm)).elim

/-- Plain cyclic-four Kelmans implies every prescribed single
vertex deletion at order 4 mod 6 in the same cyclic-four class. -/
theorem cyclic4_factor_implies_f1 (promise : CyclicUniversal.{u})
    {U : Type u} [Fintype U] [DecidableEq U] {G : SimpleGraph U} [DecidableRel G.Adj]
    (cub : ∀ x,G.degree x=3) (conn : KelmansStarter.ThreeConnected G)
    (small : SmallTrivial G) (res : Fintype.card U%6=4) (x : U) :
    KelmansStarter.HasP3Factor (oldGraph G x) := by
  classical
  by_cases sz : Fintype.card U=4
  · exact factor_after_small_root cub sz x
  have order := conn.1
  have tri := triangle_free_of_small_trivial G cub (by omega) small
  obtain ⟨S⟩ := seed_exists cub tri x
  let E := first S
  let F := second S
  have E3 := E.cubic cub
  have Es := E.preserves_small_trivial cub small
  have F3 := F.cubic E3
  have Fs := F.preserves_small_trivial E3 Es
  have Fc := F.three_connected E3 Es
  have ord : Fintype.card (Steps U)=Fintype.card U+4 := by
    change Fintype.card ((U⊕Bool)⊕Bool)=_
    rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_bool]
  have residue : Fintype.card (Steps U)%6=2 := by omega
  have f := cyclic4_factor_implies_t2 promise F3 Fc Fs residue (root x) (roots_adjacent S)
  have f' : KelmansStarter.HasP3Factor (reduced S) := by
    apply factor_transport (embed S).symm _ f
    intro y z adj
    unfold reduced
    change (FourRingReplica.Layout.minor (second S).host (root x)).Adj
      ((embed S) ((embed S).symm y)) ((embed S) ((embed S).symm z))
    simpa using adj
  obtain ⟨old,p,q,r,pq,qr,pr⟩ := residual_shape S
  apply DominoRepair.factor_of_residual (oldGraph G x) (reduced S)
    (a:=⟨S.a,S.xa.ne.symm⟩) (b:=⟨S.b,S.bx⟩) S.ab old _ _ _ f'
  · rintro (u|i) h
    · exact ((p u).mp h).elim (fun e=>Or.inr (Or.inl (congrArg Sum.inl e)))
        (fun e=>Or.inr (Or.inr (congrArg Sum.inl e)))
    · fin_cases i
      · exact ((reduced S).loopless _ h).elim
      · exact Or.inl rfl
      · exact (pr h).elim
  · rintro (u|i) h
    · exact (q u h).elim
    · fin_cases i
      · exact Or.inl rfl
      · exact ((reduced S).loopless _ h).elim
      · exact Or.inr rfl
  · rintro (u|i) h
    · exact Or.inr (congrArg Sum.inl ((r u).mp h))
    · fin_cases i
      · exact (pr h.symm).elim
      · exact Or.inl rfl
      · exact ((reduced S).loopless _ h).elim

#print axioms cyclic4_factor_implies_f1
end
end KelmansCactus.AtomicBridge
