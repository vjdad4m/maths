import C7MultiSmallScopes133
import BicycleExactTriangleCharge133

namespace Graffiti133MultiWeighted
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133BicycleCharge
  Graffiti133ExteriorSlack
open scoped Classical
set_option linter.unusedSectionVars false
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {J : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel J.Adj]

private theorem clique_iso (e : G ≃g J) (A : Finset V) :
    G.IsNClique 3 A ↔ J.IsNClique 3 (A.map e.toEquiv.toEmbedding) := by
  rw [SimpleGraph.isNClique_iff,SimpleGraph.isNClique_iff,Finset.card_map]
  refine and_congr_left' ?_
  constructor
  · intro h x xm y ym nq
    obtain ⟨a,am,ne⟩ := Finset.mem_map.mp xm
    obtain ⟨b,bm,be⟩ := Finset.mem_map.mp ym
    change e a=x at ne
    change e b=y at be
    subst x
    subst y
    exact (e.map_rel_iff').mpr (h am bm (fun q=>nq (congrArg e q)))
  · intro h x xm y ym ne
    exact (e.map_rel_iff').mp (h
      (Finset.mem_map.mpr ⟨x,xm,rfl⟩) (Finset.mem_map.mpr ⟨y,ym,rfl⟩) (e.injective.ne ne))

theorem triangle_count_iso (e : G ≃g J) : triangleCount G=triangleCount J := by
  classical
  unfold triangleCount
  apply Finset.card_bij (fun A _=>A.map e.toEquiv.toEmbedding)
  · intro A am
    exact SimpleGraph.mem_cliqueFinset_iff.mpr ((clique_iso e A).mp (SimpleGraph.mem_cliqueFinset_iff.mp am))
  · intro A _ B _ eq
    exact Finset.map_injective _ eq
  · intro B bm
    let A := B.map e.symm.toEquiv.toEmbedding
    have eq : A.map e.toEquiv.toEmbedding=B := by
      ext y
      simp only [A,Finset.mem_map]
      constructor
      · rintro ⟨x,⟨z,zm,e1⟩,e2⟩
        change e.symm z=x at e1; change e x=y at e2
        exact (by rw [←e2,←e1,e.apply_symm_apply]; exact zm)
      · intro h
        exact ⟨e.symm y,⟨y,h,rfl⟩,e.apply_symm_apply y⟩
    refine ⟨A,SimpleGraph.mem_cliqueFinset_iff.mpr ((clique_iso e A).mpr ?_),eq⟩
    rw [eq]
    exact SimpleGraph.mem_cliqueFinset_iff.mp bm

def erase_induce_iso (A : Finset V) (x : (A : Set V)) :
    ((G.induce (A : Set V)).induce {y : (A : Set V) | y≠x}) ≃g G.induce (A.erase x.val : Set V) where
  toEquiv := {
    toFun := fun y=>⟨y.val.val,Finset.mem_erase.mpr ⟨fun eq=>y.property (Subtype.ext eq),y.val.property⟩⟩
    invFun := fun y=>⟨⟨y.val,(Finset.mem_erase.mp y.property).2⟩,
      fun eq=>(Finset.mem_erase.mp y.property).1 (congrArg Subtype.val eq)⟩
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl }
  map_rel_iff' := Iff.rfl

def full_induce_iso : G.induce ((Finset.univ : Finset V) : Set V) ≃g G where
  toEquiv := {
    toFun := Subtype.val
    invFun := fun x=>⟨x,Finset.mem_univ _⟩
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl }
  map_rel_iff' := Iff.rfl

theorem row_is_degree (x : V) : row G x Finset.univ = G.degree x := by
  classical
  letI : DecidablePred (G.Adj x) := fun y=>Classical.propDecidable _
  have r : row G x Finset.univ=(Finset.univ.filter (G.Adj x)).card := (Finset.card_filter _ _).symm
  rw [r,←G.card_neighborFinset_eq_degree]
  congr 1
  ext y
  rw [G.mem_neighborFinset]
  simp

#print axioms triangle_count_iso
end Graffiti133MultiWeighted


namespace Graffiti133MultiWeighted
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7 Graffiti133BicycleCharge
  Graffiti133ExteriorSlack Graffiti133ExactTriangleCharge Graffiti133Bicycle Graffiti133SingletonSlack
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

noncomputable def multiPenalty (H : Hole G 7) (x : V) : Nat :=
  if (contactSet H x).card=3 then 1 else 0

noncomputable def multiCredit (H : Hole G 7) (x : V) : Nat :=
  if (contactSet H x).card=3 then 0 else
    if (∃ i∈contactSet H x,∃ j∈contactSet H x,Cyclic i j) then 3 else 2

def restrictedHole (H : Hole G 7) (U : Finset V) (cyc : ∀ i,H.c i∈U) :
    Hole (G.induce (U : Set V)) 7 :=
  ⟨fun i=>⟨H.c i,cyc i⟩,fun _ _ e=>H.inj (congrArg Subtype.val e),H.adj⟩

theorem restricted_contacts (H : Hole G 7) (U : Finset V) (cyc : ∀ i,H.c i∈U) (x : (U : Set V)) :
    contactSet (restrictedHole H U cyc) x=contactSet H x.val := by
  ext i
  simp only [mem_contactSet]
  rfl

theorem restricted_c4 (h4 : FourCycleFree G) (U : Finset V) :
    FourCycleFree (G.induce (U : Set V)) := by
  intro a b u v ne au bu av bv
  exact Subtype.ext (h4 _ _ _ _ (fun e=>ne (Subtype.ext e)) au bu av bv)

theorem score_base {l e t n m : Nat} (slack : l+14≤4*n)
    (charge : l+3*t=2*e) (size : n=m) : 2*e+14≤4*m+3*t := by omega

theorem score_step {e₀ e₁ t₀ t₁ n₀ n₁ d r p c P C : Nat}
    (de : e₀+d=e₁) (dt : t₀+r=t₁) (sz : n₁=n₀+1)
    (step : 2*d+p≤4+3*r+c)
    (prev : 2*e₀+14+P≤4*n₀+3*t₀+C) :
    2*e₁+14+(p+P)≤4*n₁+3*t₁+(c+C) := by omega

theorem score_finish {l e t n P C : Nat} (charge : l+3*t=2*e)
    (total : 2*e+14+P≤4*n+3*t+C) : l+14+P≤4*n+C := by omega

theorem score_add_sets
    (K D : Finset V) (E C : Finset V→Nat) (penalty credit : V→Nat)
    (base : 2*E K+14≤4*K.card+3*C K)
    (step : ∀ x, x∈D → ∀ T⊆D,x∉T →
      2*E (K∪insert x T)+penalty x+3*C (K∪T) ≤
      2*E (K∪T)+4+3*C (K∪insert x T)+credit x)
    (apart : Disjoint K D)
    (T : Finset V) (sub : T⊆D) :
    2*E (K∪T)+14+(∑ x∈T,penalty x) ≤ 4*(K∪T).card+3*C (K∪T)+(∑ x∈T,credit x) := by
  induction T using Finset.induction_on with
  | empty =>
    simpa only [Finset.union_empty,Finset.sum_empty,Nat.add_zero] using base
  | @insert x T nx ih =>
    have xd := sub (Finset.mem_insert_self _ _)
    have Tsub : T⊆D := fun y ym=>sub (Finset.mem_insert_of_mem ym)
    have nK : x∉K := fun m=>Finset.disjoint_left.mp apart m xd
    have dis : x∉K∪T := by simp [nK,nx]
    have eq : K∪insert x T=insert x (K∪T) := by ext z; simp [or_comm,or_left_comm]
    have card : (K∪insert x T).card=(K∪T).card+1 := by rw [eq,Finset.card_insert_of_not_mem dis]
    have s := step x xd T Tsub nx
    have p := ih Tsub
    simp only [Finset.sum_insert nx]
    omega

theorem actual_induced_delta (A : Finset V) (x : (A : Set V)) :
    let J := G.induce (A : Set V);
    (G.induce (A.erase x.val : Set V)).edgeFinset.card+J.degree x=J.edgeFinset.card ∧
    triangleCount (G.induce (A.erase x.val : Set V))+triangleIncidence J x=triangleCount J := by
  classical
  let J := G.induce (A : Set V)
  let map := erase_induce_iso (G:=G) A x
  have a := card_delete_add_degree J x
  have b := triangle_count_deletion J x
  rw [map.card_edgeFinset_eq] at a
  rw [triangle_count_iso map] at b
  exact ⟨a,b⟩


#print axioms actual_induced_delta
end Graffiti133MultiWeighted
