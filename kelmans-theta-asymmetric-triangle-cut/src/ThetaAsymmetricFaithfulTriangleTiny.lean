import ThetaAsymmetricFaithfulGeometry
import ThetaSevenFaithfulTiny
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaAsymmetricFaithfulTriangleTiny
open SquareCap (boundary)
open ThetaSevenFaithfulTiny (trues mem_trues trues_sum adjVal)
open ThetaSevenFaithfulCap (edges3)
open ThetaAsymmetricFaithfulTable (Wire cost newWires)
open ThetaAsymmetricFaithful (candidate)
open ThetaAsymmetricFaithfulGeometry (candidate_boundary ProperWires root3 unique3)

def countBase (c : Wire→Bool) : ℕ :=
  ((univ : Finset Wire).filter (fun i=>i.val<4∧c i=true)).card

def countFaith (c : Wire→Bool) : ℕ :=
  ((univ : Finset Wire).filter (fun i=>root3 i=2∧c i=true)).card

def NoSharedBC (c : Wire→Bool) : Prop :=
  ∀ j : Fin 3, j≠0→((univ : Finset Wire).filter (fun i=>root3 i=j∧c i=true)).card≤1

instance (c : Wire→Bool) : Decidable (NoSharedBC c) := by unfold NoSharedBC; infer_instance

def isTriangleState (k : Fin 3) (c : Wire→Bool) (s : Fin 3→Bool) : Prop :=
  k.val=2 ∧ c 1=true ∧ c 2=true ∧ s 0=true ∧ s 1=false ∧ s 2=false
instance (k : Fin 3) (c : Wire→Bool) (s : Fin 3→Bool) :
    Decidable (isTriangleState k c s) := by unfold isTriangleState; infer_instance

set_option maxRecDepth 3000 in
set_option maxHeartbeats 0 in
private theorem small_table (k : Fin 3) (a : Bool) (c : Wire→Bool) (s : Fin 3→Bool) :
    countBase c≤k.val → countFaith c≤k.val →
    2≤k.val+(trues s).card →
    (a=true → k.val=2 ∧ NoSharedBC c) →
    4 + 2*adjVal a + cost edges3 newWires c (fun _=>false) ≤
      3*k.val+cost edges3 newWires c s ∨ isTriangleState k c s := by
  let bit (v : Fin 8) (i : Fin 3) := Nat.testBit v.val i.val
  have checked : ∀ (k : Fin 3) (a : Bool) (v : Fin 8) (c : Wire→Bool),
    countBase c≤k.val → countFaith c≤k.val →
    2≤k.val+(trues (bit v)).card →
    (a=true → k.val=2 ∧ NoSharedBC c) →
    4 + 2*adjVal a + cost edges3 newWires c (fun _=>false) ≤
      3*k.val+cost edges3 newWires c (bit v) ∨ isTriangleState k c (bit v) := by
    intro k a v
    fin_cases k <;> cases a <;> fin_cases v <;> decide
  have cbit : ∀ s : Fin 3→Bool,∃ v : Fin 8,bit v=s := by decide
  obtain ⟨v,rfl⟩ := cbit s
  exact checked k a v c

section Cut
variable {W : Type*} [Fintype W] [DecidableEq W]
variable (G : SimpleGraph W) [DecidableRel G.Adj]

omit [DecidableEq W] [DecidableRel G.Adj] in
private theorem boundary_empty (c : W→Bool) (h : ∀ x,c x≠true) :
    (boundary G c).card=0 := by
  have none : boundary G c=∅ := by
    ext ⟨x,y⟩
    simp [boundary,h]
  rw [none,card_empty]

private theorem boundary_single (c : W→Bool) (u : W) (hu : c u=true)
    (h : ∀ x,c x=true→x=u) :
    (boundary G c).card=G.degree u := by
  classical
  have eq : boundary G c=(G.neighborFinset u).image (fun v=>(u,v)) := by
    ext ⟨x,y⟩
    constructor
    · intro z
      obtain ⟨a,_,d⟩ : c x=true ∧ c y=false ∧ G.Adj x y := by simpa [boundary] using z
      rw [h _ a] at d ⊢
      exact mem_image.mpr ⟨y,(mem_neighborFinset _ _ _).mpr d,rfl⟩
    · intro z
      obtain ⟨v,hv,eq⟩ := mem_image.mp z
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      have e := (mem_neighborFinset _ _ _).mp hv
      have cc : c v=false := by
        cases he : c v
        · rfl
        · exact (e.ne (h _ he).symm).elim
      simp [boundary,hu,cc,e]
  rw [eq,card_image_of_injective _ (fun _ _ e=>congrArg Prod.snd e),card_neighborFinset_eq_degree]

private theorem boundary_pair (c : W→Bool) (u v : W) (uv : u≠v)
    (hu : c u=true) (hv : c v=true) (h : ∀ x,c x=true→x=u∨x=v) :
    (boundary G c).card+2*adjVal (decide (G.Adj u v))=G.degree u+G.degree v := by
  classical
  let A := ((G.neighborFinset u).erase v).image (fun w=>(u,w))
  let B := ((G.neighborFinset v).erase u).image (fun w=>(v,w))
  have row (x y w : W) :
      (x,w)∈((G.neighborFinset x).erase y).image (fun z=>(x,z)) ↔ w≠y ∧ G.Adj x w := by
    simp [mem_image,mem_erase,mem_neighborFinset]
  have sep : Disjoint A B := by
    rw [disjoint_left]
    intro z za zb
    obtain ⟨a,_,rfl⟩ := mem_image.mp za
    obtain ⟨b,_,eq⟩ := mem_image.mp zb
    exact uv (congrArg Prod.fst eq).symm
  have hc (w : W) (nd : w≠u ∧ w≠v) : c w=false := by
    cases he : c w
    · rfl
    · exact ((h w he).elim nd.1 nd.2).elim
  have split : boundary G c=A∪B := by
    ext ⟨x,w⟩
    rw [mem_union]
    constructor
    · intro z
      obtain ⟨cx,cw,ed⟩ : c x=true ∧ c w=false ∧ G.Adj x w := by simpa [boundary] using z
      rcases h x cx with rfl|rfl
      · exact Or.inl ((row x v w).mpr ⟨fun e=>Bool.noConfusion (hv.symm.trans (e ▸ cw)),ed⟩)
      · exact Or.inr ((row x u w).mpr ⟨fun e=>Bool.noConfusion (hu.symm.trans (e ▸ cw)),ed⟩)
    · rintro (m|m)
      · obtain ⟨z,hm,eq⟩ := mem_image.mp m
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
        obtain ⟨nd,ed⟩ := (row u v z).mp (mem_image.mpr ⟨z,hm,rfl⟩)
        simp [boundary,hu,hc z ⟨ed.ne.symm,nd⟩,ed]
      · obtain ⟨z,hm,eq⟩ := mem_image.mp m
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
        obtain ⟨nd,ed⟩ := (row v u z).mp (mem_image.mpr ⟨z,hm,rfl⟩)
        simp [boundary,hv,hc z ⟨nd,ed.ne.symm⟩,ed]
  rw [split,card_union_of_disjoint sep]
  have Ac : A.card = ((G.neighborFinset u).erase v).card :=
    card_image_of_injective _ (fun _ _ e=>congrArg Prod.snd e)
  have Bc : B.card = ((G.neighborFinset v).erase u).card :=
    card_image_of_injective _ (fun _ _ e=>congrArg Prod.snd e)
  rw [Ac,Bc]
  by_cases e : G.Adj u v
  · rw [card_erase_of_mem ((mem_neighborFinset _ _ _).mpr e),
      card_erase_of_mem ((mem_neighborFinset _ _ _).mpr e.symm)]
    have p : 0<(G.neighborFinset u).card := card_pos.mpr ⟨v,(mem_neighborFinset _ _ _).mpr e⟩
    have q : 0<(G.neighborFinset v).card := card_pos.mpr ⟨u,(mem_neighborFinset _ _ _).mpr e.symm⟩
    simp only [card_neighborFinset_eq_degree] at p q ⊢
    simp [adjVal,e]
    omega
  · have aa : v∉G.neighborFinset u := by simpa [mem_neighborFinset] using e
    have bb : u∉G.neighborFinset v := by simpa [mem_neighborFinset,adj_comm] using e
    simp [erase_eq_of_not_mem aa,erase_eq_of_not_mem bb,card_neighborFinset_eq_degree,adjVal,e]
end Cut


def IndependentBC {V : Type*} (B : SimpleGraph V) (p : Wire→V) : Prop :=
  ∀ i j : Wire,i≠j→ root3 i=root3 j→ root3 i≠0→¬B.Adj (p i) (p j)

def exceptionalShore {V : Type*} [DecidableEq V] (p : Wire→V) : Finset (V⊕Fin 3) :=
  {Sum.inr 0,Sum.inl (p 1),Sum.inl (p 2)}

theorem tiny_shore {V : Type*} [Fintype V] [DecidableEq V] {B : SimpleGraph V}
    [DecidableRel B.Adj] {p : Wire→V}
    (cub : ∀ x,(candidate B p).degree x=3) (proper : ProperWires p) (ind : IndependentBC B p)
    (c : V→Bool) (s : Fin 3→Bool) (size : (trues c).card≤2)
    (notTrivial : 2≤(trues (Sum.elim c s)).card) :
    4≤(boundary (candidate B p) (Sum.elim c s)).card ∨
      trues (Sum.elim c s)=exceptionalShore p := by
  classical
  let G := candidate B p
  let pure : V⊕Fin 3→Bool := Sum.elim c (fun _=>false)
  have liftBound (g : Wire→Prop) [DecidablePred g]
      (inj : Set.InjOn p {i|g i}) :
      ((univ : Finset Wire).filter (fun i=>g i∧c (p i)=true)).card≤(trues c).card := by
    let A := (univ : Finset Wire).filter (fun i=>g i∧c (p i)=true)
    have inj' : Set.InjOn p (↑A : Set Wire) := by
      intro i hi j hj eq
      exact inj ((mem_filter.mp hi).2.1) ((mem_filter.mp hj).2.1) eq
    have ss : A.image p ⊆ trues c := by
      intro u hu
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hu
      exact mem_trues.mpr ((mem_filter.mp hi).2.2)
    simpa only [card_image_of_injOn inj'] using card_le_card ss
  have baseBound : countBase (fun i=>c (p i)) ≤ (trues c).card :=
    liftBound (fun i=>i.val<4) (fun i a j b e=>proper.1 i j a b e)
  have faithBound : countFaith (fun i=>c (p i)) ≤ (trues c).card :=
    liftBound (fun i=>root3 i=2) (by
      intro i hi j hj eq
      exact unique3 proper (Prod.ext eq (hi.trans hj.symm)))
  have hsize : 2 ≤ (trues c).card+(trues s).card := by
    simpa only [trues_sum,card_disjSum] using notTrivial
  have arithmetic :
      ∃ a : Bool, (boundary G pure).card+2*adjVal a=3*(trues c).card ∧
        (a=true→(trues c).card=2 ∧ NoSharedBC (fun i=>c (p i))) := by
    by_cases existsTwo : 1<(trues c).card
    · obtain ⟨x,tx,y,ty,xy⟩ := one_lt_card.mp existsTwo
      have tx' := mem_trues.mp tx
      have ty' := mem_trues.mp ty
      have ct : (trues c).card=2 := by omega
      have members : ∀ i,c i=true→i=x∨i=y := by
        have eq : ({x,y}:Finset V)=trues c := by
          refine eq_of_subset_of_card_le ?_ ?_
          · intro j hj
            simp only [mem_insert,mem_singleton] at hj
            rcases hj with rfl|rfl <;> assumption
          · simp [ct,card_insert_of_not_mem,xy]
        intro i h
        have d := mem_trues.mpr h
        rw [←eq] at d
        simpa using d
      let u : V⊕Fin 3 := Sum.inl x
      let v : V⊕Fin 3 := Sum.inl y
      have uv : u≠v := fun h=>xy (Sum.inl_injective h)
      have inside : ∀ z,pure z=true→z=u∨z=v := by
        rintro (z|z) hz
        · exact (members z hz).imp (congrArg Sum.inl) (congrArg Sum.inl)
        · simp [pure] at hz
      let a := decide (G.Adj u v)
      refine ⟨a,?_,?_⟩
      · have eq := boundary_pair G pure u v uv tx' ty' inside
        change (boundary G pure).card+2*adjVal a=G.degree u+G.degree v at eq
        have cu : G.degree u=3 := cub u
        have cv : G.degree v=3 := cub v
        rw [ct]
        omega
      · intro ha
        refine ⟨ct,?_⟩
        have edge : B.Adj x y := of_decide_eq_true ha
        intro r r0
        apply card_le_one.mpr
        intro i hi j hj
        by_contra ij
        obtain ⟨ri,ci⟩ := (mem_filter.mp hi).2
        obtain ⟨rj,cj⟩ := (mem_filter.mp hj).2
        have same := ri.trans rj.symm
        have iti := members (p i) ci
        have itj := members (p j) cj
        have dd : p i≠p j := fun e=>ij (unique3 proper (Prod.ext e same))
        have adj : B.Adj (p i) (p j) := by
          rcases iti with l|l <;> rcases itj with r|r
          · exact (dd (l.trans r.symm)).elim
          · simpa [l,r] using edge
          · simpa [l,r] using edge.symm
          · exact (dd (l.trans r.symm)).elim
        exact ind i j ij same (fun e=>r0 (ri.symm.trans e)) adj
    · by_cases some : ∃ x,c x=true
      · obtain ⟨x,hx⟩ := some
        have xm := mem_trues.mpr hx
        have ct : (trues c).card=1 := by
          have pos := card_pos.mpr ⟨x,xm⟩
          omega
        have members : ∀ i,c i=true→i=x := by
          intro i hi
          exact (card_le_one.mp (by omega : (trues c).card≤1)) i (mem_trues.mpr hi) x xm
        let u : V⊕Fin 3 := Sum.inl x
        have inside : ∀ z,pure z=true→z=u := by
          rintro (z|z) hz
          · exact congrArg Sum.inl (members z hz)
          · simp [pure] at hz
        refine ⟨false,?_,by simp⟩
        rw [boundary_single G pure u hx inside,cub,ct]
        rfl
      · have ct : (trues c).card=0 := by
          rw [card_eq_zero]
          ext x
          exact (mem_trues.trans (iff_of_false (fun hx=>some ⟨x,hx⟩) (not_mem_empty x)))
        have inside : ∀ z,pure z≠true := by
          rintro (z|z) hz
          · exact some ⟨z,hz⟩
          · simp [pure] at hz
        refine ⟨false,?_,by simp⟩
        rw [boundary_empty G pure inside,ct]
        rfl
  obtain ⟨a,h,ha⟩ := arithmetic
  let k : Fin 3 := ⟨(trues c).card,by omega⟩
  have m := small_table k a (fun i=>c (p i)) s baseBound faithBound hsize ha
  rcases m with bound|exception
  · left
    change 4+2*adjVal a + cost edges3 newWires (fun i=>c (p i)) (fun _=>false) ≤
      3*(trues c).card+cost edges3 newWires (fun i=>c (p i)) s at bound
    change (boundary (candidate B p) (Sum.elim c (fun _=>false))).card+2*adjVal a=3*(trues c).card at h
    rw [candidate_boundary B p proper] at h ⊢
    omega
  · right
    obtain ⟨count,c1,c2,s0,s1,s2⟩ := exception
    have ne : p 1≠p 2 := fun e=>(by decide : (1:Wire)≠2) (proper.1 1 2 (by decide) (by decide) e)
    have outsideEq : ({p 1,p 2}:Finset V)=trues c := by
      apply eq_of_subset_of_card_le
      · intro x hx
        simp only [mem_insert,mem_singleton] at hx
        rcases hx with rfl|rfl
        · exact mem_trues.mpr c1
        · exact mem_trues.mpr c2
      · change (trues c).card=2 at count
        simp [count,card_insert_of_not_mem,ne]
    have insideEq : trues s={0} := by
      ext i
      fin_cases i <;> simp [s0,s1,s2]
    rw [trues_sum,←outsideEq,insideEq]
    ext x
    cases x <;> simp [exceptionalShore]


#print axioms tiny_shore
end KelmansCactus.AtomicBridge.ThetaAsymmetricFaithfulTriangleTiny
