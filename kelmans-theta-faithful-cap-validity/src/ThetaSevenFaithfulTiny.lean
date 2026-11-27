import ThetaSevenFaithfulCost
import Mathlib.Tactic.FinCases

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaSevenFaithfulTiny
open PentagonProfile (Port)
open SquareCap (boundary)
open ThetaSevenFaithfulCap (candidate wire3 edges3)
open ThetaSevenFaithfulCost (candidate_boundary)
open ThetaSevenFaithfulLocalCut (cost capWires)

def trues {W : Type*} [Fintype W] (c : W→Bool) : Finset W :=
  univ.filter (fun x=>c x=true)

@[simp] theorem mem_trues {W : Type*} [Fintype W] {c : W→Bool} {x : W} :
    x ∈ trues c ↔ c x=true := by simp [trues]

theorem trues_sum {V T : Type*} [Fintype V] [Fintype T] (c : V→Bool) (s : T→Bool) :
    trues (Sum.elim c s) = (trues c).disjSum (trues s) := by
  classical
  ext x
  cases x <;> simp

def NoShared (c : Port→Bool) : Prop :=
  ∀ (i j : Port) (v : Fin 3), i≠j→c i=true→c j=true→wire3 i v=true→wire3 j v=true→False

instance (c : Port→Bool) : Decidable (NoShared c) := by unfold NoShared; infer_instance

def adjVal (e : Bool) : ℕ := if e then 1 else 0

private theorem small_table (k : Fin 3) (a : Bool) (c : Port→Bool) (s : Fin 3→Bool) :
    (trues c).card≤k.val →
    2≤k.val+(trues s).card →
    (a=true → k.val=2 ∧ NoShared c) →
    4 + 2*adjVal a + cost edges3 capWires c (fun _=>false) ≤
      3*k.val+cost edges3 capWires c s := by
  have checked : ∀ (k : Fin 3) (a : Bool), ∀ (c : Port→Bool) (s : Fin 3→Bool),
    (trues c).card≤k.val →
    2≤k.val+(trues s).card →
    (a=true → k.val=2 ∧ NoShared c) →
    4 + 2*adjVal a + cost edges3 capWires c (fun _=>false) ≤
      3*k.val+cost edges3 capWires c s := by
    intro k a
    fin_cases k <;> cases a <;> decide
  exact checked k a c s

theorem boundary_compl {W : Type*} [Fintype W] (G : SimpleGraph W) (c : W→Bool) :
    (boundary G (fun x=> !(c x))).card=(boundary G c).card := by
  classical
  let swap : (W×W)↪(W×W) := ⟨Prod.swap,fun _ _ h=>by simpa using congrArg Prod.swap h⟩
  have eq : boundary G (fun x=> !(c x))=(boundary G c).map swap := by
    ext ⟨x,y⟩
    have mt : (x,y)∈(boundary G c).map swap ↔ (y,x)∈boundary G c := by
      constructor
      · rintro h
        obtain ⟨⟨u,v⟩,m,h⟩ := mem_map.mp h
        change (v,u)=(x,y) at h
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
        exact m
      · intro h
        exact mem_map.mpr ⟨(y,x),h,rfl⟩
    rw [mt]
    simp [boundary,adj_comm,and_comm, and_left_comm]
  rw [eq,card_map]

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

def IndependentContacts {V : Type*} (B : SimpleGraph V) (p : Port↪V) : Prop :=
  ∀ (i j : Port) (v : Fin 3), i≠j→wire3 i v=true→wire3 j v=true→¬B.Adj (p i) (p j)

theorem tiny_shore {V : Type*} [Fintype V] [DecidableEq V] {B : SimpleGraph V}
    [DecidableRel B.Adj] {p : Port↪V}
    (cub : ∀ x,(candidate B p).degree x=3) (ind : IndependentContacts B p)
    (c : V→Bool) (s : Fin 3→Bool) (size : (trues c).card≤2)
    (notTrivial : 2≤(trues (Sum.elim c s)).card) :
    4≤(boundary (candidate B p) (Sum.elim c s)).card := by
  classical
  let G := candidate B p
  let pure : V⊕Fin 3→Bool := Sum.elim c (fun _=>false)
  have image : (trues (c ∘ p)).map p ⊆ trues c := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
    have tgt : (c ∘ p) i=true := mem_trues.mp hi
    exact mem_trues.mpr tgt
  have portSize := card_le_card image
  rw [card_map] at portSize
  have hsize : 2 ≤ (trues c).card+(trues s).card := by
    simpa only [trues_sum,card_disjSum] using notTrivial
  have arithmetic :
      ∃ a : Bool, (boundary G pure).card+2*adjVal a=3*(trues c).card ∧
        (a=true→(trues c).card=2 ∧ NoShared (c ∘ p)) := by
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
        intro i j w ij ci cj wi wj
        have iti := members (p i) ci
        have itj := members (p j) cj
        have dd : p i≠p j := fun e=>ij (p.injective e)
        have adj : B.Adj (p i) (p j) := by
          rcases iti with l|l <;> rcases itj with r|r
          · exact (dd (l.trans r.symm)).elim
          · simpa [l,r] using edge
          · simpa [l,r] using edge.symm
          · exact (dd (l.trans r.symm)).elim
        exact ind i j w ij wi wj adj
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
  have m := small_table k a (c ∘ p) s portSize hsize ha
  change 4+2*adjVal a + cost edges3 capWires (c ∘ p) (fun _=>false) ≤
    3*(trues c).card+cost edges3 capWires (c ∘ p) s at m
  change (boundary (candidate B p) (Sum.elim c (fun _=>false))).card+2*adjVal a=3*(trues c).card at h
  rw [candidate_boundary] at h ⊢
  omega

#print axioms boundary_compl
#print axioms tiny_shore
end KelmansCactus.AtomicBridge.ThetaSevenFaithfulTiny
