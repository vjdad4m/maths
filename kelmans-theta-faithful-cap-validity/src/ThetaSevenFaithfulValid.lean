import ThetaSevenFaithfulTiny
import PentagonCap
import TwinObstruction

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaSevenFaithfulValid
open SquareCap (boundary SmallTrivial FactorOn)
open PentagonCap (SmallFourTrivial)
open PentagonProfile (Port)
open ThetaSevenFaithfulCap (ambient candidate candidate_cubic wire3 edges3 edges9 target)
open ThetaSevenFaithfulCost (candidate_boundary ambient_boundary)
open ThetaSevenFaithfulTiny (trues mem_trues IndependentContacts tiny_shore boundary_compl)
open ThetaSevenFaithfulLocalCut (local_cut_domination cost oldWires capWires)
open ThetaSevenFaithfulRefill (In)

noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Exterior independence of the three physical cap neighborhoods:
(p3,t), (p1,p4), and (p1,p2,p3), in original theta coordinates.
This condition is part of the reduction, not a property imposed on all layouts. -/
def IndependentGroups (B : SimpleGraph V) (p : Port↪V) : Prop :=
  ¬B.Adj (p 2) (p 4) ∧ ¬B.Adj (p 0) (p 3) ∧
    ¬B.Adj (p 0) (p 1) ∧ ¬B.Adj (p 0) (p 2) ∧ ¬B.Adj (p 1) (p 2)

omit [Fintype V] [DecidableEq V] in
theorem groups_iff (B : SimpleGraph V) (p : Port↪V) :
    IndependentGroups B p ↔ IndependentContacts B p := by
  let pairs : List (Port×Port) := [(2,4),(0,3),(0,1),(0,2),(1,2)]
  have listed : ∀ i j : Port,∀ v : Fin 3, i≠j→wire3 i v=true→wire3 j v=true→
      (i,j)∈pairs∨(j,i)∈pairs := by decide
  constructor
  · rintro ⟨a,b,c,d,e⟩ i j t ij iW jW
    have deny (i j : Port) (h : (i,j)∈pairs) : ¬B.Adj (p i) (p j) := by
      simp [pairs] at h
      rcases h with h|h|h|h|h
      · obtain ⟨rfl,rfl⟩ := h
        exact a
      · obtain ⟨rfl,rfl⟩ := h
        exact b
      · obtain ⟨rfl,rfl⟩ := h
        exact c
      · obtain ⟨rfl,rfl⟩ := h
        exact d
      · obtain ⟨rfl,rfl⟩ := h
        exact e
    rcases listed i j t ij iW jW with h|h
    · exact deny i j h
    · exact fun e=>deny j i h e.symm
  · intro h
    exact ⟨h 2 4 0 (by decide) (by decide) (by decide),
      h 0 3 1 (by decide) (by decide) (by decide),h 0 1 2 (by decide) (by decide) (by decide),
      h 0 2 2 (by decide) (by decide) (by decide),h 1 2 2 (by decide) (by decide) (by decide)⟩

private theorem true_triple (c : V→Bool) (more : 2<(trues c).card) :
    ∃ x y z : V,c x=true∧c y=true∧c z=true∧x≠y∧x≠z∧y≠z := by
  obtain ⟨x,xc,y,yc,xy⟩ := one_lt_card.mp (by omega : 1<(trues c).card)
  have two : ({x,y}:Finset V).card=2 := by simp [card_insert_of_not_mem,xy]
  obtain ⟨z,zc,nd⟩ := exists_mem_not_mem_of_card_lt_card (by omega : ({x,y}:Finset V).card<(trues c).card)
  have nd' : z≠x ∧ z≠y := by simpa using nd
  exact ⟨x,y,z,mem_trues.mp xc,mem_trues.mp yc,mem_trues.mp zc,xy,nd'.1.symm,nd'.2.symm⟩

private theorem at_least_two {W : Type*} [Fintype W] (f : W→Bool) {a b : W}
    (fa : f a=true) (fb : f b=true) (ab : a≠b) : 2≤(trues f).card :=
  one_lt_card.mpr ⟨a,mem_trues.mpr fa,b,mem_trues.mpr fb,ab⟩

private theorem neg_true {b : Bool} : b=false→(!b)=true := by intro h; simp [h]

/-- A large/large cap cut transfers to an ambient cut with at most one
additional edge. A cut with at most two exterior vertices on a shore is
handled using the exact cut degree and the explicit independent groups. -/
theorem cap_valid_of_independent_groups {B : SimpleGraph V} [DecidableRel B.Adj] {p : Port↪V}
    (cub : ∀ x,(ambient B p).degree x=3) (cyc5 : SmallFourTrivial (ambient B p))
    (groups : IndependentGroups B p) : SmallTrivial (candidate B p) := by
  classical
  have cc := candidate_cubic B p cub
  have ind := (groups_iff B p).mp groups
  intro f bound
  by_contra! bad
  obtain ⟨⟨a,b,fa,fb,ab⟩,⟨e,g,fe,fg,eg⟩⟩ := bad
  let c : V→Bool := f ∘ Sum.inl
  let s : Fin 3→Bool := f ∘ Sum.inr
  let neg : (V⊕Fin 3)→Bool := fun x=> !(f x)
  have eq : f=Sum.elim c s := by funext x; cases x <;> rfl
  have eqNeg : neg=Sum.elim (fun x=> !(c x)) (fun x=> !(s x)) := by
    funext x
    cases x <;> rfl
  have plus : 2<(trues c).card := by
    by_contra! low
    have two := at_least_two f fa fb ab
    rw [eq] at two bound
    have force := tiny_shore cc ind c s low two
    omega
  have minus : 2<(trues (fun x=> !(c x))).card := by
    by_contra! low
    have ef : neg e=true := neg_true fe
    have gf : neg g=true := neg_true fg
    have two := at_least_two neg ef gf eg
    have nbound : (boundary (candidate B p) neg).card≤3 := by
      change (boundary (candidate B p) (fun x=> !(f x))).card≤3
      rwa [boundary_compl]
    rw [eqNeg] at two nbound
    have force := tiny_shore cc ind (fun x=> !(c x)) (fun x=> !(s x)) low two
    omega
  obtain ⟨t,ht⟩ := local_cut_domination (c ∘ p) s
  have num : (boundary (ambient B p) (Sum.elim c t)).card≤4 := by
    rw [eq,candidate_boundary] at bound
    rw [ambient_boundary]
    omega
  obtain ⟨z,hz⟩ := cyc5 _ num
  cases z
  · obtain ⟨x,y,z,hx,hy,hzz,xy,xz,yz⟩ := true_triple _ minus
    have flip (q : V) (h : (!(c q))=true) : c q=false := by
      cases e : c q <;> simp_all
    have clash := hz (.inl x) (.inl y) (.inl z) (flip _ hx) (flip _ hy) (flip _ hzz)
    exact clash.elim (fun e=>xy (Sum.inl_injective e))
      (fun e=>e.elim (fun f=>xz (Sum.inl_injective f)) (fun f=>yz (Sum.inl_injective f)))
  · obtain ⟨x,y,z,hx,hy,hzz,xy,xz,yz⟩ := true_triple _ plus
    have clash := hz (.inl x) (.inl y) (.inl z) hx hy hzz
    exact clash.elim (fun e=>xy (Sum.inl_injective e))
      (fun e=>e.elim (fun f=>xz (Sum.inl_injective f)) (fun f=>yz (Sum.inl_injective f)))

/-- This cap is cyclic-four only if the same five exterior edges are
absent: each prohibited adjacency would complete a triangle in it. -/
theorem independent_groups_of_cap_valid {B : SimpleGraph V} [DecidableRel B.Adj] {p : Port↪V}
    (cub : ∀ x,(ambient B p).degree x=3)
    (valid : SmallTrivial (candidate B p)) : IndependentGroups B p := by
  have cc := candidate_cubic B p cub
  have portSize : 5≤Fintype.card V := by simpa using Fintype.card_le_of_injective p p.injective
  have size : 5≤Fintype.card (V⊕Fin 3) := by simp; omega
  apply (groups_iff B p).mpr
  intro i j t _ wi wj edge
  have a : (candidate B p).Adj (Sum.inl (p i)) (Sum.inl (p j)) := edge
  have b : (candidate B p).Adj (Sum.inl (p j)) (Sum.inr t) := ⟨j,rfl,wj⟩
  have c : (candidate B p).Adj (Sum.inr t) (Sum.inl (p i)) := ⟨i,rfl,wi⟩
  exact TwinObstruction.no_triangle valid size a b c (cc _).le (cc _).le (cc _).le

/-- Exact criterion for this particular faithful cap in the cyclic-five
ambient domain. This says nothing about any different possible cap. -/
theorem cap_valid_iff_independent_groups {B : SimpleGraph V} [DecidableRel B.Adj] {p : Port↪V}
    (cub : ∀ x,(ambient B p).degree x=3) (cyc5 : SmallFourTrivial (ambient B p)) :
    SmallTrivial (candidate B p) ↔ IndependentGroups B p :=
  ⟨independent_groups_of_cap_valid cub,cap_valid_of_independent_groups cub cyc5⟩

/-- Reduction using only the cyclic-five graph premise, the three
independent contact groups, and strictly smaller cyclic-four F2. -/
theorem reduce_of_independent_groups
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    {B : SimpleGraph V} [DecidableRel B.Adj] {p : Port↪V}
    (cub : ∀ v,(ambient B p).degree v=3)
    (cyc5 : SmallFourTrivial (ambient B p)) (groups : IndependentGroups B p)
    (order : Fintype.card (V⊕Fin 9)%6=4) :
    FactorOn (target B p) (univ.erase (In 6)) :=
  ThetaSevenFaithfulCap.reduce smaller cub (cap_valid_of_independent_groups cub cyc5 groups) order

#print axioms groups_iff
#print axioms cap_valid_of_independent_groups
#print axioms cap_valid_iff_independent_groups
#print axioms reduce_of_independent_groups
end
end KelmansCactus.AtomicBridge.ThetaSevenFaithfulValid
