import ThetaAsymmetricFaithfulTiny
import TwinObstruction

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaAsymmetricFaithfulValid
open SquareCap (boundary SmallTrivial FactorOn)
open PentagonCap (SmallFourTrivial)
open ThetaAsymmetricFaithfulTable (Wire local_cut_domination)
open ThetaAsymmetricFaithful (ambient candidate target reduce_of_valid_cap)
open ThetaAsymmetricFaithfulGeometry (ProperWires candidate_cubic candidate_boundary ambient_boundary attach root3 unique3 candidate_exact)
open ThetaAsymmetricFaithfulTiny (IndependentContacts tiny_shore)
open ThetaSevenFaithfulRefill (In)
open ThetaSevenFaithfulTiny (trues mem_trues boundary_compl)
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

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
theorem cap_valid_of_independent_contacts {B : SimpleGraph V} [DecidableRel B.Adj] {p : Wire→V}
    (proper : ProperWires p) (cub : ∀ x,(ambient B p).degree x=3)
    (cyc5 : SmallFourTrivial (ambient B p)) (ind : IndependentContacts B p) : SmallTrivial (candidate B p) := by
  classical
  have cc := candidate_cubic B p proper cub
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
    have force := tiny_shore cc proper ind c s low two
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
    have force := tiny_shore cc proper ind (fun x=> !(c x)) (fun x=> !(s x)) low two
    omega
  obtain ⟨t,ht⟩ := local_cut_domination (fun i=>c (p i)) s
  have num : (boundary (ambient B p) (Sum.elim c t)).card≤4 := by
    rw [eq,candidate_boundary B p proper] at bound
    rw [ambient_boundary B p proper]
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


omit [DecidableEq V] in
theorem properly_many (p : Wire→V) (proper : ProperWires p) :
    4≤Fintype.card V := by
  let fn (i : Fin 4) : V := p ⟨i.val,by have z:=i.isLt; omega⟩
  have hinj : Function.Injective fn := by
    intro i j eq
    have hi : i.val<4 := i.isLt
    have hj : j.val<4 := j.isLt
    have H := proper.1 ⟨i.val,by omega⟩ ⟨j.val,by omega⟩ hi hj eq
    exact Fin.ext (congrArg (fun i : Wire=>i.val) H)
  simpa using Fintype.card_le_of_injective fn hinj

/-- The asymmetric three-cap has exactly the explicit contact-group
adjacencies as potential obstructions in the cyclic-five domain. -/
theorem cap_valid_iff_independent_contacts {B : SimpleGraph V} [DecidableRel B.Adj]
    {p : Wire→V} (proper : ProperWires p) (cub : ∀ x,(ambient B p).degree x=3)
    (cyc5 : SmallFourTrivial (ambient B p)) :
    SmallTrivial (candidate B p) ↔ IndependentContacts B p := by
  refine ⟨?_,cap_valid_of_independent_contacts proper cub cyc5⟩
  intro valid i j _ same edge
  let C := candidate B p
  have cc := candidate_cubic B p proper cub
  have base := properly_many p proper
  have size : 5≤Fintype.card (V⊕Fin 3) := by simp; omega
  have A : C.Adj (Sum.inl (p i)) (Sum.inl (p j)) := edge
  have B' : C.Adj (Sum.inl (p j)) (Sum.inr (root3 i)) := by
    change (candidate B p).Adj _ _
    rw [candidate_exact]
    exact ⟨j,rfl,same.symm⟩
  have C' : C.Adj (Sum.inr (root3 i)) (Sum.inl (p i)) := by
    change (candidate B p).Adj _ _
    rw [candidate_exact]
    exact ⟨i,rfl,rfl⟩
  exact TwinObstruction.no_triangle valid size A B' C' (cc _).le (cc _).le (cc _).le

theorem reduce_of_independent_contacts
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    {B : SimpleGraph V} [DecidableRel B.Adj] {p : Wire→V}
    (proper : ProperWires p) (cub : ∀ x,(ambient B p).degree x=3)
    (cyc5 : SmallFourTrivial (ambient B p)) (ind : IndependentContacts B p)
    (order : Fintype.card (V⊕Fin 9)%6=4) :
    FactorOn (target B p) (univ.erase (In 6)) := by
  have dn : p 0≠p 3 := fun eq=>(by decide : (0:Wire)≠3) (proper.1 0 3 (by decide) (by decide) eq)
  have large := properly_many p proper
  exact reduce_of_valid_cap smaller dn (by omega) (candidate_cubic B p proper cub)
    (cap_valid_of_independent_contacts proper cub cyc5 ind) order

#print axioms cap_valid_iff_independent_contacts
#print axioms reduce_of_independent_contacts
end
end KelmansCactus.AtomicBridge.ThetaAsymmetricFaithfulValid
