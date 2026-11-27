import ThetaAsymmetricFaithfulTriangleTiny
import ThetaAsymmetricFaithfulScope

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaAsymmetricFaithfulTriangleCuts
open SquareCap (boundary)
open PentagonCap (SmallFourTrivial)
open ThetaAsymmetricFaithful (ambient candidate)
open ThetaAsymmetricFaithfulTable (Wire local_cut_domination)
open ThetaAsymmetricFaithfulGeometry (candidate_cubic candidate_boundary ambient_boundary root3)
open ThetaAsymmetricFaithfulScope (proper_of_four_injective faithful_contacts_independent)
open ThetaAsymmetricFaithfulTriangleTiny (tiny_shore IndependentBC exceptionalShore)
open ThetaSevenFaithfulTiny (trues mem_trues boundary_compl)

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {B : SimpleGraph V} [DecidableRel B.Adj] {p : Wire→V}

private theorem bc_independent_of_no_ear (cub : ∀ x,(ambient B p).degree x=3)
    (cyc5 : SmallFourTrivial (ambient B p)) (safe : ¬B.Adj (p 0) (p 3)) :
    IndependentBC B p := by
  obtain ⟨a,b,c⟩ := faithful_contacts_independent cub cyc5
  let P : List (Wire×Wire) := [(0,3),(4,5),(4,6),(5,6)]
  have listed : ∀ i j : Wire,i≠j→ root3 i=root3 j→ root3 i≠0→(i,j)∈P∨(j,i)∈P := by decide
  have deny (u v : Wire) (h : (u,v)∈P) : ¬B.Adj (p u) (p v) := by
    simp [P] at h
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> assumption
  intro i j ij same h
  rcases listed i j ij same h with e|e
  · exact deny i j e
  · exact fun w=>deny j i e w.symm

private theorem triple (c : V→Bool) (size : 2<(trues c).card) :
    ∃ x y z : V,c x=true∧c y=true∧c z=true∧x≠y∧x≠z∧y≠z := by
  obtain ⟨x,xc,y,yc,xy⟩ := one_lt_card.mp (by omega : 1<(trues c).card)
  have two : ({x,y}:Finset V).card=2 := by simp [card_insert_of_not_mem,xy]
  obtain ⟨z,zc,nd⟩ := exists_mem_not_mem_of_card_lt_card (by omega : ({x,y}:Finset V).card<(trues c).card)
  have nd' : z≠x∧z≠y := by simpa using nd
  exact ⟨x,y,z,mem_trues.mp xc,mem_trues.mp yc,mem_trues.mp zc,xy,nd'.1.symm,nd'.2.symm⟩

/-- The cut geometry does not assume p2--p3 absent. Every nontrivial
three-edge-or-smaller cut then has the exact exceptional vertex triple
as one shore. If the edge exists, that triple is a real triangle. -/
theorem only_triangle_shore (cub : ∀ x,(ambient B p).degree x=3)
    (cyc5 : SmallFourTrivial (ambient B p))
    (four : ∀ i j : Wire,i.val<4→j.val<4→p i=p j→i=j)
    (safe : ¬B.Adj (p 0) (p 3)) (f : V⊕Fin 3→Bool)
    (budget : (boundary (candidate B p) f).card≤3)
    (pos : 2≤(trues f).card) (neg : 2≤(trues (fun x=> !(f x))).card) :
    trues f=exceptionalShore p ∨ trues (fun x=> !(f x))=exceptionalShore p := by
  classical
  have proper := proper_of_four_injective cub cyc5 four
  have cc := candidate_cubic B p proper cub
  have ind := bc_independent_of_no_ear cub cyc5 safe
  let c : V→Bool := f ∘ Sum.inl
  let s : Fin 3→Bool := f ∘ Sum.inr
  have eq : f=Sum.elim c s := by funext x; cases x <;> rfl
  have eqN : (fun x=> !(f x))=Sum.elim (fun x=> !(c x)) (fun x=> !(s x)) := by
    funext x
    cases x <;> rfl
  by_cases first : (trues c).card≤2
  · have pp : 2≤(trues (Sum.elim c s)).card := by rwa [←eq]
    rcases tiny_shore cc proper ind c s first pp with low|exact
    · rw [←eq] at low
      omega
    · exact Or.inl (eq.symm ▸ exact)
  by_cases second : (trues (fun x=> !(c x))).card≤2
  · have pp : 2≤(trues (Sum.elim (fun x=> !(c x)) (fun x=> !(s x)))).card := by rwa [←eqN]
    rcases tiny_shore cc proper ind (fun x=> !(c x)) (fun x=> !(s x)) second pp with low|exact
    · rw [←eqN,boundary_compl] at low
      omega
    · exact Or.inr (eqN.symm ▸ exact)
  obtain ⟨t,ht⟩ := local_cut_domination (fun i=>c (p i)) s
  have num : (boundary (ambient B p) (Sum.elim c t)).card≤4 := by
    rw [eq,candidate_boundary B p proper] at budget
    rw [ambient_boundary B p proper]
    omega
  obtain ⟨q,hq⟩ := cyc5 _ num
  exfalso
  cases q
  · obtain ⟨u,v,w,hu,hv,hw,uv,uw,vw⟩ := triple _ (by omega : 2<(trues (fun x=> !(c x))).card)
    have toF (x : V) (h : (!(c x))=true) : c x=false := by simpa using h
    exact (hq (.inl u) (.inl v) (.inl w) (toF _ hu) (toF _ hv) (toF _ hw)).elim
      (fun e=>uv (Sum.inl_injective e))
      (fun e=>e.elim (fun d=>uw (Sum.inl_injective d)) (fun d=>vw (Sum.inl_injective d)))
  · obtain ⟨u,v,w,hu,hv,hw,uv,uw,vw⟩ := triple _ (by omega : 2<(trues c).card)
    exact (hq (.inl u) (.inl v) (.inl w) hu hv hw).elim
      (fun e=>uv (Sum.inl_injective e))
      (fun e=>e.elim (fun d=>uw (Sum.inl_injective d)) (fun d=>vw (Sum.inl_injective d)))

#print axioms only_triangle_shore
end
end KelmansCactus.AtomicBridge.ThetaAsymmetricFaithfulTriangleCuts
