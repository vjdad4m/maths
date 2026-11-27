import SimplicialTrial
import CliquePool
namespace Graffiti384b.Shared
open Finset SimpleGraph JointRank
open private Joint17.eligible Joint17.poolNbr from JointEarSample
open private Simplicial16.bonus Simplicial16.active_fiber from SimplicialTrial
open private FiniteRange.bad from FiniteRange384b
open private LowSample.anchor_samples from LowSample384b
open private Repair.nbr_add Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Sum the simultaneous ear gains. Each requirement is the exact set of
its neighbors in the sampling pool, irrespective of overlap with another ear. -/
theorem mass_at (X E : Finset V) (sz : X.card=26) (sep : Disjoint X E)
    (ind : ∀ u∈E,∀ v∈E,¬G.Adj u v) (two : ∀ v∈E,G.degree v=2)
    (hx : X⊆high G) (inj : Set.InjOn (trianglesAt G) (X:Set V))
    (n : Fintype.card V=33) (failure : 18≤gamma G) :
    2*(26:ℕ).choose (9)+(∑ v∈E,(26-nbr G v X).choose (9-nbr G v X))+(∑ v∈X,((X.powersetCard (9)).filter (fun s => v∈Simplicial16.activated G X s)).card)≤
      ∑ v∈X,((X.powersetCard (9)).filter (fun s => v∈FiniteRange.bad G X s)).card := by
  classical
  let K := X.powersetCard (9)
  have kc : K.card=(26:ℕ).choose (9) := by dsimp [K]; rw [card_powersetCard,sz]
  have each (s : Finset V) (sm : s∈K) : 2+(Joint17.eligible G X E s).card+(Simplicial16.activated G X s).card≤(FiniteRange.bad G X s).card := by
    obtain ⟨sub,ks⟩ := mem_powersetCard.mp sm
    have z := Simplicial16.trial G X E s sep ind two sub hx inj
    rw [card_sdiff sub,sz,ks,n] at z; omega
  have z := sum_le_sum each
  simp only [sum_add_distrib,sum_const,smul_eq_mul,kc] at z
  have flip (P : Finset V) (F : Finset V → Finset V) (sub : ∀ s∈K,F s⊆P) :
      (∑ s∈K,(F s).card)=∑ v∈P,(K.filter (fun s => v∈F s)).card := by
    calc _ = ∑ s∈K,∑ v∈P,if v∈F s then 1 else 0 := by
             apply sum_congr rfl; intro s sm; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub s sm)]
         _ = _ := by rw [sum_comm]; simp [sum_boole]
  rw [flip X (Simplicial16.activated G X) (fun s sm => (filter_subset ..).trans (mem_powersetCard.mp sm).1),flip E (Joint17.eligible G X E) (fun _ _ => filter_subset ..),flip X (FiniteRange.bad G X) (fun _ _ => (filter_subset ..).trans sdiff_subset)] at z
  have fiber (v : V) (vm : v∈E) : (26-nbr G v X).choose (9-nbr G v X)≤(K.filter (fun s => v∈Joint17.eligible G X E s)).card := by
    have small : (Joint17.poolNbr G X v).card≤2 := by
      rw [←two v vm,←card_neighborFinset_eq_degree]
      exact card_le_card (fun i m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2)
    have lim := LowSample.anchor_samples X (Joint17.poolNbr G X v) (9) (filter_subset ..) (by omega)
    rw [sz] at lim
    simpa [K,Joint17.eligible,vm,Joint17.poolNbr,nbr] using lim
  have gain := sum_le_sum fiber
  change 2*(26:ℕ).choose (9)+(∑ v∈E,(26-nbr G v X).choose (9-nbr G v X))+(∑ v∈X,(K.filter (fun s => v∈Simplicial16.activated G X s)).card)≤∑ v∈X,(K.filter (fun s => v∈FiniteRange.bad G X s)).card
  rw [Nat.mul_comm ((26:ℕ).choose (9)) 2] at z
  omega

end Graffiti384b.Shared
#print axioms Graffiti384b.Shared.mass_at
