import SimplicialTrial
namespace Graffiti384b.Simplicial16
open Finset SimpleGraph JointRank
open private Joint17.eligible Joint17.poolNbr from JointEarSample
open private Simplicial16.bonus Simplicial16.active_fiber from SimplicialTrial
open private FiniteRange.bad from FiniteRange384b
open private LowSample.anchor_samples from LowSample384b
open private Repair.nbr_add Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Sum the simultaneous ear gains. Each requirement is the exact set of
its neighbors in the sampling pool, irrespective of overlap with another ear. -/
theorem mass_at (k : ℕ) (kl : 8≤k) (ku : k≤9) (X E : Finset V) (sz : X.card=27) (sep : Disjoint X E)
    (ind : ∀ u∈E,∀ v∈E,¬G.Adj u v) (two : ∀ v∈E,G.degree v=2)
    (hx : X⊆high G) (inj : Set.InjOn (trianglesAt G) (X:Set V))
    (n : Fintype.card V=33) (failure : 18≤gamma G) :
    (11-k)*(27:ℕ).choose (k+1)+(∑ v∈E,(27-nbr G v X).choose (k+1-nbr G v X))+(∑ v∈X,((X.powersetCard (k+1)).filter (fun s => v∈activated G X s)).card)≤
      ∑ v∈X,((X.powersetCard (k+1)).filter (fun s => v∈FiniteRange.bad G X s)).card := by
  classical
  let K := X.powersetCard (k+1)
  have kc : K.card=(27:ℕ).choose (k+1) := by dsimp [K]; rw [card_powersetCard,sz]
  have each (s : Finset V) (sm : s∈K) : (11-k)+(Joint17.eligible G X E s).card+(activated G X s).card≤(FiniteRange.bad G X s).card := by
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
  rw [flip X (activated G X) (fun s sm => (filter_subset ..).trans (mem_powersetCard.mp sm).1),flip E (Joint17.eligible G X E) (fun _ _ => filter_subset ..),flip X (FiniteRange.bad G X) (fun _ _ => (filter_subset ..).trans sdiff_subset)] at z
  have fiber (v : V) (vm : v∈E) : (27-nbr G v X).choose (k+1-nbr G v X)≤(K.filter (fun s => v∈Joint17.eligible G X E s)).card := by
    have small : (Joint17.poolNbr G X v).card≤2 := by
      rw [←two v vm,←card_neighborFinset_eq_degree]
      exact card_le_card (fun i m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2)
    have lim := LowSample.anchor_samples X (Joint17.poolNbr G X v) (k+1) (filter_subset ..) (by omega)
    rw [sz] at lim
    simpa [K,Joint17.eligible,vm,Joint17.poolNbr,nbr] using lim
  have gain := sum_le_sum fiber
  change (11-k)*(27:ℕ).choose (k+1)+(∑ v∈E,(27-nbr G v X).choose (k+1-nbr G v X))+(∑ v∈X,(K.filter (fun s => v∈activated G X s)).card)≤∑ v∈X,(K.filter (fun s => v∈FiniteRange.bad G X s)).card
  rw [Nat.mul_comm ((27:ℕ).choose (k+1)) (11-k)] at z
  omega

theorem mass (X E : Finset V) (sz : X.card=27) (sep : Disjoint X E)
    (ind : ∀ u∈E,∀ v∈E,¬G.Adj u v) (two : ∀ v∈E,G.degree v=2)
    (hx : X⊆high G) (inj : Set.InjOn (trianglesAt G) (X:Set V))
    (n : Fintype.card V=33) (failure : 18≤gamma G) :
    3*4686825+(∑ v∈E,(27-nbr G v X).choose (9-nbr G v X))+(∑ v∈X,((X.powersetCard 9).filter (fun s => v∈activated G X s)).card)≤
      ∑ v∈X,((X.powersetCard 9).filter (fun s => v∈FiniteRange.bad G X s)).card := by
  have z := mass_at G 8 (by decide) (by decide) X E sz sep ind two hx inj n failure
  change 3*(27:ℕ).choose 9+_+_≤_ at z
  rwa [show (27:ℕ).choose 9=4686825 by rw [Nat.choose_eq_fast_choose]; decide] at z

private def row (r : ℕ) := if r=0 then 2288132 else if r=1 then 1951642 else if r<4 then 1776500
  else if r<8 then 1311380 else if r<13 then 923780 else if r<19 then 621452 else 545870

private def refund (r d : ℕ) := if r+2=d.choose 2 then Simplicial16.bonus d else 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem table : (∀ r : Fin 27,∀ d : Fin 11,∀ a : Fin 2,∀ b : Fin 3,
    (r.val+2≤d.val.choose 2 ∨ d.val=10) → 3≤d.val →
    EarCredit.Pair.loss d (a.val+b.val)+453492*a.val+46189*b.val≤row r+refund r d) ∧
    (∑ r∈range 27,row r)=25752866 := by
  unfold EarCredit.Pair.loss refund Simplicial16.bonus FiniteRange.badCount row; simp only [Nat.choose_eq_fast_choose]; decide

/-- Each paid incidence to either other ear is counted individually, including
when an exterior vertex is adjacent to both. The rank pays for both charges. -/
theorem ranked (X A F : Finset V) (sz : X.card=27) (sep : Disjoint (A∪F) X)
    (hx : X⊆high G) (af : Disjoint A F) (ca : ∀ v∈X,nbr G v A≤1) (cf : F.card=2)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v) :
    (∑ v∈X,((X.powersetCard 9).filter (fun s => v∈FiniteRange.bad G X s)).card)+
      453492*(∑ v∈X,nbr G v A)+46189*(∑ v∈X,nbr G v F)≤25752866+(∑ v∈X,((X.powersetCard 9).filter (fun s => v∈activated G X s)).card) := by
  classical
  let bill := fun v => ((X.powersetCard 9).filter (fun s => v∈FiniteRange.bad G X s)).card
  let act := fun v => ((X.powersetCard 9).filter (fun s => v∈activated G X s)).card
  let r := rank X (trianglesAt G)
  have each (v : V) (vm : v∈X) : bill v+453492*nbr G v A+46189*nbr G v F≤row (r v)+act v := by
    have rk := mem_image_of_mem (rank X (trianglesAt G)) vm
    rw [rank_range X _ inj,sz,mem_range] at rk
    have lr := rank_lower X (trianglesAt G) inj 2 lo vm
    let d := min (G.degree v) 10
    have dm : d≤10 := min_le_right .. 
    have dc : r v+2≤d.choose 2 ∨ d=10 := by
      by_cases hd : G.degree v≤10
      · rw [show d=G.degree v from min_eq_left hd,Nat.add_comm]; exact Or.inl (lr.trans (Repair.triangles_le_choose G v))
      · exact Or.inr (min_eq_right (by omega))
    have b := EarCredit.Pair.pair_fiber G sz sep vm
    rw [Repair.nbr_add G v af] at b
    have cf' := card_le_card (filter_subset (G.Adj v) F)
    have z := table.1 ⟨r v,rk⟩ ⟨d,by omega⟩ ⟨nbr G v A,by have := ca v vm; omega⟩
      ⟨nbr G v F,by unfold nbr; omega⟩ dc (le_min (mem_filter.mp (hx vm)).2 (by decide))
    have rb : refund (r v) d≤act v := by
      unfold refund; split_ifs with eq
      · have lt : d<10 := by
          by_contra! ge
          have ten : d=10 := by omega
          rw [ten,show (10:ℕ).choose 2=45 by decide] at eq
          change r v<27 at rk; omega
        have de : d=G.degree v := by dsimp [d] at *; omega
        have sat : saturated G v := by
          unfold saturated
          apply Nat.le_antisymm (Repair.triangles_le_choose G v)
          rw [←de,←eq,Nat.add_comm]; exact lr
        exact Simplicial16.active_fiber G X sz vm sat 8 d (min_le_left ..) (by omega)
      · exact Nat.zero_le _
    exact ((Nat.add_le_add_right (Nat.add_le_add_right b _) _).trans z).trans (Nat.add_le_add_left rb _)
  have sum := sum_le_sum each
  simp only [sum_add_distrib,←mul_sum] at sum
  rwa [sum_by_rank X _ inj row,sz,table.2] at sum

end Graffiti384b.Simplicial16
#print axioms Graffiti384b.Simplicial16.mass_at
#print axioms Graffiti384b.Simplicial16.mass
#print axioms Graffiti384b.Simplicial16.ranked
