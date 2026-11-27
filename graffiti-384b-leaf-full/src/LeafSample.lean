import CleanFinish
namespace Graffiti384b.LeafPath
open Finset SimpleGraph Simplicial16 JointRank
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private Joint17.eligible Joint17.poolNbr from JointEarSample
open private LowSample.anchor_samples from LowSample384b
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
private theorem active28 (X : Finset V) (xs : X.card=28) {v : V} (vx : v∈X) (sat : saturated G v)
    (k d : ℕ) (di : d≤G.degree v) (dr : d<28) :
    (27:ℕ).choose k-FiniteRange.badCount 28 k d≤((X.powersetCard (k+1)).filter (fun s => v∈activated G X s)).card := by
  classical
  let K := (X.erase v).powersetCard k
  let ok := fun s : Finset V => 2≤nbr G v (Xᶜ∪s)
  have total := filter_card_add_filter_neg_card_eq_card (s:=K) ok
  have ks : K.card=(27:ℕ).choose k := by dsimp [K]; rw [card_powersetCard,card_erase_of_mem vx,xs]
  have fail : K.filter (fun s => ¬ok s)⊆(X.powersetCard k).filter (fun s => v∈FiniteRange.bad G X s) := by
    intro s sm
    obtain ⟨sk,no⟩ := mem_filter.mp sm
    obtain ⟨se,sc⟩ := mem_powersetCard.mp sk
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨se.trans (erase_subset ..),sc⟩,
      mem_filter.mpr ⟨mem_sdiff.mpr ⟨vx,fun vs => (mem_erase.mp (se vs)).1 rfl⟩,Nat.lt_of_not_ge no⟩⟩
  have bound := FiniteRange.count_bad G X k d v vx di (xs ▸ dr)
  rw [xs] at bound
  have small := (card_le_card fail).trans bound
  let good := K.filter ok
  have off {s : Finset V} (sm : s∈good) : v∉s := fun vs =>
    (mem_erase.mp ((mem_powersetCard.mp (mem_filter.mp sm).1).1 vs)).1 rfl
  have inj : Set.InjOn (insert v) (good:Set (Finset V)) := by
    intro s sm t tm eq
    simpa [erase_insert (off sm),erase_insert (off tm)] using congrArg (fun S : Finset V => S.erase v) eq
  have inc : good.image (insert v)⊆(X.powersetCard (k+1)).filter (fun s => v∈activated G X s) := by
    intro t tm
    obtain ⟨s,sm,rfl⟩ := mem_image.mp tm
    obtain ⟨ks',yes⟩ := mem_filter.mp sm
    obtain ⟨se,sc⟩ := mem_powersetCard.mp ks'
    have sub := insert_subset vx (se.trans (erase_subset ..))
    have ct := card_insert_of_not_mem (off sm)
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sub,by omega⟩,mem_filter.mpr ⟨mem_insert_self ..,sat,?_⟩⟩
    exact yes.trans (card_le_card (filter_subset_filter _ (union_subset_union Subset.rfl (subset_insert ..))))
  have count := card_le_card inc
  rw [card_image_of_injOn inj] at count
  change good.card+_=K.card at total
  omega

theorem mass (X E : Finset V) (sz : X.card=28) (sep : Disjoint X E)
    (ind : ∀ u∈E,∀ v∈E,¬G.Adj u v) (two : ∀ v∈E,G.degree v=2)
    (hx : X⊆high G) (inj : Set.InjOn (trianglesAt G) (X:Set V))
    (n : Fintype.card V=33) (failure : 18≤gamma G) :
    2*(28:ℕ).choose 11+(∑ v∈E,(28-nbr G v X).choose (11-nbr G v X))+(∑ v∈X,((X.powersetCard 11).filter (fun s => v∈activated G X s)).card)≤
      ∑ v∈X,((X.powersetCard 11).filter (fun s => v∈FiniteRange.bad G X s)).card := by
  classical
  let K := X.powersetCard 11
  have kc : K.card=(28:ℕ).choose 11 := by dsimp [K]; rw [card_powersetCard,sz]
  have each (s : Finset V) (sm : s∈K) : 2+(Joint17.eligible G X E s).card+(activated G X s).card≤(FiniteRange.bad G X s).card := by
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
  have fiber (v : V) (vm : v∈E) : (28-nbr G v X).choose (11-nbr G v X)≤(K.filter (fun s => v∈Joint17.eligible G X E s)).card := by
    have small : (Joint17.poolNbr G X v).card≤2 := by
      rw [←two v vm,←card_neighborFinset_eq_degree]
      exact card_le_card (fun i m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2)
    have lim := LowSample.anchor_samples X (Joint17.poolNbr G X v) 11 (filter_subset ..) (by omega)
    rw [sz] at lim
    simpa [K,Joint17.eligible,vm,Joint17.poolNbr,nbr] using lim
  have gain := sum_le_sum fiber
  change 2*(28:ℕ).choose 11+(∑ v∈E,(28-nbr G v X).choose (11-nbr G v X))+(∑ v∈X,(K.filter (fun s => v∈activated G X s)).card)≤∑ v∈X,(K.filter (fun s => v∈FiniteRange.bad G X s)).card
  rw [Nat.mul_comm ((28:ℕ).choose 11) 2] at z
  omega

private def row (r : ℕ) := if r=0 then 8379912 else if r<4 then 5928342 else if r<8 then 3938662
  else if r<13 then 2469012 else if r<19 then 1461252 else if r<26 then 814606 else 425646
private def refund (r d : ℕ) := if r+2=d.choose 2 then (27:ℕ).choose 10-FiniteRange.badCount 28 10 d else 0
set_option maxRecDepth 65536 in
private theorem costs : (∀ r : Fin 28,∀ d : Fin 11,3≤d.val →
    (r.val+2≤d.val.choose 2 ∨ d.val=10) → FiniteRange.badCount 28 11 d≤row r+refund r d) ∧
    (∑ r∈range 28,row r)=69585692 := by
  unfold row refund FiniteRange.badCount; simp only [Nat.choose_eq_fast_choose]; decide

theorem ranked (X : Finset V) (sz : X.card=28) (hx : X⊆high G)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v) :
    (∑ v∈X,((X.powersetCard 11).filter (fun s => v∈FiniteRange.bad G X s)).card)≤
      69585692+(∑ v∈X,((X.powersetCard 11).filter (fun s => v∈activated G X s)).card) := by
  classical
  let r := rank X (trianglesAt G)
  have each (v : V) (vm : v∈X) :
      ((X.powersetCard 11).filter (fun s => v∈FiniteRange.bad G X s)).card≤row (r v)+
        ((X.powersetCard 11).filter (fun s => v∈activated G X s)).card := by
    let d := min (G.degree v) 10
    have dm : d≤10 := min_le_right ..
    have dr : d≤G.degree v := min_le_left ..
    have rk := mem_image_of_mem (rank X (trianglesAt G)) vm
    rw [rank_range X _ inj,sz,mem_range] at rk
    change r v<28 at rk
    have lr := rank_lower X (trianglesAt G) inj 2 lo vm
    change 2+r v≤trianglesAt G v at lr
    have cap := Repair.triangles_le_choose G v
    have dc : r v+2≤d.choose 2 ∨ d=10 := by
      by_cases eq : G.degree v≤10
      · rw [show d=G.degree v from min_eq_left eq]; exact Or.inl (by omega)
      · exact Or.inr (min_eq_right (by omega))
    have z := costs.1 ⟨r v,rk⟩ ⟨d,by omega⟩ (le_min (mem_filter.mp (hx vm)).2 (by decide)) dc
    have bill := FiniteRange.count_bad G X 11 d v vm dr (sz ▸ (by omega))
    rw [sz] at bill
    refine bill.trans (z.trans (Nat.add_le_add_left ?_ _))
    unfold refund; split_ifs with eq
    · change r v+2=d.choose 2 at eq
      have lt : d<10 := by
        by_cases ten : d=10
        · rw [ten,show (10:ℕ).choose 2=45 by decide] at eq; omega
        · omega
      have dg : d=G.degree v := by dsimp [d] at *; omega
      have sat : saturated G v := by unfold saturated; rw [←dg]; rw [←dg] at cap; omega
      exact active28 G X sz vm sat 10 d dr (by omega)
    · exact Nat.zero_le _
  have sum := sum_le_sum each
  rwa [sum_add_distrib,sum_by_rank X _ inj row,sz,costs.2] at sum

end Graffiti384b.LeafPath
#print axioms Graffiti384b.LeafPath.mass
#print axioms Graffiti384b.LeafPath.ranked
