import CubicSaving
namespace Graffiti384b.SparsePairs
open Finset SimpleGraph Simplicial16 TwoEars
open private Joint17.eligible Joint17.poolNbr from JointEarSample
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private LowSample.anchor_samples from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
private theorem active29 (X : Finset V) (xs : X.card=29) {v : V} (vx : v∈X) (sat : saturated G v)
    (k d : ℕ) (di : d≤G.degree v) (dr : d<29) :
    (28:ℕ).choose k-FiniteRange.badCount 29 k d≤((X.powersetCard (k+1)).filter (fun s => v∈activated G X s)).card := by
  classical
  let K := (X.erase v).powersetCard k
  let ok := fun s : Finset V => 2≤nbr G v (Xᶜ∪s)
  have total := filter_card_add_filter_neg_card_eq_card (s:=K) ok
  have ks : K.card=(28:ℕ).choose k := by dsimp [K]; rw [card_powersetCard,card_erase_of_mem vx,xs]
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

theorem extra_mass (X E : Finset V) (sz : X.card=29) (sep : Disjoint X E)
    (ind : ∀ u∈E,∀ v∈E,¬G.Adj u v) (two : ∀ v∈E,G.degree v=2)
    (hx : X⊆high G) (inj : Set.InjOn (trianglesAt G) (X:Set V))
    (failure : Fintype.card V<gamma G+16) :
    3*(29:ℕ).choose (11)+(∑ v∈E,(29-nbr G v X).choose (11-nbr G v X))+(∑ v∈X,((X.powersetCard (11)).filter (fun s => v∈activated G X s)).card)+(∑ v∈X,((X.powersetCard (11)).filter (fun s => v∈extra G X E s)).card)≤
      ∑ v∈X,((X.powersetCard (11)).filter (fun s => v∈FiniteRange.bad G X s)).card := by
  classical
  let K := X.powersetCard (11)
  have kc : K.card=(29:ℕ).choose (11) := by dsimp [K]; rw [card_powersetCard,sz]
  have each (s : Finset V) (sm : s∈K) : 3+(Joint17.eligible G X E s).card+(activated G X s).card+(extra G X E s).card≤(FiniteRange.bad G X s).card := by
    obtain ⟨sub,ks⟩ := mem_powersetCard.mp sm
    have z := extra_trial G X E s sep ind two sub hx inj
    rw [card_sdiff sub,sz,ks] at z; omega
  have z := sum_le_sum each
  simp only [sum_add_distrib,sum_const,smul_eq_mul,kc] at z
  have flip (P : Finset V) (F : Finset V → Finset V) (sub : ∀ s∈K,F s⊆P) :
      (∑ s∈K,(F s).card)=∑ v∈P,(K.filter (fun s => v∈F s)).card := by
    calc _ = ∑ s∈K,∑ v∈P,if v∈F s then 1 else 0 := by
             apply sum_congr rfl; intro s sm; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub s sm)]
         _ = _ := by rw [sum_comm]; simp [sum_boole]
  rw [flip X (extra G X E) (fun s sm => (filter_subset ..).trans (mem_powersetCard.mp sm).1),flip X (activated G X) (fun s sm => (filter_subset ..).trans (mem_powersetCard.mp sm).1),flip E (Joint17.eligible G X E) (fun _ _ => filter_subset ..),flip X (FiniteRange.bad G X) (fun _ _ => (filter_subset ..).trans sdiff_subset)] at z
  have fiber (v : V) (vm : v∈E) : (29-nbr G v X).choose (11-nbr G v X)≤(K.filter (fun s => v∈Joint17.eligible G X E s)).card := by
    have small : (Joint17.poolNbr G X v).card≤2 := by
      rw [←two v vm,←card_neighborFinset_eq_degree]
      exact card_le_card (fun i m => (G.mem_neighborFinset ..).mpr (mem_filter.mp m).2)
    have lim := LowSample.anchor_samples X (Joint17.poolNbr G X v) (11) (filter_subset ..) (by omega)
    rw [sz] at lim
    simpa [K,Joint17.eligible,vm,Joint17.poolNbr,nbr] using lim
  have gain := sum_le_sum fiber
  change 3*(29:ℕ).choose (11)+(∑ v∈E,(29-nbr G v X).choose (11-nbr G v X))+(∑ v∈X,(K.filter (fun s => v∈activated G X s)).card)+(∑ v∈X,(K.filter (fun s => v∈extra G X E s)).card)≤∑ v∈X,(K.filter (fun s => v∈FiniteRange.bad G X s)).card
  rw [Nat.mul_comm ((29:ℕ).choose (11)) 3] at z
  omega

theorem cubic29 (X E : Finset V) (xs : X.card=29) {v : V} (vx : v∈X)
    (sc : trianglesAt G v=2) (dg : G.degree v=3) (free : nbr G v E=0) :
    1562275≤((X.powersetCard 11).filter (fun s => v∈extra G X E s)).card := by
  classical
  obtain ⟨A,pa⟩ := protecting_pair G dg sc
  let U := insert v (A∩X)
  have ux : U⊆X := insert_subset vx inter_subset_right
  have size : U.card≤3 := (card_insert_le ..).trans (by have := card_le_card (inter_subset_left (s₁:=A) (s₂:=X)); rw [pa.1] at this; omega)
  have c := LowSample.anchor_samples X U 11 ux (by omega)
  have lim : ∀ j : Fin 4,1562275≤(29-j.val).choose (11-j.val) := by simp only [Nat.choose_eq_fast_choose]; decide
  rw [xs] at c
  refine (lim ⟨U.card,by omega⟩).trans (c.trans (card_le_card ?_))
  intro s sm; obtain ⟨sk,us⟩ := mem_filter.mp sm
  refine mem_filter.mpr ⟨sk,mem_filter.mpr ⟨us (mem_insert_self ..),sc,dg,free,A,pa,?_⟩⟩
  intro i ia; by_cases ix : i∈X
  · exact mem_union_right _ (us (mem_insert_of_mem (mem_inter.mpr ⟨ia,ix⟩)))
  · exact mem_union_left _ (mem_compl.mpr ix)
end Graffiti384b.SparsePairs
#print axioms Graffiti384b.SparsePairs.extra_mass
#print axioms Graffiti384b.SparsePairs.cubic29
