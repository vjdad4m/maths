import CleanTrial
namespace Graffiti384b.PendantRank
open Finset SimpleGraph Donor JointRank
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private Repair.triangles_le_choose from Repair384b
open private Donor.rankDegree from PendantBudget
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem fiber (X : Finset V) (xs : X.card=26) {v : V} (vx : v∈X) (sat : trianglesAt G v=(G.degree v).choose 2)
    (k d : ℕ) (di : d≤G.degree v) (dr : d<26) :
    (25:ℕ).choose k-FiniteRange.badCount 26 k d≤((X.powersetCard (k+1)).filter (fun s => v∈active G X s)).card := by
  classical
  let K := (X.erase v).powersetCard k
  let ok := fun s : Finset V => 2≤nbr G v (Xᶜ∪s)
  have total := filter_card_add_filter_neg_card_eq_card (s:=K) ok
  have ks : K.card=(25:ℕ).choose k := by dsimp [K]; rw [card_powersetCard,card_erase_of_mem vx,xs]
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
  have inc : good.image (insert v)⊆(X.powersetCard (k+1)).filter (fun s => v∈active G X s) := by
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

def base := (25:ℕ).choose 9
def reward (d : ℕ) := base-FiniteRange.badCount 26 9 d
def charge (p d : ℕ) := max (FiniteRange.badCount 26 10 d) ((26-d).choose 10+p)
def envelope (floor p i : ℕ) :=
  let d := max floor (Donor.rankDegree i)
  if i+2=d.choose 2 then
    max (base+charge p (d+1)) (base+charge p d-reward d)
  else base+charge p d

def tariff (d : ℕ) := if d≤4 then 591790 else if d≤5 then 381840 else if d≤6 then 171890 else 0

def marked (X : Finset V) (v : V) := if v∈exposed G X then tariff (G.degree v) else 0

private theorem exposure_credit (j d p : ℕ) (low : 3≤j) (le : j≤d) (cap : p≤290000) :
    (26-j).choose 10+p+tariff d≤charge p j := by
  by_cases small : d≤6
  · have tab : ∀ i h : Fin 7,3≤ i.val → i.val≤h.val →
        (26-i.val).choose 10+290000+tariff h.val≤FiniteRange.badCount 26 10 i.val := by
      unfold tariff FiniteRange.badCount
      simp only [Nat.choose_eq_fast_choose]
      decide
    have upper := tab ⟨j,by omega⟩ ⟨d,by omega⟩ low le
    change (26-j).choose 10+290000+tariff d≤FiniteRange.badCount 26 10 j at upper
    exact (show (26-j).choose 10+p+tariff d≤FiniteRange.badCount 26 10 j by omega).trans (le_max_left ..)
  · have zero : tariff d=0 := by unfold tariff; split_ifs <;> omega
    simpa only [zero,Nat.add_zero] using (le_max_right (FiniteRange.badCount 26 10 j) ((26-j).choose 10+p))

/-- At a rank equal to a binomial triangle cap, either the vertex is
simplicial or its degree must increase by at least one. -/
theorem rank_budget (X : Finset V) (sz : X.card=26)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (pos : ∀v∈X,2≤trianglesAt G v)
    (floor p : ℕ) (pcap : p≤290000) (fs : floor≤8) (degrees : ∀v∈X,floor≤G.degree v) :
    (∑ k∈X.powersetCard 10,(FiniteRange.bad G X k).card)+(exposed G X).card*p+(∑v∈X,marked G X v)+26*base ≤
      (∑ i∈range 26,envelope floor p i)+(∑ k∈X.powersetCard 10,(active G X k).card) := by
  classical
  let rank' := rank X (trianglesAt G)
  let B (v : V) := ((X.powersetCard 10).filter (fun k => v∈FiniteRange.bad G X k)).card
  let A (v : V) := ((X.powersetCard 10).filter (fun k => v∈active G X k)).card
  let price (v : V) := if v∈exposed G X then p else 0
  have each (v : V) (vm : v∈X) : B v+price v+marked G X v+base≤envelope floor p (rank' v)+A v := by
    have ri : rank' v<26 := mem_range.mp (by rw [←sz,←rank_range X (trianglesAt G) inj]; exact mem_image_of_mem _ vm)
    have lo := rank_lower X (trianglesAt G) inj 2 pos vm
    change 2+rank' v≤trianglesAt G v at lo
    have cap := Repair.triangles_le_choose G v
    have ds : Donor.rankDegree (rank' v)≤8 := by unfold Donor.rankDegree; split_ifs <;> decide
    have req : Donor.rankDegree (rank' v)≤G.degree v := by
      by_cases big : 8≤G.degree v
      · exact ds.trans big
      have tab : ∀d : Fin 8,∀r : Fin 26,2+r.val≤d.val.choose 2 → Donor.rankDegree r≤d := by decide
      exact tab ⟨_,Nat.lt_of_not_ge big⟩ ⟨_,ri⟩ (lo.trans cap)
    let d := max floor (Donor.rankDegree (rank' v))
    have den : d≤G.degree v := max_le (degrees v vm) req
    have du : d≤8 := max_le fs ds
    have do' : 3≤d := by dsimp [d]; unfold Donor.rankDegree; split_ifs <;> omega
    have lim (j : ℕ) (low : 3≤j) (up : j<26) (dj : j≤G.degree v) : B v+price v+marked G X v≤charge p j := by
      by_cases ext : v∈exposed G X
      · obtain ⟨w,wx,vw⟩ := (mem_filter.mp ext).2
        have lim := BoundaryFiber.count G X 10 j vm wx vw dj (by omega)
        rw [sz] at lim
        change B v≤(26-j).choose 10 at lim
        simp only [price,marked,if_pos ext]
        exact (Nat.add_le_add_right (Nat.add_le_add_right lim p) _).trans (exposure_credit j (G.degree v) p low dj pcap)
      · have lim := FiniteRange.count_bad G X 10 j v vm dj (by omega)
        rw [sz] at lim
        exact (show B v+price v+marked G X v≤FiniteRange.badCount 26 10 j by simpa [price,marked,ext] using lim).trans (le_max_left ..)
    change _≤(if rank' v+2=d.choose 2 then max (base+charge p (d+1)) (base+charge p d-reward d) else base+charge p d)+_
    by_cases top : rank' v+2=d.choose 2
    · rw [if_pos top]
      by_cases exactD : G.degree v=d
      · have sat : trianglesAt G v=(G.degree v).choose 2 := by rw [exactD] at cap ⊢; omega
        have gain : reward d≤A v := fiber G X sz vm sat 9 d den (by omega)
        have cheap := lim d do' (by omega) den
        have rewardMax : reward d≤base := Nat.sub_le .. 
        have m := le_max_right (base+charge p (d+1)) (base+charge p d-reward d)
        omega
      · have cheap := lim (d+1) (by omega) (by omega) (by omega)
        have m := le_max_left (base+charge p (d+1)) (base+charge p d-reward d)
        omega
    · rw [if_neg top]
      have cheap := lim d do' (by omega) den
      omega
  have doubleCount (f : Finset V→Finset V) (sub : ∀k∈X.powersetCard 10,f k⊆X) :
      (∑ k∈X.powersetCard 10,(f k).card)=∑v∈X,((X.powersetCard 10).filter (fun k => v∈f k)).card := by
    calc
      _ = ∑k∈X.powersetCard 10,∑v∈X, (if v∈f k then 1 else 0 : ℕ) := by
        apply sum_congr rfl
        intro k km
        simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub k km)]
      _ = _ := by rw [sum_comm]; simp
  have total := sum_le_sum each
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,sz] at total
  rw [sum_by_rank X (trianglesAt G) inj,sz] at total
  have credit : (∑v∈X,price v)=(exposed G X).card*p := by
    simp only [price,←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr (show exposed G X⊆X from filter_subset ..),sum_const,nsmul_eq_mul,Nat.cast_id]
  rw [doubleCount (FiniteRange.bad G X) (fun _ _ => (filter_subset ..).trans sdiff_subset),doubleCount (active G X)
    (fun _ km => (filter_subset ..).trans (mem_powersetCard.mp km).1),←credit]
  exact total

end Graffiti384b.PendantRank
#print axioms Graffiti384b.PendantRank.rank_budget
