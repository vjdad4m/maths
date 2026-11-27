import PendantBound
namespace Graffiti384b.Adjacent12
open Finset SimpleGraph JointRank CliqueChoice
open private Repair.triangles_le_choose from Repair384b
open private EarCredit.credited from CreditRanks31
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private CliqueChoice.degree_neighbor from CliqueChoice384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def saturated (v : V) := trianglesAt G v=(G.degree v).choose 2
instance (v : V) : Decidable (saturated G v) := inferInstanceAs (Decidable (_=_))
def activated (X s : Finset V) := s.filter (fun v => saturated G v ∧ 2≤nbr G v (Xᶜ∪s))

/-- Remove all activated sampled simplicial vertices together. Their distinct
scores make them pairwise nonadjacent; every affected omitted neighbor sees
the same two surviving witnesses. -/
theorem trial (X O s : Finset V) (sep : Disjoint X O)
    (fixed : ∀ v∈O,2≤nbr G v (X∪O)ᶜ) (away : ∀ v∈X,∀ w∈O,¬G.Adj v w)
    (sub : s⊆X) (inj : Set.InjOn (trianglesAt G) (X:Set V)) :
    gamma G+(X\s).card+O.card+(activated G X s).card≤Fintype.card V+(FiniteRange.bad G X s).card := by
  classical
  let P := activated G X s
  let t := s\P
  have ps : P⊆s := filter_subset ..
  have ts : t⊆s := sdiff_subset
  have no {x y : V} (xp : x∈P) (yp : y∈P) : ¬G.Adj x y := by
    intro xy
    have sx := (mem_filter.mp xp).2.1
    have sy := (mem_filter.mp yp).2.1
    have d := Nat.le_antisymm (CliqueChoice.degree_neighbor G (saturated_clique G sx) xy)
      (CliqueChoice.degree_neighbor G (saturated_clique G sy) xy.symm)
    exact xy.ne (inj (sub (ps xp)) (sub (ps yp)) (sx.trans ((congrArg (fun j : ℕ => j.choose 2) d).trans sy.symm)))
  have keep {p y : V} (pp : p∈P) (py : G.Adj p y) (ym : y∈Xᶜ∪s) : y∈Xᶜ∪t := by
    rcases mem_union.mp ym with off|ys
    · exact mem_union_left _ off
    · exact mem_union_right _ (mem_sdiff.mpr ⟨ys,fun yp => no pp yp py⟩)
  have safe {p w : V} (pp : p∈P) (out : w∉Xᶜ∪t) (near : w=p ∨ G.Adj p w) : 2≤nbr G w (Xᶜ∪t) := by
    apply (mem_filter.mp pp).2.2.trans (card_le_card ?_)
    intro y ym
    obtain ⟨old,py⟩ := mem_filter.mp ym
    have kept := keep pp py old
    refine mem_filter.mpr ⟨kept,?_⟩
    rcases near with rfl|pw
    · exact py
    · exact saturated_clique G (mem_filter.mp pp).2.1 _ _ pw py (fun eq => out (eq ▸ kept))
  have bs : FiniteRange.bad G X t⊆FiniteRange.bad G X s := by
    intro w wm
    obtain ⟨xo,low⟩ := mem_filter.mp wm
    obtain ⟨wx,wt⟩ := mem_sdiff.mp xo
    have out : w∉Xᶜ∪t := fun h => (mem_union.mp h).elim (fun o => mem_compl.mp o wx) wt
    have wp : w∉P := fun m => (not_lt_of_ge (safe m out (Or.inl rfl))) low
    have edges {p} (pp : p∈P) : ¬G.Adj p w := fun pw => (not_lt_of_ge (safe pp out (Or.inr pw))) low
    have mono : nbr G w (Xᶜ∪s)≤nbr G w (Xᶜ∪t) := by
      apply card_le_card; intro y ym
      obtain ⟨old,wy⟩ := mem_filter.mp ym
      refine mem_filter.mpr ⟨?_,wy⟩
      exact (mem_union.mp old).elim (mem_union_left _)
        (fun ys => mem_union_right _ (mem_sdiff.mpr ⟨ys,fun yp => edges yp wy.symm⟩))
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨wx,fun ws => wt (mem_sdiff.mpr ⟨ws,wp⟩)⟩,mono.trans_lt low⟩
  have z := Pendant16.trial G X O t sep fixed away
  rw [card_sdiff (ts.trans sub)] at z
  have tt : t.card+P.card=s.card := card_sdiff_add_card_eq_card ps
  have sx := card_le_card sub
  have bcard := card_le_card bs
  rw [card_sdiff sub]; change gamma G+_+_+P.card≤_
  omega

private def bonus (d : ℕ) := (25:ℕ).choose 8-FiniteRange.badCount 26 8 d

/-- Insertion into an eight-vertex sample activates a designated center
unless it has fewer than two retained neighbors. The old deficiency
fiber already bounds the number of these exceptions. -/
private theorem active_fiber (X : Finset V) (xs : X.card=26) {v : V} (vx : v∈X) (sat : saturated G v)
    (k d : ℕ) (di : d≤G.degree v) (dr : d<26) :
    (25:ℕ).choose k-FiniteRange.badCount 26 k d≤((X.powersetCard (k+1)).filter (fun s => v∈activated G X s)).card := by
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

private def row (r : ℕ) := if r=0 then 1456730 else if r=1 then 1206557
  else if r<4 then 1107890 else if r<8 then 797810 else if r<13 then 545870
  else if r<19 then 354926 else 308620
private def refund (r d : ℕ) := if r+2=d.choose 2 then bonus d else 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem table :
    (∀ r : Fin 26,∀ d : Fin 11,3≤d.val → (r.val+2≤d.val.choose 2 ∨ d.val=10) →
      max (FiniteRange.badCount 26 9 d) ((26-d.val).choose 9+260000)≤row r+refund r d) ∧
    (∑ r∈range 26,row r)=15089553 := by
  unfold row refund bonus FiniteRange.badCount; simp only [Nat.choose_eq_fast_choose]; decide

/-- The refund uses the actual triangle count, so it is available precisely when
the minimum degree at this rank would force a clique neighborhood. -/
theorem ranked (X A : Finset V) (sz : X.card=26) (sep : Disjoint X A)
    (hx : X⊆high G) (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v) :
    (∑ v∈X,((X.powersetCard 9).filter (fun s => v∈FiniteRange.bad G X s)).card)+
      (X.filter (fun v => 0<nbr G v A)).card*260000 ≤ 15089553+
      ∑ v∈X,((X.powersetCard 9).filter (fun s => v∈activated G X s)).card := by
  classical
  let r := rank X (trianglesAt G)
  let hit := fun v => 0<nbr G v A
  let bill := fun v => ((X.powersetCard 9).filter (fun s => v∈FiniteRange.bad G X s)).card
  let act := fun v => ((X.powersetCard 9).filter (fun s => v∈activated G X s)).card
  have each (v : V) (vm : v∈X) : bill v+(if hit v then 260000 else 0)≤row (r v)+act v := by
    have rk := mem_image_of_mem (rank X (trianglesAt G)) vm
    rw [rank_range X _ inj,sz,mem_range] at rk
    change r v<26 at rk
    have lr := rank_lower X (trianglesAt G) inj 2 lo vm
    let d := min (G.degree v) 10
    have sm : d≤10 := min_le_right ..
    have dg : d≤G.degree v := min_le_left ..
    have dc : r v+2≤d.choose 2 ∨ d=10 := by
      by_cases h : G.degree v≤10
      · rw [show d=G.degree v from min_eq_left h,Nat.add_comm]; exact Or.inl (lr.trans (Repair.triangles_le_choose G v))
      · exact Or.inr (min_eq_right (by omega))
    have tab := table.1 ⟨r v,rk⟩ ⟨d,by omega⟩ (le_min (mem_filter.mp (hx vm)).2 (by decide)) dc
    dsimp only at tab
    have rc : refund (r v) d≤act v := by
      unfold refund; split_ifs with eq
      · have lt : d<10 := by
          by_contra! ge; have ten : d=10 := by omega
          rw [ten,show (10:ℕ).choose 2=45 by decide] at eq; omega
        have de : d=G.degree v := by dsimp [d] at *; omega
        have sat : saturated G v := by
          unfold saturated; apply Nat.le_antisymm (Repair.triangles_le_choose G v)
          rw [←de,←eq,Nat.add_comm]; exact lr
        exact active_fiber G X sz vm sat 8 d dg (by omega)
      · exact Nat.zero_le _
    apply le_trans _ (Nat.add_le_add_left rc _)
    apply le_trans _ tab
    by_cases hv : hit v
    · obtain ⟨w,wm⟩ := card_pos.mp hv
      obtain ⟨wa,vw⟩ := mem_filter.mp wm
      have b := EarCredit.credited G vm (fun wx => disjoint_left.mp sep wx wa) vw 9
      rw [sz] at b
      have mono := Nat.choose_le_choose 9 (show 26-G.degree v≤26-d by omega)
      rw [if_pos hv]; exact (Nat.add_le_add_right (b.trans mono) _).trans (le_max_right ..)
    · have b := FiniteRange.count_bad G X 9 d v vm dg (by omega)
      rw [sz] at b; rw [if_neg hv,Nat.add_zero]; exact b.trans (le_max_left ..)
  have sum := sum_le_sum (s:=X) each
  have fee : (∑ v∈X,if hit v then 260000 else 0)=(X.filter hit).card*260000 := by rw [←sum_filter]; simp
  simp only [sum_add_distrib,fee] at sum
  change _≤(∑ v∈X,row (rank X (trianglesAt G) v))+_ at sum
  rwa [sum_by_rank X _ inj row,sz,table.2] at sum

/-- Nine draws with two fixed omissions suffice with ten credited high vertices. -/
theorem pool (n : Fintype.card V=33) (X O A : Finset V) (sz : X.card=26)
    (os : O.card=2) (sep : Disjoint X O) (sa : Disjoint X A)
    (safe : ∀ v∈O,2≤nbr G v (X∪O)ᶜ) (away : ∀ v∈X,∀ w∈O,¬G.Adj v w)
    (hx : X⊆high G) (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v)
    (hits : 10≤(X.filter (fun v => 0<nbr G v A)).card) : gamma G≤17 := by
  classical
  let K := X.powersetCard 9
  let B := FiniteRange.bad G X
  let P := activated G X
  have cap := ranked G X A sz sa hx inj lo
  have swap (F : Finset V→Finset V) (inc : ∀ s∈K,F s⊆X) :
      (∑ s∈K,(F s).card)=∑ v∈X,(K.filter (fun s => v∈F s)).card := by
    calc _ = ∑ s∈K,∑ v∈X,if v∈F s then 1 else 0 := by
              apply sum_congr rfl
              intro s sm; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (inc s sm)]
         _ = _ := by rw [sum_comm]; simp [sum_boole]
  by_contra! bad
  have each (s : Finset V) (sm : s∈K) : 4+(P s).card≤(B s).card := by
    obtain ⟨sub,k⟩ := mem_powersetCard.mp sm
    have tr := trial G X O s sep safe away sub inj
    rw [card_sdiff sub,sz,k,os,n] at tr
    change 4+(activated G X s).card≤(FiniteRange.bad G X s).card; omega
  have mass := sum_le_sum each
  rw [sum_add_distrib,sum_const,smul_eq_mul,swap B (fun _ _ => (filter_subset ..).trans sdiff_subset),
    swap P (fun _ sm => (filter_subset ..).trans (mem_powersetCard.mp sm).1)] at mass
  have size : K.card=3124550 := by dsimp [K]; rw [card_powersetCard,sz,Nat.choose_eq_fast_choose]; decide
  rw [size] at mass
  change (∑ v∈X,(K.filter (fun s => v∈B s)).card)+_≤_+∑ v∈X,(K.filter (fun s => v∈P s)).card at cap
  omega

end Graffiti384b.Adjacent12
#print axioms Graffiti384b.Adjacent12.trial
#print axioms Graffiti384b.Adjacent12.ranked
#print axioms Graffiti384b.Adjacent12.pool
