import CubicRanks
namespace Graffiti384b.Clean
open Graffiti384b.Eleven
open private Eleven.refund from CubicRanks
open Finset SimpleGraph JointRank Simplicial16
open private Reserved16.loss Reserved16.fiber Reserved16.refund from ReservedRanks
open private Simplicial16.active_fiber from SimplicialTrial
open private FiniteRange.bad from FiniteRange384b
open private Repair.nbr_add Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def leftSize (m : Fin 15) : ℕ := #[2,2,2,2,2,2,3,3,3,3,3,4,4,4,5][m.val]!
def rightSize (m : Fin 15) : ℕ := #[3,4,5,6,7,8,3,4,5,6,7,4,5,6,5][m.val]!
private def lower (m : Fin 15) := 1+(leftSize m).choose 2
private def upper (m : Fin 15) := 1+(rightSize m).choose 2
private def mark (m : Fin 15) (r : ℕ) := if upper m≤r+3 then r+4 else
  if min (lower m) (upper m-1)≤r+2 then r+3 else r+2
theorem coverage : ∀ x : Fin 6,∀ y : Fin 9,2≤x.val → x.val≤y.val → 5≤x.val+y.val →
    x.val+y.val≤10 → ∃ m : Fin 15,leftSize m=x.val ∧ rightSize m=y.val := by decide
private theorem mark_lower (m : Fin 15) (r s p q : ℕ) (ps : p≠s) (qs : q≠s) (pq : p≠q)
    (small : p≤lower m ∨ q≤lower m) (big : max p q≤upper m)
    (rb : 2+r≤s-(if p<s then 1 else 0)-(if q<s then 1 else 0)) : mark m r≤s := by
  have bp := (Nat.max_le.mp big).1
  have bq := (Nat.max_le.mp big).2
  unfold mark
  split_ifs <;> split_ifs at rb <;> omega
private theorem mark_limit : ∀ m : Fin 15,∀ r : Fin 27,mark m r<45 := by decide
private def discounted (m : Fin 15) (r : ℕ) : Bool :=
  decide (mark m r=27 ∧ upper m<27 ∧ 20<r)
private def charge (s : ℕ) (discount : Bool) :=
  if s=2 then 3494689 else if s=3 then 2759218 else if s<6 then 2636326 else if s<10 then 1822366
  else if s<15 then 1192516 else if s<21 then 739024 else if s<28 ∧ !discount then 432718 else 384098
private def row (m : Fin 15) (r : ℕ) := charge (mark m r) (discounted m r)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem costs :
    ∀ s : Fin 31,∀ discount : Bool,∀ d : Fin 11,∀ a : Fin 2,∀ b : Fin 3,
      2≤s.val → 3≤d.val → (s.val≤d.val.choose 2 ∨ d.val=10) →
      (discount=true → s.val=27 ∧ d.val≠8) →
      Reserved16.loss d (a.val+b.val)+340340*a.val+21879*b.val≤charge s discount+Eleven.refund s d b := by
  unfold charge Reserved16.loss Eleven.refund FiniteRange.badCount; simp only [Nat.choose_eq_fast_choose]; decide

private theorem scores_range : ∀ m : Fin 15,∀ r : Fin 27,2≤mark m r ∧ mark m r<31 := by decide

set_option maxRecDepth 65536 in
private theorem totals : ∀ m : Fin 15,(∑ i∈range 27,row m i)+2506≤27472005+340340*(leftSize m+rightSize m)+87516 := by
  decide
set_option maxHeartbeats 3000000 in
theorem ranked (X A F E : Finset V) (sz : X.card=27) (sep : Disjoint (A∪F) X)
    (hx : X⊆high G) (af : Disjoint A F) (ca : ∀ v∈X,nbr G v A≤1) (cf : F.card=2)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v)
    (p q : ℕ) (p2 : 2≤p) (q2 : 2≤q) (pq : p≠q)
    (outside : ∀ v∈X,trianglesAt G v≠p ∧ trianglesAt G v≠q)
    (m : Fin 15) (small : p≤1+(leftSize m).choose 2 ∨ q≤1+(leftSize m).choose 2)
    (big : max p q≤1+(rightSize m).choose 2)
    (exterior : ∀ w,w∉X → trianglesAt G w≤max p q)
    (clean : ∀ v∈X,nbr G v F=0 → nbr G v E=0) :
    (∑ v∈X,((X.powersetCard 10).filter (fun s => v∈FiniteRange.bad G X s)).card)+
      340340*(∑ v∈X,nbr G v A)+21879*(∑ v∈X,nbr G v F) +2506≤(27472005+340340*(leftSize m+rightSize m)+87516)+(∑ v∈X,((X.powersetCard 10).filter (fun s => v∈activated G X s)).card)+(∑ v∈X,((X.powersetCard 10).filter (fun s => v∈extra G X E s)).card) := by
  classical
  let bill := fun v => ((X.powersetCard 10).filter (fun s => v∈FiniteRange.bad G X s)).card
  let act := fun v => ((X.powersetCard 10).filter (fun s => v∈activated G X s)).card
  let ex := fun v => ((X.powersetCard 10).filter (fun s => v∈extra G X E s)).card
  let f := fun v => trianglesAt G v-(if p<trianglesAt G v then 1 else 0)-(if q<trianglesAt G v then 1 else 0)
  have fi : Set.InjOn f (X:Set V) := by
    intro u um v vm eq
    obtain ⟨up,uq⟩ := outside u um
    obtain ⟨vp,vq⟩ := outside v vm
    apply inj um vm
    dsimp [f] at eq; split_ifs at eq <;> omega
  have floor (v : V) (vm : v∈X) : 2≤f v := by
    have hv := lo v vm
    obtain ⟨vp,vq⟩ := outside v vm
    dsimp [f]; split_ifs <;> omega
  let r := rank X f
  have each (v : V) (vm : v∈X) : bill v+340340*nbr G v A+21879*nbr G v F≤row m (r v)+(act v+ex v) := by
    have rk := mem_image_of_mem (rank X f) vm
    rw [rank_range X _ fi,sz,mem_range] at rk
    have idx := rank_lower X f fi 2 floor vm
    change 2+r v≤f v at idx
    obtain ⟨vp,vq⟩ := outside v vm
    have lr := mark_lower m (r v) (trianglesAt G v) p q vp.symm vq.symm pq small big idx
    change mark m (r v)≤trianglesAt G v at lr
    let d := min (G.degree v) 10
    have dm : d≤10 := min_le_right .. 
    have dc : mark m (r v)≤d.choose 2 ∨ d=10 := by
      by_cases hd : G.degree v≤10
      · rw [show d=G.degree v from min_eq_left hd]; exact Or.inl (lr.trans (Repair.triangles_le_choose G v))
      · exact Or.inr (min_eq_right (by omega))
    have fit (db : d≠10) (large : upper m<mark m (r v)) :
        d+r v+1≤27+2*(d.choose 2-mark m (r v)) := by
      have dd : d=G.degree v := by dsimp [d] at *; omega
      have topLimit : max p q≤upper m := big
      let L := X.filter (fun w => f w<f v)
      let U := (G.neighborFinset v).filter (fun w => trianglesAt G v≤trianglesAt G w)
      have xv : insert v L⊆X := insert_subset vm (filter_subset ..)
      have vs : v∉L := fun m => (lt_irrefl _) (mem_filter.mp m).2
      have boundU : U⊆X\(insert v L) := by
        intro w wm
        obtain ⟨wn,sw⟩ := mem_filter.mp wm
        have wx : w∈X := by
          by_cases hw : w∈X
          · exact hw
          · have top := (exterior w hw).trans topLimit
            omega
        refine mem_sdiff.mpr ⟨wx,?_⟩
        intro wl
        rcases mem_insert.mp wl with rfl|lt
        · exact G.not_mem_neighborFinset_self _ wn
        · have fw := (mem_filter.mp lt).2
          change f w<f v at fw
          obtain ⟨wp,wq⟩ := outside w wx
          dsimp [f] at fw; split_ifs at fw <;> omega
      have uc := card_le_card boundU
      rw [card_sdiff xv,card_insert_of_not_mem vs,sz] at uc
      have lc : L.card=r v := rfl
      have rc := JointDense.dense_neighbor_bound G v
      change G.degree v≤U.card+_ at rc
      rw [←dd] at rc
      have rank_lt : r v<27 := rk
      have mono := Nat.sub_le_sub_left lr (d.choose 2)
      rw [lc] at uc
      omega
    have b := Reserved16.fiber G sz sep vm
    rw [Repair.nbr_add G v af] at b
    have cf' := card_le_card (filter_subset (G.Adj v) F)
    have range' := scores_range m ⟨r v,rk⟩
    have disc (yes : discounted m (r v)=true) : mark m (r v)=27 ∧ d≠8 := by
      obtain ⟨val,cap,late⟩ := of_decide_eq_true (show decide (mark m (r v)=27 ∧ upper m<27 ∧ 20<r v)=true from yes)
      refine ⟨val,?_⟩
      intro de
      have imposs := fit (by omega) (by omega)
      rw [de,val,show (8:ℕ).choose 2=28 by decide] at imposs
      omega
    have z := costs ⟨mark m (r v),range'.2⟩ (discounted m (r v)) ⟨d,by omega⟩ ⟨nbr G v A,by have := ca v vm; omega⟩
      ⟨nbr G v F,by unfold nbr; omega⟩ range'.1 (le_min (mem_filter.mp (hx vm)).2 (by decide)) dc disc
    have rb : Eleven.refund (mark m (r v)) d (nbr G v F)≤act v+ex v := by
      unfold Eleven.refund
      split_ifs with eq bcase
      · have lt : d<10 := by
          by_cases ten : d=10
          · rw [ten,show (10:ℕ).choose 2=45 by decide] at eq
            exact False.elim ((Nat.ne_of_lt (mark_limit m ⟨r v,rk⟩)) eq)
          · omega
        have de : d=G.degree v := by dsimp [d] at *; omega
        have sat : saturated G v := by
          unfold saturated
          apply Nat.le_antisymm (Repair.triangles_le_choose G v)
          rw [←de,←eq]; exact lr
        exact (Simplicial16.active_fiber G X sz vm sat 9 d (min_le_left ..) (by omega)).trans (Nat.le_add_right ..)
      · obtain ⟨mv,dv,free⟩ := bcase
        have dg : G.degree v=3 := by change min (G.degree v) 10=3 at dv; omega
        have lo' := lo v vm
        have hi' := Repair.triangles_le_choose G v
        rw [dg,show (3:ℕ).choose 2=3 by decide] at hi'
        by_cases sc : trianglesAt G v=2
        · exact (extra_fiber G X E sz vm sc dg (clean v vm free)).trans (Nat.le_add_left ..)
        · have sat : saturated G v := by dsimp [saturated]; rw [dg,show (3:ℕ).choose 2=3 by decide]; omega
          have old := Simplicial16.active_fiber G X sz vm sat 9 3 dg.ge (by decide)
          have num : 100947≤(26:ℕ).choose 9-FiniteRange.badCount 27 9 3 := by
            unfold FiniteRange.badCount; simp only [Nat.choose_eq_fast_choose]; decide
          exact (num.trans old).trans (Nat.le_add_right ..)
      · exact Nat.zero_le _
    exact ((Nat.add_le_add_right (Nat.add_le_add_right b _) _).trans z).trans (Nat.add_le_add_left rb _)
  have sum := sum_le_sum each
  simp only [sum_add_distrib,←mul_sum] at sum
  rw [sum_by_rank X f fi (fun j => row m j),sz] at sum
  have last := totals m
  dsimp only [bill,act,ex] at sum
  omega

end Graffiti384b.Clean
#print axioms Graffiti384b.Clean.coverage
#print axioms Graffiti384b.Clean.ranked
