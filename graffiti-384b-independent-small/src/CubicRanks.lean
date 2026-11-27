import CubicExtra
namespace Graffiti384b.Eleven
open Finset SimpleGraph JointRank Simplicial16
open private Reserved16.loss Reserved16.fiber Reserved16.refund from ReservedRanks
open private Simplicial16.active_fiber from SimplicialTrial
open private FiniteRange.bad from FiniteRange384b
open private Repair.nbr_add Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def regime (p q : ℕ) : Fin 3 := if p≤4 ∨ q≤4 then 0 else if p≤7 ∨ q≤7 then 1 else 2
private def mark (m : Fin 3) (r : ℕ) := if m=0 then (if r<2 then r+2 else r+3)
  else if m=1 then (if r<5 then r+2 else if r<13 then r+3 else r+4)
  else if r<8 then r+2 else r+4
private def cut (m : Fin 3) := if m=1 then 16 else 11
private def scoresOK (p q : ℕ) := (p≤4 ∨ q≤4) ∨ ((p≤7 ∨ q≤7) ∧ p≤16 ∧ q≤16) ∨ (p≤11 ∧ q≤11)
private theorem mark_lower (r s p q : ℕ) (ps : p≠s) (qs : q≠s) (pq : p≠q)
    (mode : scoresOK p q)
    (rb : 2+r≤s-(if p<s then 1 else 0)-(if q<s then 1 else 0)) :
    mark (regime p q) r≤s := by
  unfold scoresOK at mode
  unfold regime
  split_ifs <;> simp [mark] <;> split_ifs <;> split_ifs at rb <;> omega
private theorem up {p q : ℕ} (m : scoresOK p q) (non : regime p q≠0) : max p q≤cut (regime p q) := by
  unfold scoresOK at m
  unfold regime at *
  split_ifs at * <;> simp_all [cut]
  omega
private theorem mark_limit : ∀ m : Fin 3,∀ r : Fin 27,mark m r<45 := by decide
private def row (m : Fin 3) (r : ℕ) := if m=0 then #[3494689,2759218,2636326,1822366,1822366,1822366,1822366,1192516,1192516,1192516,1192516,1192516,739024,739024,739024,739024,739024,739024,432718,432718,432718,432718,432718,432718,432718,384098,384098][r]! else if m=1 then #[3494689,2759218,2636326,2636326,1822366,1822366,1822366,1192516,1192516,1192516,1192516,1192516,739024,739024,739024,739024,739024,432718,432718,432718,432718,432718,432718,384098,384098,384098,384098][r]! else #[3494689,2759218,2636326,2636326,1822366,1822366,1822366,1822366,1192516,1192516,1192516,739024,739024,739024,739024,739024,739024,432718,432718,432718,432718,432718,432718,384098,384098,384098,384098][r]!
private def refund (s d b : ℕ) := if s=d.choose 2 then (26:ℕ).choose 9-FiniteRange.badCount 27 9 d else
  if s=2 ∧ d=3 ∧ b=0 then 100947 else 0
set_option maxRecDepth 65536 in
set_option maxHeartbeats 16000000 in
private theorem table :
    (∀ m : Fin 3,∀ r : Fin 27,∀ d : Fin 11,∀ a : Fin 2,∀ b : Fin 3,
      (mark m r≤d.val.choose 2 ∨ d.val=10) → 3≤d.val →
      (d.val≠10 → cut m<mark m r → m≠0 → d.val+r.val+1≤27+2*(d.val.choose 2-mark m r)) →
      Reserved16.loss d (a.val+b.val)+340340*a.val+21879*b.val≤row m r+refund (mark m r) d b) ∧
    (∀ m : Fin 3,(∑ i∈range 27,row m i)≤30960415) := by
  unfold mark cut Reserved16.loss row refund FiniteRange.badCount; simp only [Nat.choose_eq_fast_choose]; decide
set_option maxHeartbeats 3000000 in
theorem cubic_rank (X A F E : Finset V) (sz : X.card=27) (sep : Disjoint (A∪F) X)
    (hx : X⊆high G) (af : Disjoint A F) (ca : ∀ v∈X,nbr G v A≤1) (cf : F.card=2)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v)
    (p q : ℕ) (p2 : 2≤p) (q2 : 2≤q) (pq : p≠q)
    (outside : ∀ v∈X,trianglesAt G v≠p ∧ trianglesAt G v≠q)
    (mode : scoresOK p q)
    (exterior : ∀ w,w∉X → trianglesAt G w≤max p q)
    (clean : ∀ v∈X,nbr G v F=0 → nbr G v E=0) :
    (∑ v∈X,((X.powersetCard 10).filter (fun s => v∈FiniteRange.bad G X s)).card)+
      340340*(∑ v∈X,nbr G v A)+21879*(∑ v∈X,nbr G v F)≤30960415+(∑ v∈X,((X.powersetCard 10).filter (fun s => v∈activated G X s)).card)+(∑ v∈X,((X.powersetCard 10).filter (fun s => v∈extra G X E s)).card) := by
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
  let single := regime p q
  let r := rank X f
  have each (v : V) (vm : v∈X) : bill v+340340*nbr G v A+21879*nbr G v F≤row single (r v)+(act v+ex v) := by
    have rk := mem_image_of_mem (rank X f) vm
    rw [rank_range X _ fi,sz,mem_range] at rk
    have idx := rank_lower X f fi 2 floor vm
    change 2+r v≤f v at idx
    obtain ⟨vp,vq⟩ := outside v vm
    have lr := mark_lower (r v) (trianglesAt G v) p q vp.symm vq.symm pq mode idx
    change mark single (r v)≤trianglesAt G v at lr
    let d := min (G.degree v) 10
    have dm : d≤10 := min_le_right .. 
    have dc : mark single (r v)≤d.choose 2 ∨ d=10 := by
      by_cases hd : G.degree v≤10
      · rw [show d=G.degree v from min_eq_left hd]; exact Or.inl (lr.trans (Repair.triangles_le_choose G v))
      · exact Or.inr (min_eq_right (by omega))
    have fit (db : d≠10) (large : cut single<mark single (r v)) (md : single≠0) :
        d+r v+1≤27+2*(d.choose 2-mark single (r v)) := by
      have dd : d=G.degree v := by dsimp [d] at *; omega
      have topLimit : max p q≤cut single := up mode md
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
    have z := table.1 single ⟨r v,rk⟩ ⟨d,by omega⟩ ⟨nbr G v A,by have := ca v vm; omega⟩
      ⟨nbr G v F,by unfold nbr; omega⟩ dc (le_min (mem_filter.mp (hx vm)).2 (by decide)) fit
    have rb : refund (mark single (r v)) d (nbr G v F)≤act v+ex v := by
      unfold refund
      split_ifs with eq bcase
      · have lt : d<10 := by
          by_cases ten : d=10
          · rw [ten,show (10:ℕ).choose 2=45 by decide] at eq
            exact False.elim ((Nat.ne_of_lt (mark_limit single ⟨r v,rk⟩)) eq)
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
  rw [sum_by_rank X f fi (fun j => row single j),sz] at sum
  have last := table.2 single
  have z := sum.trans (Nat.add_le_add_right last _)
  dsimp only [bill,act,ex] at z
  omega

end Graffiti384b.Eleven
#print axioms Graffiti384b.Eleven.cubic_rank
