import IndependentThirteen
namespace Graffiti384b.Twelve
open Finset SimpleGraph JointRank Simplicial16
open private Reserved16.loss Reserved16.fiber Reserved16.refund from ReservedRanks
open private Simplicial16.active_fiber from SimplicialTrial
open private FiniteRange.bad from FiniteRange384b
open private Repair.nbr_add Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
private def mark (single : Bool) (r : ℕ) := if single then (if r<5 then r+2 else r+3)
  else if r<9 then r+2 else if r<13 then r+3 else r+4
private theorem mark_lower (r s p q : ℕ) (ps : p≠s) (qs : q≠s) (pq : p≠q)
    (mode : p≤7 ∨ q≤7 ∨ ((p≤11 ∨ q≤11) ∧ p≤16 ∧ q≤16))
    (rb : 2+r≤s-(if p<s then 1 else 0)-(if q<s then 1 else 0)) :
    mark (decide (p≤7 ∨ q≤7)) r≤s := by
  by_cases m : p≤7 ∨ q≤7
  · simp only [m,decide_true,mark,ite_true]
    split_ifs <;> split_ifs at rb <;> omega
  · simp only [m,decide_false,mark,Bool.false_eq_true,ite_false]
    split_ifs <;> split_ifs at rb <;> omega
private theorem mark_limit : ∀ m : Bool,∀ r : Fin 27,mark m r<45 := by decide
private def row (m : Bool) (r : ℕ) := if m then #[3595636,2759218,2636326,2636326,1822366,1822366,1822366,1192516,1192516,1192516,1192516,1192516,739024,739024,739024,739024,739024,739024,646646,646646,646646,646646,646646,646646,646646,598026,598026][r]! else #[3595636,2759218,2636326,2636326,1822366,1822366,1822366,1822366,1192516,1192516,1192516,1192516,739024,739024,739024,739024,739024,646646,646646,646646,646646,646646,646646,598026,598026,598026,598026][r]!
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
private theorem table :
    (∀ m : Bool,∀ r : Fin 27,∀ d : Fin 11,∀ a : Fin 2,∀ b : Fin 3,
      (mark m r≤d.val.choose 2 ∨ d.val=10) → 3≤d.val →
      (d.val≠10 → 16<mark m r → m=false → d.val+r.val+1≤27+2*(d.val.choose 2-mark m r)) →
      Reserved16.loss d (a.val+b.val)+554268*a.val+21879*b.val≤row m r+Reserved16.refund (mark m r) d) ∧
    (∀ m : Bool,(∑ i∈range 27,row m i)≤33654134) := by
  unfold mark Reserved16.loss row Reserved16.refund FiniteRange.badCount; simp only [Nat.choose_eq_fast_choose]; decide
set_option maxHeartbeats 3000000 in
theorem sharp_rank (X A F : Finset V) (sz : X.card=27) (sep : Disjoint (A∪F) X)
    (hx : X⊆high G) (af : Disjoint A F) (ca : ∀ v∈X,nbr G v A≤1) (cf : F.card=2)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v)
    (p q : ℕ) (p2 : 2≤p) (q2 : 2≤q) (pq : p≠q)
    (outside : ∀ v∈X,trianglesAt G v≠p ∧ trianglesAt G v≠q)
    (mode : p≤7 ∨ q≤7 ∨ ((p≤11 ∨ q≤11) ∧ p≤16 ∧ q≤16))
    (exterior : p≤16 → q≤16 → ∀ w,w∉X → trianglesAt G w≤16) :
    (∑ v∈X,((X.powersetCard 10).filter (fun s => v∈FiniteRange.bad G X s)).card)+
      554268*(∑ v∈X,nbr G v A)+21879*(∑ v∈X,nbr G v F)≤33654134+(∑ v∈X,((X.powersetCard 10).filter (fun s => v∈activated G X s)).card) := by
  classical
  let bill := fun v => ((X.powersetCard 10).filter (fun s => v∈FiniteRange.bad G X s)).card
  let act := fun v => ((X.powersetCard 10).filter (fun s => v∈activated G X s)).card
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
  let single := decide (p≤7 ∨ q≤7)
  let r := rank X f
  have each (v : V) (vm : v∈X) : bill v+554268*nbr G v A+21879*nbr G v F≤row single (r v)+act v := by
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
    have fit (db : d≠10) (large : 16<mark single (r v)) (md : single=false) :
        d+r v+1≤27+2*(d.choose 2-mark single (r v)) := by
      have dd : d=G.degree v := by dsimp [d] at *; omega
      have ns : ¬(p≤7 ∨ q≤7) := by
        intro hp; have yes : single=true := decide_eq_true hp; exact Bool.noConfusion (md.symm.trans yes)
      obtain ⟨_,p16,q16⟩ := (mode.resolve_left (fun hp => ns (Or.inl hp))).resolve_left (fun hq => ns (Or.inr hq))
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
          · have top := exterior p16 q16 w hw
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
    have rb : Reserved16.refund (mark single (r v)) d≤act v := by
      unfold Reserved16.refund; split_ifs with eq
      · have lt : d<10 := by
          by_contra! ge
          have ten : d=10 := by omega
          rw [ten,show (10:ℕ).choose 2=45 by decide] at eq
          exact (Nat.ne_of_lt (mark_limit single ⟨r v,rk⟩)) eq
        have de : d=G.degree v := by dsimp [d] at *; omega
        have sat : saturated G v := by
          unfold saturated
          apply Nat.le_antisymm (Repair.triangles_le_choose G v)
          rw [←de,←eq]; exact lr
        exact Simplicial16.active_fiber G X sz vm sat 9 d (min_le_left ..) (by omega)
      · exact Nat.zero_le _
    exact ((Nat.add_le_add_right (Nat.add_le_add_right b _) _).trans z).trans (Nat.add_le_add_left rb _)
  have sum := sum_le_sum each
  simp only [sum_add_distrib,←mul_sum] at sum
  rw [sum_by_rank X f fi (fun j => row single j),sz] at sum
  have last := table.2 single
  exact sum.trans (Nat.add_le_add_right last _)

end Graffiti384b.Twelve
#print axioms Graffiti384b.Twelve.sharp_rank
