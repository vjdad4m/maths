import ThreeFibers33

namespace Graffiti384b.ThreeChoice
open Finset SimpleGraph JointRank

def price : ℕ := 370000
def floorMass : ℕ := 3665432

def mark (i : ℕ) := if i<2 then i+1 else i+2

def budget (s : ℕ) := if s≤1 then 22064130 else if s≤3 then 17651304 else if s≤5 then 13238478
  else if s=6 then 10176280 else if s≤8 then 9401238 else if s=9 then 7070958 else if s≤12 then 6348888
  else if s=13 then 4797038 else if s≤16 then 4081428 else if s≤18 then 3191728 else if s≤21 then 2494206
  else if s≤23 then 2099988 else if s≤28 then 1445432 else if s=29 then 1386158 else 1110000

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
theorem arithmetic : (∀ i : Fin 31,∀ b : Fin 28,∀ j : Fin 4,
    mark i≤(b.val+j.val).choose 2 →
    (j.val≤1 → b.val≤10 → mark i≤RankTable.cap b.val 3+b.val*j.val) →
    weight b j 0+price*j.val≤budget (mark i)) ∧
    (∀ i : Fin 31,∀ b : Fin 29,(b.val≤10 → mark i≤3+2*b.val+RankTable.cap b.val 4) →
      floorMass≤budget (mark i)+price*b.val) ∧
    (∑ i∈range 31,budget (mark i))=168339458 ∧ 168339458<3*floorMass+12*(28:ℕ).choose 10 := by
  unfold weight bill FiniteRange.badCount RankTable.cap mark budget floorMass price
  simp only [Nat.choose_eq_fast_choose]
  decide

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

omit [Fintype V] [DecidableEq V] in
private theorem balance (A W : Finset V) : (∑ w∈W,nbr H w A)=∑ a∈A,nbr H a W := by
  calc _ = ∑ w∈W,∑ a∈A,if H.Adj w a then 1 else 0 := by simp [sum_boole,nbr]
       _ = ∑ a∈A,∑ w∈W,if H.Adj a w then 1 else 0 := by rw [sum_comm]; simp_rw [H.adj_comm]
       _ = _ := by simp [sum_boole,nbr]

/-- The incidence correction cancels between the three anchors and the
28 tested vertices. All 31 scores share a single rank ordering. -/
theorem mass {A W : Finset V} (dis : Disjoint A W) (asize : A.card=3) (ws : W.card=28)
    (pos : ∀ w,0<trianglesAt H w) (inj : Function.Injective (trianglesAt H))
    (skip : ∀ w∈A∪W,trianglesAt H w≠3)
    (cap : ∀ w∈W,trianglesAt H w≤(nbr H w W+nbr H w A).choose 2)
    (localCap : ∀ w∈W,nbr H w A≤1 → nbr H w W≤10 →
      trianglesAt H w≤RankTable.cap (nbr H w W) 3+nbr H w W*nbr H w A)
    (anchorCap : ∀ a∈A,nbr H a W≤10 → trianglesAt H a≤3+2*nbr H a W+RankTable.cap (nbr H a W) 4) :
    (∑ w∈W,weight (nbr H w W) (nbr H w A) 0)<12*(28:ℕ).choose 10 := by
  classical
  let S := A∪W
  let g (w : V) := if trianglesAt H w<3 then trianglesAt H w else trianglesAt H w-1
  have fi : Set.InjOn g (S:Set V) := by
    intro u um v vm eq
    have := skip u um; have := skip v vm
    unfold g at eq; apply inj; split_ifs at eq <;> omega
  have po (w : V) (_ : w∈S) : 1≤g w := by have := pos w; unfold g; split_ifs <;> omega
  have sz : S.card=31 := by rw [show S=A∪W from rfl,card_union_of_disjoint dis,asize,ws]
  let r := rank S g
  have valid {w : V} (wm : w∈S) : r w<31 := by
    have m := mem_image_of_mem (rank S g) wm
    rw [rank_range S g fi,sz,mem_range] at m; exact m
  have minscore {w : V} (wm : w∈S) : mark (r w)≤trianglesAt H w := by
    have l := rank_lower S g fi 1 po wm
    change 1+r w≤(if trianglesAt H w<3 then trianglesAt H w else trianglesAt H w-1) at l
    have := skip w wm; unfold mark; split_ifs at * <;> omega
  let f (w : V) := budget (mark (r w))
  have wb (w : V) (wm : w∈W) : weight (nbr H w W) (nbr H w A) 0+price*nbr H w A≤f w := by
    have inc := mem_union_right A wm
    have sub : W.filter (H.Adj w)⊆W.erase w := fun x m => mem_erase.mpr ⟨(mem_filter.mp m).2.ne.symm,(mem_filter.mp m).1⟩
    have bnd := card_le_card sub
    rw [card_erase_of_mem wm,ws] at bnd
    have b : nbr H w W<28 := by change (W.filter _).card<28; omega
    have j : nbr H w A<4 := by have h := card_filter_le A (H.Adj w); change nbr H w A≤A.card at h; omega
    exact arithmetic.1 ⟨r w,valid inc⟩ ⟨_,b⟩ ⟨_,j⟩ ((minscore inc).trans (cap w wm))
      (fun j' b' => (minscore inc).trans (localCap w wm j' b'))
  have ab (w : V) (wm : w∈A) : floorMass≤f w+price*nbr H w W := by
    have inc := mem_union_left W wm
    have b : nbr H w W<29 := by have h := card_filter_le W (H.Adj w); change nbr H w W≤W.card at h; omega
    exact arithmetic.2.1 ⟨r w,valid inc⟩ ⟨_,b⟩ (fun h => (minscore inc).trans (anchorCap w wm h))
  have wsum := sum_le_sum wb
  have asum := sum_le_sum ab
  rw [sum_add_distrib,←mul_sum] at wsum
  rw [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,asize] at asum
  have eq := balance H A W
  rw [eq] at wsum
  have all : (∑ w∈A,f w)+(∑ w∈W,f w)=168339458 := by
    rw [←sum_union dis]
    change (∑ w∈S,(fun i => budget (mark i)) (rank S g w))=_
    rw [sum_by_rank S g fi (fun i => budget (mark i)),sz]; exact arithmetic.2.2.1
  have strict := arithmetic.2.2.2
  omega

end Graffiti384b.ThreeChoice
#print axioms Graffiti384b.ThreeChoice.arithmetic
#print axioms Graffiti384b.ThreeChoice.mass
