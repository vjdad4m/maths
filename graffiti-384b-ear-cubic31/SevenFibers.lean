import Diversity31Frontier

namespace Graffiti384b.Seven
open Finset SimpleGraph
open private EarAnchor.mask EarAnchor.masked from AnchorCut33
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Number of 8-subsets charged for an exterior vertex with b neighbors
in a pool of size 23 and g guaranteed neighbors. -/
def bill (b g : ℕ) := if g=0 then FiniteRange.badCount 23 8 b else
  if g=1 then (22-b).choose 8 else 0

def weight (b j credit : ℕ) := j*bill b (credit+(j-1)) + (2-j)*bill b (credit+j)

def failures (W k : Finset V) (credit : V → ℕ) := (W\k).filter (fun w => nbr H w k+credit w<2)

private theorem with_credit {W : Finset V} (size : W.card=23) {w : V} (wm : w∈W) (g : V → ℕ) :
    ((W.powersetCard 8).filter (fun k => w∈failures H W k g)).card≤bill (nbr H w W) (g w) := by
  classical
  let L := W.filter (H.Adj w)
  have sub : L⊆W.erase w := by intro v vm; exact mem_erase.mpr ⟨(mem_filter.mp vm).2.ne.symm,(mem_filter.mp vm).1⟩
  have nL : L.card=nbr H w W := rfl
  have ss : (W.erase w\L).card=22-nbr H w W := by rw [card_sdiff sub,card_erase_of_mem wm,size,nL]
  by_cases zero : g w=0
  · let J := EarAnchor.mask H W
    have d : J.degree w=nbr H w W := by
      rw [←card_neighborFinset_eq_degree]
      have eq : J.neighborFinset w=L := by ext v; simp [J,L,EarAnchor.mask,wm]
      exact (congrArg card eq).trans nL
    have bound := FiniteRange.count_bad J W 8 (nbr H w W) w wm d.ge (by
      have h := card_le_card sub; rw [card_erase_of_mem wm,size,nL] at h; omega)
    rw [size] at bound
    rw [bill,if_pos zero]
    apply (card_le_card ?_).trans bound
    intro k km
    obtain ⟨sample,low⟩ := mem_filter.mp km
    obtain ⟨wk,small⟩ := mem_filter.mp low
    refine mem_filter.mpr ⟨sample,mem_filter.mpr ⟨wk,?_⟩⟩
    have inter : W∩(Wᶜ∪k)=k := by
      have subK := (mem_powersetCard.mp sample).1
      ext v; simp only [mem_inter,mem_union,mem_compl]; constructor
      · rintro ⟨a,h⟩; exact h.resolve_left (not_not.mpr a)
      · intro h; exact ⟨subK h,Or.inr h⟩
    change nbr (EarAnchor.mask H W) w (Wᶜ∪k)<2
    rw [EarAnchor.masked H wm,inter]
    omega
  · by_cases one : g w=1
    · have inc : (W.powersetCard 8).filter (fun k => w∈failures H W k g)⊆(W.erase w\L).powersetCard 8 := by
        intro k km
        obtain ⟨sample,low⟩ := mem_filter.mp km
        obtain ⟨kw,sz⟩ := mem_powersetCard.mp sample
        obtain ⟨wk,small⟩ := mem_filter.mp low
        refine mem_powersetCard.mpr ⟨?_,sz⟩
        intro v vm
        apply mem_sdiff.mpr ⟨mem_erase.mpr ⟨fun (eq : v=w) => (mem_sdiff.mp wk).2 (eq ▸ vm),kw vm⟩,?_⟩
        intro vl
        have po : 0<nbr H w k := card_pos.mpr ⟨v,mem_filter.mpr ⟨vm,(mem_filter.mp vl).2⟩⟩
        omega
      have h := card_le_card inc
      rw [card_powersetCard,ss] at h
      simpa [bill,one] using h
    · have empty : (W.powersetCard 8).filter (fun k => w∈failures H W k g)=∅ := eq_empty_of_forall_not_mem (by
        intro k km; have h := (mem_filter.mp (mem_filter.mp km).2).2; omega)
      rw [empty,card_empty]; exact Nat.zero_le _

/-- Sum over the two possible omitted tips. -/
theorem two_fibers {A W : Finset V} (sz : A.card=2) (size : W.card=23) {w : V} (wm : w∈W) (credit : V → ℕ) :
    (∑ x∈A,((W.powersetCard 8).filter (fun k => w∈failures H W k
      (fun y => credit y+nbr H y (A.erase x)))).card)≤weight (nbr H w W) (nbr H w A) (credit w) := by
  classical
  let B := A.filter (H.Adj w)
  have sub : B⊆A := filter_subset ..
  have sb : B.card=nbr H w A := rfl
  have er (x : V) : (A.erase x).filter (H.Adj w)=B.erase x := by ext y; simp [B,and_assoc,and_left_comm]
  let f := fun x => bill (nbr H w W) (credit w+nbr H w (A.erase x))
  have upper := sum_le_sum (s:=A) (fun x _ => with_credit H size wm (fun y => credit y+nbr H y (A.erase x)))
  apply upper.trans
  change (∑ x∈A,f x)≤_
  have eq := sum_sdiff sub (f:=f)
  have valA : (∑ x∈A\B,f x)=(A\B).card*bill (nbr H w W) (credit w+nbr H w A) := by
    calc _ = ∑ _x∈A\B,bill (nbr H w W) (credit w+nbr H w A) := by
            apply sum_congr rfl; intro x xm
            change bill _ (_+((A.erase x).filter _).card)=_
            rw [er,erase_eq_of_not_mem (mem_sdiff.mp xm).2,sb]
         _ = _ := by simp
  have valB : (∑ x∈B,f x)=B.card*bill (nbr H w W) (credit w+(nbr H w A-1)) := by
    calc _ = ∑ _x∈B,bill (nbr H w W) (credit w+(nbr H w A-1)) := by
            apply sum_congr rfl; intro x xm
            change bill _ (_+((A.erase x).filter _).card)=_
            rw [er,card_erase_of_mem xm,sb]
         _ = _ := by simp
  rw [←eq,valA,valB,card_sdiff sub,sz,sb]
  exact le_of_eq (Nat.add_comm ..)

end Graffiti384b.Seven
#print axioms Graffiti384b.Seven.two_fibers

