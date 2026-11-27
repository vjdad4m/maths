import ParentFiber180
import RootReserve180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem child_bound (T : SimpleGraph V) (tree : T.IsTree) (r : V) (q : V→V) (rank : V→ℕ)
    (down : ∀ x≠r,rank (q x)<rank x) (take : ∀ x≠r,T.Adj x (q x)) (C : Finset V) :
    ((univ.erase r).filter (fun x => q x∈C)).card+(if r∈C ∧ r∈leaves T then 1 else 0)≤
      C.card+(∑ x∈C,(T.degree x-2))+(if r∈C then 1 else 0) := by
  classical
  let kids x := ((univ.erase r).filter (fun y => q y=x)).card
  have sum : (∑ x∈C,kids x)=((univ.erase r).filter (fun x => q x∈C)).card := sum_card_fiberwise_eq_card_filter ..
  have point (x : V) (xr : x≠r) : kids x≤1+(T.degree x-2) := by
    have h := parent_neighbors T tree r q rank down take x xr
    change T.degree x=kids x+1 at h;omega
  have other : ∑ x∈C.erase r,kids x≤(C.erase r).card+∑ x∈C.erase r,(T.degree x-2) := by
    simpa only [sum_add_distrib,sum_const,smul_eq_mul,mul_one] using
      sum_le_sum (s:=C.erase r) (fun x xm => point x (mem_erase.mp xm).1)
  rw [←sum]
  by_cases rc : r∈C
  · have split := add_sum_erase C kids rc
    have bd := add_sum_erase C (fun x => T.degree x-2) rc
    have count := card_erase_add_one rc
    have inc : (univ.erase r).filter (fun y => q y=r)⊆T.neighborFinset r := by
      intro y ym
      obtain ⟨yn,eq⟩ := mem_filter.mp ym
      exact (T.mem_neighborFinset _ _).mpr (eq ▸ (take y (mem_erase.mp yn).1).symm)
    have cap : kids r≤T.degree r := by simpa only [card_neighborFinset_eq_degree] using card_le_card inc
    change T.degree r-2+(∑ x∈C.erase r,(T.degree x-2))=∑ x∈C,(T.degree x-2) at bd
    by_cases lf : r∈leaves T
    · have one : T.degree r=1 := (mem_filter.mp lf).2
      simp only [rc,lf,and_self,if_true];omega
    · simp only [rc,lf,and_false,if_false,if_true,add_zero];omega
  · simpa [rc,erase_eq_of_not_mem rc] using other

/-- Count a single distance level in a marked forest. Internal marked
parent edges point one original level downward. The designated extra exit
accounts for the actual root when its marked component reaches the prefix. -/
theorem forest_width (T : SimpleGraph V) (tree : T.IsTree) (r : V) (q : V→V) (rank d : V→ℕ)
    (down : ∀ x≠r,rank (q x)<rank x) (take : ∀ x≠r,T.Adj x (q x))
    (D : Finset V) (k : ℕ) (pos : d r<k) (mon : ∀ x∈D,x≠r → d x=d (q x)+1)
    (exit : r∈D.filter (fun x => d x<k) →
      ∃ z,z≠r ∧ z∉D ∧ q z∈D.filter (fun x => d x<k)) :
    let C := D.filter (fun x => d x<k)
    let Y := D.filter (fun x => d x=k)
    (T.edgeFinset∩D.sym2).card+Y.card+(if r∈D ∧ r∈leaves T then 1 else 0)≤
      D.card+(∑ v∈C,(T.degree v-2)) := by
  classical
  intro C Y
  let B := C∪Y
  let K := (univ.erase r).filter (fun x => q x∈C)
  let S := (D.erase r).filter (fun x => q x∈D)
  have parent := parent_image T tree r q rank down take
  have inn : T.edgeFinset∩D.sym2⊆S.image (fun x => s(x,q x)) := by
    intro e em
    obtain ⟨et,dd⟩ := mem_inter.mp em
    rw [←parent] at et
    obtain ⟨x,xr,rfl⟩ := mem_image.mp et
    obtain ⟨xd,pd⟩ := mk_mem_sym2_iff.mp dd
    exact mem_image.mpr ⟨x,mem_filter.mpr ⟨mem_erase.mpr ⟨(mem_erase.mp xr).1,xd⟩,pd⟩,rfl⟩
  have edges := (card_le_card inn).trans card_image_le
  have outside : S\B⊆D\B := fun x xm => mem_sdiff.mpr ⟨(mem_erase.mp (mem_filter.mp (mem_sdiff.mp xm).1).1).2,(mem_sdiff.mp xm).2⟩
  have inside : S∩B⊆K := by
    intro x xm
    obtain ⟨xs,xb⟩ := mem_inter.mp xm
    obtain ⟨xr,pd⟩ := mem_filter.mp xs
    obtain ⟨nr,xd⟩ := mem_erase.mp xr
    have h := mon x xd nr
    have dk : d x≤k := (mem_union.mp xb).elim (fun m => (mem_filter.mp m).2.le) (fun m => (mem_filter.mp m).2.le)
    exact mem_filter.mpr ⟨mem_erase.mpr ⟨nr,mem_univ _⟩,mem_filter.mpr ⟨pd,by omega⟩⟩
  have rc : r∈C ↔ r∈D := by simp [C,pos]
  have hit : (S∩B).card+(if r∈C then 1 else 0)≤K.card := by
    split_ifs with cr
    · obtain ⟨z,zr,zd,zp⟩ := exit cr
      have miss : z∉S∩B := fun m => zd (mem_erase.mp (mem_filter.mp (mem_inter.mp m).1).1).2
      have sub := insert_subset (mem_filter.mpr ⟨mem_erase.mpr ⟨zr,mem_univ _⟩,zp⟩ : z∈K) inside
      simpa only [card_insert_of_not_mem miss] using card_le_card sub
    · simpa using card_le_card inside
  have cb : Disjoint C Y := disjoint_left.mpr (fun x xc xy => (mem_filter.mp xc).2.ne (mem_filter.mp xy).2)
  have bc : B.card=C.card+Y.card := card_union_of_disjoint cb
  have bs : B⊆D := union_subset (filter_subset ..) (filter_subset ..)
  have ds := card_sdiff_add_card_eq_card bs
  have ss := card_sdiff_add_card_inter S B
  have oc := card_le_card outside
  have cap := child_bound T tree r q rank down take C
  change K.card+(if r∈C ∧ r∈leaves T then 1 else 0)≤C.card+(∑ x∈C,(T.degree x-2))+(if r∈C then 1 else 0) at cap
  simp only [rc] at cap hit
  omega

#print axioms child_bound
#print axioms forest_width
end Minimal180.Transversals
