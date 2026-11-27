import Seam180
import CoreSplit180

set_option warningAsError true
namespace Minimal180.OddBlock
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A second-form witness in the split case forces its entire tip wing to
be a single edge. -/
theorem second_wing_edge {J : SimpleGraph V} {x y w : V} {S T C : Finset V}
    (s : Split J w S T) (xs : x∈S) (ys : y∉S) (xw : J.Adj x w)
    (tip : NeedsTip J C (univ\C) x y) : S={x,w} := by
  classical
  let D := univ\C
  have wd : w∉D := fun h => tip.2.2.2.1 ⟨w,h,xw⟩
  let f (v : V) := decide (v∈S)
  have on : OnEdges J D f := by
    intro i hi j hj e
    rcases s.edges e with k|k
    · simp [f,k.1,k.2]
    · have ni : i∉S := fun h => wd ((s.common h k.1) ▸ hi)
      have nj : j∉S := fun h => wd ((s.common h k.2) ▸ hj)
      simp [f,ni,nj]
  have apart {z : V} (zd : z∈D) : z∉S := by
    intro zS
    have eq := ((connected_cuts J D).mp tip.2.2.1).2 f on z zd y tip.2.1
    simp [f,zS,ys] at eq
  apply Subset.antisymm _ (insert_subset xs (singleton_subset_iff.mpr s.both.1))
  intro i hi
  by_cases ix : i=x
  · exact ix ▸ mem_insert_self _ _
  by_cases iw : i=w
  · exact iw ▸ mem_insert_of_mem (mem_singleton_self _)
  have ic : i∈C := by by_contra h; exact apart (mem_sdiff.mpr ⟨mem_univ _,h⟩) hi
  obtain ⟨j,jd,e⟩ := tip.2.2.2.2 i ic ix
  rcases s.edges e with k|k
  · exact (apart jd k.2).elim
  · exact (iw (s.common hi k.1)).elim

/-- If neither wing is a single edge, the first form is equivalent to
unrestricted leaf gain. No assumption that such a gain occurs is built in. -/
theorem first_iff_split_gain {J : SimpleGraph V} (jc : J.Connected) (hn : 2<Fintype.card V)
    {x y w : V} {S T : Finset V} (s : Split J w S T)
    (xs : x∈S) (xt : x∉T) (yt : y∈T) (ys : y∉S) (xy : x≠y) (old : ¬J.Adj x y)
    (xw : J.Adj x w) (wy : J.Adj w y) (U : Finset V) (ls : S≠{x,w}) (rs : T≠{y,w}) :
    FirstForm J U x y w ↔ weightedLeaves J U<weightedLeaves (J⊔edge x y) U := by
  have iff := triangle_gain_iff_core J jc hn x y w xy old xw wy U
  constructor
  · rintro ⟨C,cu,wc,ct,win⟩
    exact iff.mpr ⟨C,cu,wc,ct,Or.inl win⟩
  · intro gain
    obtain ⟨C,cu,wc,ct,h⟩ := iff.mp gain
    rcases h with win|tip|tip
    · exact ⟨C,cu,wc,ct,win⟩
    · exact (ls (second_wing_edge s xs ys xw tip)).elim
    · exact (rs (second_wing_edge s.flip yt xt wy.symm tip)).elim

/-- An eligible pendant tip obstructs the first form. Exchanging the
middle for that tip in any proposed first certificate reaches the same
score already in the lower graph. -/
theorem pendant_excludes_first {J : SimpleGraph V} (jc : J.Connected) (hn : 2<Fintype.card V)
    {x y w : V} (xy : x≠y) (xw : J.Adj x w) (wy : J.Adj w y)
    (pend : ∀ j, J.Adj x j → j=w) (U : Finset V) (xu : x∈U) :
    ¬FirstForm J U x y w := by
  classical
  rintro ⟨C,cu,wc,size,sides,dom⟩
  let D := univ\C
  let R := D.erase x
  let F := insert x (C.erase w)
  have xd : x∈D := sides.1
  have yd : y∈D := sides.2.1
  have wd : w∉D := fun h => (mem_sdiff.mp h).2 wc
  have yr : y∈R := mem_erase.mpr ⟨xy.symm,yd⟩
  have xc : x∉C := (mem_sdiff.mp xd).2
  have con : Con J R := by
    apply (connected_cuts J R).mpr
    refine ⟨⟨y,yr⟩,?_⟩
    intro f on
    let g (v : V) := if v=x then f y else f v
    have good : OnEdges J D g := by
      intro i hi j hj e
      have ix : i≠x := fun h => wd ((pend _ (h ▸ e)) ▸ hj)
      have jx : j≠x := fun h => wd ((pend _ (h ▸ e.symm)) ▸ hi)
      simpa [g,ix,jx] using on i (mem_erase.mpr ⟨ix,hi⟩) j (mem_erase.mpr ⟨jx,hj⟩) e
    have cuts := sides.2.2.2 g good (by simp [g,xy.symm])
    intro i hi j hj
    simpa [g,(mem_erase.mp hi).1,(mem_erase.mp hj).1] using
      cuts i (mem_of_mem_erase hi) j (mem_of_mem_erase hj)
  have core : univ\F=insert w R := by
    ext i
    by_cases iw : i=w <;> by_cases ix : i=x <;> simp_all [F,R,D]
  have fu : F⊆U := insert_subset xu ((erase_subset _ _).trans cu)
  have equal : F.card=C.card := by
    change (insert x (C.erase w)).card=C.card
    rw [card_insert_of_not_mem (fun h => xc (mem_of_mem_erase h)),card_erase_add_one wc]
  have newcon : Con J (insert w R) := by
    apply con_of_neighbors J con (subset_insert _ _)
    intro z hz zr
    have eq := (mem_insert.mp hz).resolve_right zr
    exact eq ▸ ⟨y,yr,wy⟩
  have score := (score_iff_core J jc hn U C.card).mpr (by
    refine ⟨F,fu,equal.ge,core ▸ newcon,?_⟩
    intro i fi
    rw [core]
    rcases mem_insert.mp fi with eq|cw
    · exact eq ▸ ⟨w,mem_insert_self ..,xw⟩
    obtain ⟨j,jd,ij⟩ := dom i (mem_of_mem_erase cw)
    have jx : j≠x := fun h => (mem_erase.mp cw).1 (pend i (h ▸ ij.symm))
    exact ⟨j,mem_insert_of_mem (mem_erase.mpr ⟨jx,jd⟩),ij⟩)
  omega

#print axioms second_wing_edge
#print axioms first_iff_split_gain
#print axioms pendant_excludes_first
end Minimal180.OddBlock
