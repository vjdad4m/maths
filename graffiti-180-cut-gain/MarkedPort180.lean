import CutGain180
import TightWing180

set_option warningAsError true
namespace Minimal180.CutGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- With a free tip and a one-leaf increase upon marking the seam, one can
retain the old optimum while restricting the seam to that tip. -/
theorem ready_of_mark_gain {B : SimpleGraph V} (bc : B.Connected) {w x : V}
    (wx : B.Adj w x) (U E : Finset V) (free : x∉E) (off : ∀ i∈E, i≠w → i∈U)
    (rise : weightedLeaves B U<weightedLeaves B E) : Ready B w x U := by
  classical
  apply le_antisymm (leaf_mono B (prune_le ..) U)
  by_cases hn : 2<Fintype.card V
  · let H := prune B w {x}
    obtain ⟨M,mb,tr,top⟩ := tree_opt B bc E
    let C := E∩leaves M
    let D := univ\C
    have xc : x∉C := fun h => free (mem_inter.mp h).1
    have xd : x∈D := mem_sdiff.mpr ⟨mem_univ _,xc⟩
    have wc : w∈C := by
      by_contra no
      have inc : C⊆U∩leaves M := fun i h => mem_inter.mpr
        ⟨off i (mem_inter.mp h).1 (fun eq => no (eq ▸ h)),(mem_inter.mp h).2⟩
      have lim : (U∩leaves M).card≤weightedLeaves B U :=
        le_sup (f:=fun K => (U∩leaves K).card) (mem_filter.mpr ⟨mem_univ _,mb,tr⟩)
      have small := (card_le_card inc).trans lim
      change (E∩leaves M).card≤_ at small
      omega
    have out {i : V} (id : i∈D) : i≠w := fun h => (mem_sdiff.mp id).2 (h ▸ wc)
    obtain ⟨con,dom⟩ := leaf_core B M mb tr hn C inter_subset_right
    have base : Con H D := con.mono (fun a b e => prune_away (out a.property) (out b.property) e)
    have attach : Con H (insert w D) := con_of_neighbors H base (subset_insert ..) (by
      intro i hi no
      exact (mem_insert.mp hi).resolve_right no ▸ ⟨x,xd,prune_spoke wx (mem_singleton_self _)⟩)
    have bound := weightedCore H (insert w D) U attach (by
      intro i no
      obtain ⟨iw,ic⟩ : i≠w ∧ i∈C := by simpa [D] using no
      obtain ⟨j,jd,e⟩ := dom i ic
      exact ⟨j,mem_insert_of_mem jd,prune_away iw (out jd) e⟩)
    have inc : C.erase w⊆U\(insert w D) := by
      intro i hi
      obtain ⟨iw,ic⟩ := mem_erase.mp hi
      exact mem_sdiff.mpr ⟨off i (mem_inter.mp ic).1 iw,by simp [D,iw,ic]⟩
    have cap := (card_le_card inc).trans bound
    have sz := card_erase_add_one wc
    change C.card=weightedLeaves B E at top
    change weightedLeaves B U≤weightedLeaves H U
    omega
  · have eq : ({w,x}:Finset V)=univ := eq_of_subset_of_card_le (subset_univ _) (by
      rw [card_univ,card_pair wx.ne]; omega)
    have full : prune B w {x}=B := by
      apply le_antisymm (prune_le ..)
      intro i j e
      have nbr {a : V} (wa : B.Adj w a) : a∈({x}:Finset V) := by
        have am : a∈({w,x}:Finset V) := eq ▸ mem_univ _
        exact (mem_insert.mp am).resolve_left wa.ne.symm
      exact ⟨e,fun k => nbr (k ▸ e),fun k => nbr (k ▸ e.symm)⟩
    rw [full]

/-- A split with a doubly marked seam gains whenever both smaller rooted
wing bounds hold and the two tips belong to neither local eligibility
set. The root and the parity set are otherwise unrestricted. -/
theorem double_mark_gain {J : SimpleGraph V} (jc : J.Connected) (hn : 3<Fintype.card V)
    {x y w : V} {S T : Finset V} (s : Split J w S T) (xs : x∈S) (xt : x∉T) (yt : y∈T) (ys : y∉S)
    (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (nc : ((J⊔edge x y).induce ({w}ᶜ : Set V)).Preconnected)
    (drop : bipartiteNum (J⊔edge x y)<bipartiteNum J) (r : ↥S) (A P : Finset V)
    (wa : w∈A) (wp : w∈P) (xaf : x∉A) (xpf : x∉P) (yaf : y∉A) (ypf : y∉P) :
    let L (B : Finset V) := pull (fun v : ↥S => v.val) B
    let R (B : Finset V) := pull (fun v : ↥T => v.val) B
    let U := eligible A P r.val
    let E := eligible (L A) (L P) r
    let F := eligible (R A) (R P) ⟨w,s.both.2⟩
    weightedLeaves J U+bipartiteNum J=1+A.card+P.card →
    1+(L A).card+(L P).card≤weightedLeaves (side J S) E+bipartiteNum (side J S) →
    1+(R A).card+(R P).card≤weightedLeaves (side J T) F+bipartiteNum (side J T) →
    weightedLeaves J U<weightedLeaves (J⊔edge x y) U := by
  classical
  intro L R U E F tight lb rb
  have data := tight_wings jc s xs ys xy drop r A P tight lb rb
  obtain ⟨_,_,near,far⟩ := data
  have wu : w∈U := eligible_iff.mpr ⟨Or.inl wa,if h : w=r.val then Or.inr (h ▸ And.intro wa wp) else Or.inl h⟩
  apply (cut_gain_iff_wings jc hn s xs xt yt ys xy old xw wy nc U).mpr
  refine ⟨wu,?_,?_⟩
  · let l : ↥S := ⟨w,s.both.1⟩
    apply ready_of_mark_gain (s.connectedL jc) (show (side J S).Adj l ⟨x,xs⟩ from xw.symm) _ E
    · intro h
      exact (eligible_iff.mp h).1.elim (fun k => xaf (mem_pull.mp k)) (fun k => xpf (mem_pull.mp k))
    · intro i hi il
      obtain ⟨mark,root⟩ := eligible_iff.mp hi
      exact mem_pull.mpr (mem_erase.mpr ⟨fun h => il (Subtype.ext h),
        eligible_iff.mpr ⟨mark.imp mem_pull.mp mem_pull.mp,root.imp (fun ne eq => ne (Subtype.ext eq))
          (fun h => ⟨mem_pull.mp h.1,mem_pull.mp h.2⟩)⟩⟩)
    · change weightedLeaves (side J S) E=_ at near
      rw [near]
      simp [U,weight,wa]
  · let z : ↥T := ⟨w,s.both.2⟩
    apply ready_of_mark_gain (s.flip.connectedL jc) (show (side J T).Adj z ⟨y,yt⟩ from wy) _ F
    · intro h
      exact (eligible_iff.mp h).1.elim (fun k => yaf (mem_pull.mp k)) (fun k => ypf (mem_pull.mp k))
    · intro i hi iz
      have iw : i.val≠w := fun h => iz (Subtype.ext h)
      have ir : i.val≠r.val := fun h => iw (s.common (h.symm ▸ r.property) i.property)
      exact mem_pull.mpr (mem_erase.mpr ⟨iw,eligible_iff.mpr
        ⟨(eligible_iff.mp hi).1.imp mem_pull.mp mem_pull.mp,Or.inl ir⟩⟩)
    · change weightedLeaves (side J T) F=_ at far
      rw [far]
      simp [U,weight,wa,wp]

#print axioms ready_of_mark_gain
#print axioms double_mark_gain
end Minimal180.CutGain
