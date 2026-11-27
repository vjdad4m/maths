import Controlled180
import SecondScores180
set_option warningAsError true
namespace Minimal180.Controlled
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The displayed return set itself yields a tree leaf certificate. -/
theorem return_certificate (J : SimpleGraph V) (C B Z : Finset V) (x y : V) (xy : x≠y)
    (tip : NeedsTip J C (univ\C) x y) (bc : B⊆C.erase x) (zs : Z⊆(univ\C).erase y)
    (links : ∀ b∈B,J.Adj x b)
    (join : ∀ H∈remote J ((univ\C)\Z) y,∃ b∈B,Dominates J H b)
    (serve : ∀ q∈demand J ((univ\C)\Z) C Z x,q∈B ∨ Dominates J B q) :
    let G := J⊔SimpleGraph.edge x y
    let L := (C.erase x\B)∪Z
    Con G (univ\L) ∧ ∀ q∈L,Dominates G (univ\L) q := by
  classical
  let G := J⊔SimpleGraph.edge x y
  let R := (univ\C)\Z
  let K := insert x B
  let L := (C.erase x\B)∪Z
  have yr : y∈R := mem_sdiff.mpr ⟨tip.2.1,fun h => (mem_erase.mp (zs h)).1 rfl⟩
  have xz : x∉Z := fun h => (mem_sdiff.mp (mem_of_mem_erase (zs h))).2 tip.1
  have split : univ\L=R∪K := by
    ext a
    by_cases ax : a=x
    · subst a; simp [L,R,K,xz]
    have bz (h:a∈B) := mem_of_mem_erase (bc h)
    have zc (h:a∈Z) := (mem_sdiff.mp (mem_of_mem_erase (zs h))).2
    simp only [L,R,K,mem_sdiff,mem_univ,true_and,mem_union,mem_erase,mem_insert,ax,
      not_false_eq_true,false_or]
    tauto
  change Con G (univ\L) ∧ ∀ q∈L,Dominates G (univ\L) q
  rw [split]
  constructor
  · apply (connected_cuts G (R∪K)).mpr
    have xk : x∈R∪K := mem_union_right _ (mem_insert_self ..)
    refine ⟨⟨x,xk⟩,?_⟩
    intro f edges
    have add : G.Adj x y := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,xy⟩)
    have root := edges x xk y (mem_union_left _ yr) add
    have sb (b:V) (h:b∈B) : f b=f x :=
      edges b (mem_union_right _ (mem_insert_of_mem h)) x xk (Or.inl (links b h).symm)
    have path {i j : V} (h : (within J R).Reachable i j) : f i=f j := by
      obtain ⟨p⟩ := h
      induction p with
      | nil => rfl
      | cons e _ ih => exact (edges _ (mem_union_left _ e.2.1) _ (mem_union_left _ e.2.2) (Or.inl e.1)).trans ih
    have all (a:V) (h:a∈R∪K) : f a=f x := by
      rcases mem_union.mp h with ar|ak
      · by_cases eq : part J R a=part J R y
        · have yy : y∈part J R a := eq ▸ (mem_part ..).mpr ⟨yr,.refl _⟩
          exact (path ((mem_part ..).mp yy).2).trans root.symm
        have hh : part J R a∈remote J R y := mem_erase.mpr ⟨eq,mem_image_of_mem _ ar⟩
        obtain ⟨b,hb,t,ht,bt⟩ := join _ hh
        obtain ⟨tr,p⟩ := (mem_part ..).mp ht
        exact (path p).trans ((edges t (mem_union_left _ tr) b (mem_union_right _ (mem_insert_of_mem hb))
          (Or.inl bt.symm)).trans (sb b hb))
      · rcases mem_insert.mp ak with e|h'
        · rw [e]
        · exact sb a h'
    exact fun a ha b hb => (all a ha).trans (all b hb).symm
  · intro q hl
    by_cases qr : Dominates J R q
    · obtain ⟨a,ha,e⟩ := qr
      exact ⟨a,mem_union_left _ ha,Or.inl e⟩
    by_cases qx : J.Adj q x
    · exact ⟨x,mem_union_right _ (mem_insert_self ..),Or.inl qx⟩
    have inc : q∈C.erase x∪Z := (union_subset_union_left (sdiff_subset : C.erase x\B⊆C.erase x)) hl
    have nb : q∉B := by
      rcases mem_union.mp hl with h|h
      · exact (mem_sdiff.mp h).2
      · exact fun k => (mem_sdiff.mp (mem_of_mem_erase (zs h))).2 (mem_of_mem_erase (bc k))
    rcases serve q ((mem_demand ..).mpr ⟨inc,qr,qx⟩) with k|⟨b,hb,e⟩
    · exact (nb k).elim
    · exact ⟨b,mem_union_right _ (mem_insert_of_mem hb),Or.inl e⟩

/-- Tightness of the upper eligible-leaf optimum prevents any valid return
set from saving more than one eligible vertex. -/
theorem release_bound (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (x y w : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U C B Z : Finset V) (cu : C⊆U) (count : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (bc : B⊆C.erase x) (zs : Z⊆(U\C).erase y)
    (links : ∀ b∈B,J.Adj x b)
    (join : ∀ H∈remote J ((univ\C)\Z) y,∃ b∈B,Dominates J H b)
    (serve : ∀ q∈demand J ((univ\C)\Z) C Z x,q∈B ∨ Dominates J B q) : Z.card≤B.card+1 := by
  classical
  let G := J⊔SimpleGraph.edge x y
  let L := (C.erase x\B)∪Z
  have zs' : Z⊆(univ\C).erase y := by
    intro t h
    obtain ⟨ty,tc⟩ := mem_erase.mp (zs h)
    exact mem_erase.mpr ⟨ty,mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp tc).2⟩⟩
  obtain ⟨conn,dom⟩ := return_certificate J C B Z x y xy tip bc zs' links join serve
  have leaves : L⊆U := by
    intro q h
    rcases mem_union.mp h with k|k
    · exact cu (mem_of_mem_erase (mem_sdiff.mp k).1)
    · exact (mem_sdiff.mp (mem_of_mem_erase (zs k))).1
  have cap := (score_iff_core G (hc.mono le_sup_left) hn U L.card).mpr ⟨L,leaves,le_rfl,conn,dom⟩
  have top := (second_scores J hc hn x y w xy old xw wy U C cu count tip).1
  have dis : Disjoint (C.erase x\B) Z := disjoint_left.mpr (fun q h z =>
    (mem_sdiff.mp (mem_of_mem_erase (zs z))).2 (mem_of_mem_erase (mem_sdiff.mp h).1))
  have nL : L.card=(C.erase x\B).card+Z.card := card_union_of_disjoint dis
  have nC := card_erase_add_one tip.1
  have nB := card_sdiff_add_card_eq_card bc
  change weightedLeaves G U=weightedLeaves J U+1 at top
  omega

#print axioms return_certificate
#print axioms release_bound
end Minimal180.Controlled
