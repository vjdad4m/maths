import Row534

namespace Restrained534
open Finset SimpleGraph CographRadius
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- An edge whose ends have no common neighbor. -/
def HasEdgeOffTriangles (H : SimpleGraph V) : Prop :=
  ∃ a b, H.Adj a b ∧ ∀ v, ¬ (H.Adj a v ∧ H.Adj b v)

omit [Fintype V] in
theorem dominating_pair_iff : HasEdgeOffTriangles Gᶜ ↔
    ∃ D : Finset V, D.card = 2 ∧ G.IsIndepSet D ∧ Dominates G D := by
  classical
  constructor
  · rintro ⟨a,b,edge,bare⟩
    obtain ⟨ab,nonadj⟩ := (G.compl_adj a b).mp edge
    let D : Finset V := {a,b}
    refine ⟨D,by simp [D,ab],?_,?_⟩
    · intro u hu v hv ne adj
      have split (x : V) (h : x ∈ D) : x = a ∨ x = b := by simpa [D] using h
      rcases split u hu with rfl|rfl <;> rcases split v hv with rfl|rfl
      · exact ne rfl
      · exact nonadj adj
      · exact nonadj adj.symm
      · exact ne rfl
    · intro v
      by_cases inside : v ∈ D
      · exact Or.inl inside
      · have va : v ≠ a := fun eq => inside (by simp [D,eq])
        have vb : v ≠ b := fun eq => inside (by simp [D,eq])
        by_cases av : G.Adj a v
        · exact Or.inr ⟨a,by simp [D],av.symm⟩
        · have bv : G.Adj b v := by
            by_contra miss
            exact bare v ⟨(G.compl_adj _ _).mpr ⟨va.symm,av⟩,
              (G.compl_adj _ _).mpr ⟨vb.symm,miss⟩⟩
          exact Or.inr ⟨b,by simp [D],bv.symm⟩
  · rintro ⟨D,sz,ind,dom⟩
    obtain ⟨a,b,ab,rfl⟩ := card_eq_two.mp sz
    have na : ¬ G.Adj a b := ind (by simp) (by simp) ab
    refine ⟨a,b,(G.compl_adj _ _).mpr ⟨ab,na⟩,?_⟩
    rintro v ⟨av,bv⟩
    have out : v ∉ ({a,b} : Finset V) := by simp [av.ne.symm,bv.ne.symm]
    obtain ⟨w,hw,vw⟩ := (dom v).resolve_left out
    rcases (show w = a ∨ w = b by simpa using hw) with rfl|rfl
    · exact ((G.compl_adj _ _).mp av).2 vw.symm
    · exact ((G.compl_adj _ _).mp bv).2 vw.symm

/-- A local test in the complement detects every equality case, even for
arbitrary join factors. Their induced subgraphs need not be cographs. -/
theorem join_equality [Nontrivial V] [DecidableRel G.Adj] (join : ProperJoin G)
    (deg : ∀ v, 2 ≤ G.degree v) :
    restrainedNumber G = independentDomination G ↔
      (∃ u, ∀ v, ¬ Gᶜ.Adj u v) ∨ HasEdgeOffTriangles Gᶜ := by
  classical
  have iso : (∃ u, ∀ v, ¬ Gᶜ.Adj u v) ↔ ∃ u, Universal G u := by
    constructor
    · rintro ⟨u,h⟩
      refine ⟨u,fun v ne => ?_⟩
      by_contra miss
      exact h v ((G.compl_adj _ _).mpr ⟨ne,miss⟩)
    · rintro ⟨u,h⟩
      exact ⟨u,fun v e => ((G.compl_adj _ _).mp e).2 (h v e.ne)⟩
  rw [iso]
  by_cases center : ∃ u, Universal G u
  · obtain ⟨u,hu⟩ := center
    rw [cone_formula G hu,independent_universal G hu,(cone_leafless G hu).mpr deg]
    exact ⟨fun _ => Or.inl ⟨u,hu⟩,fun _ => rfl⟩
  · rw [nonuniversal_join G join center,or_iff_right center,dominating_pair_iff]
    obtain ⟨T,ht,hi,hd⟩ := attained G
    constructor
    · intro eq
      exact ⟨T,ht.trans eq.symm,hi,hd⟩
    · rintro ⟨D,sz,ind,dom⟩
      have lo := two_le_of_no_universal G center hd
      have upper : independentDomination G ≤ 2 := Nat.sInf_le
        (s := {n : ℕ | ∃ S : Finset V, S.card = n ∧ G.IsIndepSet S ∧ Dominates G S})
        ⟨D,sz,ind,dom⟩
      omega

#print axioms dominating_pair_iff
#print axioms join_equality
end Restrained534
