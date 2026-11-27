import Row1078

namespace EulerDom574
open Finset SimpleGraph TriangleMatching1078
variable {V : Type*} (G : SimpleGraph V)

noncomputable def domination := sInf {k | ∃ S : Finset V, S.card=k ∧ Dominates G S}

theorem attained [Fintype V] : ∃ S : Finset V, S.card=domination G ∧ Dominates G S := by
  exact Nat.sInf_mem (s:={k | ∃ S : Finset V, S.card=k ∧ Dominates G S})
    ⟨_,univ,rfl,fun v => Or.inl (mem_univ v)⟩

theorem line_attained [Fintype V] [DecidableRel G.Adj] :
    ∃ D : Finset G.edgeSet, D.card=lineDomination G ∧ Dominates G.lineGraph D := by
  classical
  exact Nat.sInf_mem (s:={k | ∃ S : Finset G.edgeSet, S.card=k ∧ Dominates G.lineGraph S})
    ⟨_,univ,rfl,fun e => Or.inl (mem_univ e)⟩

/-- At minimum degree two, discard one endpoint of an edge-dominating set.
Every outside vertex still sees a retained endpoint. -/
theorem upper [Fintype V] [DecidableRel G.Adj] [Nonempty V] (deg : ∀ v, 2 ≤ G.degree v) :
    domination G + 1 ≤ 2 * lineDomination G := by
  classical
  obtain ⟨D,sizeD,hD⟩ := line_attained G
  let ends (e : G.edgeSet) := univ.filter (fun v : V => v ∈ e.val)
  let T := D.biUnion ends
  have inside {v : V} : v ∈ T ↔ ∃ e ∈ D, v ∈ e.val := by simp [T,ends]
  have size (e : G.edgeSet) : (ends e).card ≤ 2 := by
    rcases e with ⟨q,hq⟩
    induction q using Sym2.ind with
    | h a b =>
      apply le_trans (card_le_card (t:={a,b}) ?_) (card_insert_le _ _ |>.trans (by simp))
      intro v hv
      simpa [Sym2.mem_iff] using (mem_filter.mp hv).2
  have bound : T.card ≤ 2*D.card := calc
    _ ≤ ∑ e ∈ D, (ends e).card := card_biUnion_le
    _ ≤ ∑ _ ∈ D, 2 := sum_le_sum (fun e _ => size e)
    _ = _ := by simp [Nat.mul_comm]
  have hit {a b : V} (ab : G.Adj a b) : a ∈ T ∨ b ∈ T := by
    obtain ⟨e,he,z,ze,zab⟩ := (dominates_iff G D).mp hD ⟨s(a,b),ab⟩
    rcases Sym2.mem_iff.mp zab with rfl|rfl
    · exact Or.inl (inside.mpr ⟨_,he,ze⟩)
    · exact Or.inr (inside.mpr ⟨_,he,ze⟩)
  have member : T.Nonempty := by
    let v := Classical.arbitrary V
    obtain ⟨w,hw⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset v).card from by
      rw [card_neighborFinset_eq_degree]; have := deg v; omega)
    rcases hit ((G.mem_neighborFinset _ _).mp hw) with h|h <;> exact ⟨_,h⟩
  obtain ⟨x,hx⟩ := member
  have other : ∃ y ∈ T, G.Adj x y := by
    obtain ⟨e,he,hxe⟩ := inside.mp hx
    obtain ⟨y,rep⟩ := Sym2.mem_iff_exists.mp hxe
    exact ⟨y,inside.mpr ⟨e,he,by rw [rep]; exact Sym2.mem_iff.mpr (Or.inr rfl)⟩,
      (show s(x,y) ∈ G.edgeSet from rep ▸ e.property)⟩
  have dominates : Dominates G (T.erase x) := by
    intro v
    by_cases vx : v = x
    · subst v
      obtain ⟨y,hy,xy⟩ := other
      exact Or.inr ⟨y,mem_erase.mpr ⟨xy.ne.symm,hy⟩,xy⟩
    by_cases h : v ∈ T
    · exact Or.inl (mem_erase.mpr ⟨vx,h⟩)
    have card : 1 < (G.neighborFinset v).card := by rw [card_neighborFinset_eq_degree]; exact deg v
    obtain ⟨y,hy,ne⟩ := exists_mem_ne card x
    have vy := (G.mem_neighborFinset _ _).mp hy
    exact Or.inr ⟨y,mem_erase.mpr ⟨ne,(hit vy).resolve_left h⟩,vy⟩
  have small : domination G ≤ (T.erase x).card := Nat.sInf_le ⟨T.erase x,rfl,dominates⟩
  have drop := card_erase_add_one hx
  omega
#print axioms upper
end EulerDom574
