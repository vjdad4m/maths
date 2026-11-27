import Packing
import Bound

namespace Chain5169
open SimpleGraph Finset BullCover1125 TriangleMatching1078
variable {V : Type*} {G : SimpleGraph V}

/-- On a spanning path, pair consecutive vertices, reusing the previous vertex
as the partner of the final singleton when the order is odd. -/
theorem spanning_cover {m : ℕ} (hm : 1 ≤ m) (e : Fin (m+1) ≃ V)
    (next : ∀ i j : Fin (m+1), i.val+1 = j.val → G.Adj (e i) (e j)) :
    edgeCoverNumber G ≤ (m+2)/2 := by
  classical
  let start (k : Fin ((m+2)/2)) : Fin (m+1) := ⟨min (2*k.val) (m-1),by omega⟩
  let finish (k : Fin ((m+2)/2)) : Fin (m+1) := ⟨(start k).val+1,by dsimp [start]; omega⟩
  let edge (k : Fin ((m+2)/2)) : G.edgeSet := ⟨s(e (start k),e (finish k)),next _ _ rfl⟩
  let P := univ.image edge
  have cover : Covers G P := by
    intro v
    let i := e.symm v
    let k : Fin ((m+2)/2) := ⟨i.val / 2,by have := i.isLt; omega⟩
    refine ⟨edge k,mem_image.mpr ⟨k,mem_univ _,rfl⟩,?_⟩
    have atEnd : i = start k ∨ i = finish k := by
      have bounds := i.isLt
      by_cases h : i.val = (start k).val
      · exact Or.inl (Fin.ext h)
      · apply Or.inr ∘ Fin.ext
        dsimp [start,k] at h
        dsimp [finish,start,k]
        omega
    have vi : v = e i := (e.apply_symm_apply v).symm
    exact Sym2.mem_iff.mpr (atEnd.imp (fun h => vi.trans (congrArg e h)) (fun h => vi.trans (congrArg e h)))
  have cost : P.card ≤ (m+2)/2 := card_image_le.trans_eq (by simp)
  exact (Nat.sInf_le (s:={n | ∃ P : Finset G.edgeSet, P.card=n ∧ Covers G P}) ⟨P,rfl,cover⟩).trans cost

variable [Fintype V]

/-- Counting endpoints bounds the number of vertices covered by any edge cover. -/
theorem vertices_le_twice_cover (iso : IsolateFree G) :
    Fintype.card V ≤ 2 * edgeCoverNumber G := by
  classical
  obtain ⟨P,hp⟩ := (coverable_iff G).mpr iso
  obtain ⟨C,sz,hit⟩ := Nat.sInf_mem (s:={n | ∃ P : Finset G.edgeSet,P.card=n ∧ Covers G P}) ⟨_,P,rfl,hp⟩
  change C.card = edgeCoverNumber G at sz
  let ends (e : G.edgeSet) : Finset V := {e.val.out.1,e.val.out.2}
  have lower : univ ⊆ C.biUnion ends := by
    intro x _
    obtain ⟨e,he,hx⟩ := hit x
    rw [← e.val.out_eq] at hx
    exact mem_biUnion.mpr ⟨e,he,by simpa [ends] using Sym2.mem_iff.mp hx⟩
  calc
    _ = (univ : Finset V).card := card_univ.symm
    _ ≤ _ := card_le_card lower
    _ ≤ ∑ e ∈ C, (ends e).card := card_biUnion_le
    _ ≤ ∑ _ ∈ C, 2 := sum_le_sum fun e _ => (card_insert_le _ _).trans (by simp)
    _ = _ := by simp [sz,Nat.mul_comm]

/-- The induced-matching packing bound: if every edge touches at most one
designated edge, any line-graph dominating set must have at least as many
members as the number of designated edges. -/
theorem packing_lower {U I : Type*} [Fintype U] [Fintype I] (G : SimpleGraph U)
    [DecidableRel G.Adj] (M : I → G.edgeSet)
    (apart : ∀ (e : G.edgeSet) (i j : I),
      (∃ v, v ∈ e.val ∧ v ∈ (M i).val) → (∃ w, w ∈ e.val ∧ w ∈ (M j).val) → i=j) :
    Fintype.card I ≤ lineDomination G := by
  classical
  obtain ⟨D,sz,dom⟩ := EulerDom574.line_attained G
  have existsEdge (i : I) : ∃ e : ↥D, ∃ v, v ∈ e.val.val ∧ v ∈ (M i).val := by
    obtain ⟨e,he,hit⟩ := (dominates_iff G D).mp dom (M i)
    exact ⟨⟨e,he⟩,hit⟩
  choose pick hit using existsEdge
  have inj : Function.Injective pick := fun i j eq => apart (pick i).val i j (hit i) (eq ▸ hit j)
  simpa [sz] using Fintype.card_le_of_injective pick inj

end Chain5169
