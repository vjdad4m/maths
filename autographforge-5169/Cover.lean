import Local

namespace BullCover1125
open SimpleGraph Finset TriangleMatching1078

def IsolateFree {V : Type*} (G : SimpleGraph V) := ∀ v, ∃ w, G.Adj v w

def Covers {V : Type*} (G : SimpleGraph V) (P : Finset G.edgeSet) :=
  ∀ v : V, ∃ e ∈ P, v ∈ e.val

noncomputable def edgeCoverNumber {V : Type*} (G : SimpleGraph V) :=
  sInf {k : ℕ | ∃ P : Finset G.edgeSet, P.card=k ∧ Covers G P}

/-- NetworkX raises when an isolated vertex prevents an edge cover. The
upstream numerical table drops the missing cell. -/
noncomputable def edgeCoverValue {V : Type*} (G : SimpleGraph V) : Option ℕ := by
  classical
  exact if IsolateFree G then some (edgeCoverNumber G) else none

theorem coverable_iff {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (∃ P, Covers G P) ↔ IsolateFree G := by
  classical
  constructor
  · rintro ⟨P,covers⟩ v
    obtain ⟨e,_,mem⟩ := covers v
    obtain ⟨w,h⟩ := Sym2.mem_iff_exists.mp mem
    exact ⟨w,show s(v,w) ∈ G.edgeSet from h ▸ e.property⟩
  · intro iso
    refine ⟨univ,fun v => ?_⟩
    obtain ⟨w,h⟩ := iso v
    exact ⟨⟨s(v,w),h⟩,mem_univ _,Sym2.mem_iff.mpr (Or.inl rfl)⟩

/-- Transform any edge-dominating set, including one with repeated endpoints,
into an edge cover of size at most twice its cardinality. -/
theorem cover_from_domination {V : Type*} [Fintype V] (G : SimpleGraph V)
    (iso : IsolateFree G) (cl : Free G claw) (bu : Free G bull)
    {D : Finset G.edgeSet} (dom : Dominates G.lineGraph D) :
    ∃ P : Finset G.edgeSet, P.card ≤ 2*D.card ∧ Covers G P := by
  classical
  let S := univ.filter (fun v : V => ∃ e ∈ D, v ∈ e.val)
  have incident {v} : v ∈ S ↔ ∃ e ∈ D, v ∈ e.val := by simp [S]
  have hit {v w} (vw : G.Adj v w) : v ∈ S ∨ w ∈ S := by
    obtain ⟨e,he,z,ze,zw⟩ := (dominates_iff G D).mp dom ⟨s(v,w),vw⟩
    rcases Sym2.mem_iff.mp zw with rfl|rfl
    · exact Or.inl (incident.mpr ⟨_,he,ze⟩)
    · exact Or.inr (incident.mpr ⟨_,he,ze⟩)
  let left (e : G.edgeSet) := e.val.out.1
  let right (e : G.edgeSet) := e.val.out.2
  have repr (e : G.edgeSet) : s(left e,right e) = e.val := e.val.out_eq
  let X (e : G.edgeSet) := univ.filter fun x => x ∉ S ∧ (G.Adj (left e) x ∨ G.Adj (right e) x)
  have localPiece (e : ↥D) : ∃ P : Finset G.edgeSet, P.card ≤ 2 ∧
      ∀ v, v=left e ∨ v=right e ∨ v∈X e → ∃ f ∈ P, v ∈ f.val := by
    apply local_cover cl bu
    refine ⟨show s(left e,right e) ∈ G.edgeSet from repr e ▸ e.val.property,?_,?_,?_⟩
    · intro x hx
      have outside := (mem_filter.mp hx).2.1
      constructor
      · rintro rfl
        exact outside (incident.mpr ⟨e,e.property,Sym2.out_fst_mem _⟩)
      · rintro rfl
        exact outside (incident.mpr ⟨e,e.property,Sym2.out_snd_mem _⟩)
    · intro x hx y hy edge
      exact (hit edge).elim (mem_filter.mp hx).2.1 (mem_filter.mp hy).2.1
    · exact fun x hx => (mem_filter.mp hx).2.2
  choose piece cost covers using localPiece
  let P := univ.biUnion piece
  refine ⟨P,?_,?_⟩
  · calc
      P.card ≤ ∑ e, (piece e).card := card_biUnion_le
      _ ≤ ∑ _ : ↥D, 2 := sum_le_sum fun e _ => cost e
      _ = _ := by simp [Nat.mul_comm]
  · intro v
    have usePiece (e : ↥D) (h : v=left e ∨ v=right e ∨ v∈X e) : ∃ f ∈ P, v ∈ f.val := by
      obtain ⟨f,hf,ve⟩ := covers e v h
      exact ⟨f,mem_biUnion.mpr ⟨e,mem_univ _,hf⟩,ve⟩
    by_cases hv : v ∈ S
    · obtain ⟨e,he,ve⟩ := incident.mp hv
      rw [← repr e] at ve
      rcases Sym2.mem_iff.mp ve with h|h
      · exact usePiece ⟨e,he⟩ (Or.inl h)
      · exact usePiece ⟨e,he⟩ (Or.inr (Or.inl h))
    · obtain ⟨w,vw⟩ := iso v
      obtain ⟨e,he,we⟩ := incident.mp ((hit vw).resolve_left hv)
      rw [← repr e] at we
      apply usePiece ⟨e,he⟩
      apply Or.inr ∘ Or.inr
      refine mem_filter.mpr ⟨mem_univ _,hv,?_⟩
      rcases Sym2.mem_iff.mp we with h|h
      · exact Or.inl (h ▸ vw.symm)
      · exact Or.inr (h ▸ vw.symm)

theorem bound {V : Type*} [Fintype V] (G : SimpleGraph V)
    (iso : IsolateFree G) (cl : Free G claw) (bu : Free G bull) :
    edgeCoverNumber G ≤ 2*lineDomination G := by
  classical
  obtain ⟨D,sz,dom⟩ := Nat.sInf_mem (s:={k | ∃ D : Finset G.edgeSet,
    D.card=k ∧ Dominates G.lineGraph D}) ⟨_,univ,rfl,fun e => Or.inl (mem_univ e)⟩
  change D.card = lineDomination G at sz
  obtain ⟨P,small,hP⟩ := cover_from_domination G iso cl bu dom
  exact (Nat.sInf_le (s:={k | ∃ P : Finset G.edgeSet,P.card=k ∧ Covers G P})
    ⟨P,rfl,hP⟩).trans (sz ▸ small)

theorem row1125 {V : Type*} [Fintype V] (G : SimpleGraph V) (_order : 2 ≤ Fintype.card V)
    (cl : Free G claw) (co : ¬ Graffiti137.InducedPath G 4) {r : ℕ}
    (definedValue : edgeCoverValue G = some r) :
    r ≤ 2 * lineDomination G := by
  classical
  by_cases h : IsolateFree G
  · have eq : edgeCoverNumber G = r := by simpa [edgeCoverValue,h] using definedValue
    exact eq ▸ bound G h cl (cograph_bull_free co)
  · simp [edgeCoverValue,h] at definedValue

end BullCover1125
