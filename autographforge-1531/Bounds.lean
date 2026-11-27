import Row2560
import DegreeTwoClass

namespace EdgeCover1531
open SimpleGraph Finset BullCover1125 TriangleMatching1078 Graffiti271 GraffitiDegreeTwo
variable {V : Type*} {G : SimpleGraph V}

theorem triangle_free_excludes_bull (tri : TriangleFree G) : Free G bull := by
  rintro ⟨f⟩
  exact tri (f 0) (f 1) (f 4) (f.map_rel_iff.mpr (by decide)) (f.map_rel_iff.mpr (by decide))
    (f.map_rel_iff.mpr (by decide))

theorem row1531 [Fintype V] (_hn : 2 ≤ Fintype.card V) (cl : Free G claw) (tri : TriangleFree G)
    {r : ℕ} (numeric : edgeCoverValue G = some r) : r ≤ 2 * lineDomination G := by
  classical
  by_cases hi : IsolateFree G
  · have eq : edgeCoverNumber G = r := by simpa [edgeCoverValue,hi] using numeric
    have h := Packing2560.refined hi cl
    simpa [eq,(Packing2560.packing_zero_iff G).mpr (triangle_free_excludes_bull tri)] using h
  · simp [edgeCoverValue,hi] at numeric

variable [Fintype V]

theorem two_neighbors (cl : Free G claw) (tri : TriangleFree G) (v : V) : (nbr G v).card ≤ 2 := by
  refine Packing2560.neighbor_limit cl ?_ v ?_
  · intro x hx y hy xy
    exact tri v x y ((mem_nbr G).mp hx) xy ((mem_nbr G).mp hy).symm
  · exact fun x hx => (mem_nbr G).mp hx

omit [Fintype V] in
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

/-- Each selected edge sees at most three edges counting itself.
The two endpoint incidence sets overlap in at least the selected edge. -/
theorem count_dominated_edges [DecidableRel G.Adj] (hd : ∀ v, G.degree v ≤ 2) :
    Nat.card G.edgeSet ≤ 3 * lineDomination G := by
  classical
  obtain ⟨D,sz,dom⟩ := Nat.sInf_mem (s:={k | ∃ D : Finset G.edgeSet,
    D.card=k ∧ Dominates G.lineGraph D}) ⟨_,univ,rfl,fun e => Or.inl (mem_univ e)⟩
  change D.card = lineDomination G at sz
  let patch (e : G.edgeSet) := G.incidenceFinset e.val.out.1 ∪ G.incidenceFinset e.val.out.2
  have size (e : G.edgeSet) : (patch e).card ≤ 3 := by
    let a := e.val.out.1
    let b := e.val.out.2
    have first : e.val ∈ G.incidenceFinset a := (G.mem_incidenceFinset _ _).2 ⟨e.property,Sym2.out_fst_mem _⟩
    have second : e.val ∈ G.incidenceFinset b := (G.mem_incidenceFinset _ _).2 ⟨e.property,Sym2.out_snd_mem _⟩
    have pos := card_pos.mpr ⟨_,mem_inter.mpr ⟨first,second⟩⟩
    have sum := card_union_add_card_inter (G.incidenceFinset a) (G.incidenceFinset b)
    rw [G.card_incidenceFinset_eq_degree,G.card_incidenceFinset_eq_degree] at sum
    change (G.incidenceFinset a ∪ G.incidenceFinset b).card ≤ 3
    have ha := hd a
    have hb := hd b
    omega
  have sub : G.edgeFinset ⊆ D.biUnion patch := by
    intro t ht
    have edge : t ∈ G.edgeSet := mem_edgeFinset.mp ht
    obtain ⟨f,hf,v,vf,vt⟩ := (dominates_iff G D).mp dom ⟨t,edge⟩
    refine mem_biUnion.mpr ⟨f,hf,mem_union.mpr ?_⟩
    rw [← f.val.out_eq] at vf
    rcases Sym2.mem_iff.mp vf with h|h
    · exact Or.inl ((G.mem_incidenceFinset _ _).mpr ⟨edge,h ▸ vt⟩)
    · exact Or.inr ((G.mem_incidenceFinset _ _).mpr ⟨edge,h ▸ vt⟩)
  calc
    Nat.card G.edgeSet = G.edgeFinset.card := by rw [Nat.card_eq_fintype_card,G.edgeFinset_card]
    _ ≤ _ := card_le_card sub
    _ ≤ ∑ e ∈ D, (patch e).card := card_biUnion_le
    _ ≤ ∑ _ ∈ D, 3 := sum_le_sum (fun e _ => size e)
    _ = _ := by simp [sz,Nat.mul_comm]

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

theorem connected_cover_bound (hn : 2 ≤ Fintype.card V) (hc : G.Connected) (cl : Free G claw)
    (tri : TriangleFree G) : edgeCoverNumber G ≤ (Fintype.card V + 1)/2 := by
  obtain ⟨m,hm,e,wrap,shape⟩ := degree_two_indexed G hc hn (two_neighbors cl tri)
  have card := Fintype.card_congr e
  rw [Fintype.card_fin] at card
  rw [← card]
  exact spanning_cover hm e (fun i j eq => (shape i j).mpr (Or.inl eq))

theorem edge_budget (cl : Free G claw) (tri : TriangleFree G) :
    Nat.card G.edgeSet ≤ 3 * lineDomination G := by
  classical
  apply count_dominated_edges
  intro v
  have same : G.neighborFinset v = nbr G v := by ext x; simp
  simpa [← G.card_neighborFinset_eq_degree v,same] using two_neighbors cl tri v

theorem equality_orders (hn : 2 ≤ Fintype.card V) (hc : G.Connected) (cl : Free G claw)
    (tri : TriangleFree G) (tight : edgeCoverNumber G = 2*lineDomination G) :
    Fintype.card V = 3 ∨ Fintype.card V = 4 ∨ Fintype.card V = 7 := by
  classical
  have cover := connected_cover_bound hn hc cl tri
  have cap := edge_budget cl tri
  have lower := hc.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card (α:=V)] at lower
  omega
end EdgeCover1531
