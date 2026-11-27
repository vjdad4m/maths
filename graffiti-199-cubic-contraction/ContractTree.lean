import ContractEdge
import RootedTreeRank

namespace Graffiti199Depleted.ContractedEdge

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} (E : ContractedEdge G)
variable [DecidableEq V] [Fintype V]

private def expansion (T : Finset E.Vertex) : Finset V :=
  Finset.univ.filter fun x => E.project x ∈ T

private theorem mem_expansion {T : Finset E.Vertex} {x : V} :
    x ∈ E.expansion T ↔ E.project x ∈ T := by simp [expansion]

private theorem expanded_tree {T : Finset E.Vertex}
    (tree : (E.graph.induce (↑T : Set E.Vertex)).IsTree)
    (noCommon : ∀ x, ¬ (G.Adj x E.a ∧ G.Adj x E.b)) :
    (G.induce (↑(E.expansion T) : Set V)).IsTree := by
  classical
  let S := E.expansion T
  let H := E.graph.induce (↑T : Set E.Vertex)
  let J := G.induce (↑S : Set V)
  let f : (↑S : Set V) → (↑T : Set E.Vertex) := fun x =>
    ⟨E.project x.val,(E.mem_expansion).mp x.property⟩
  let g : (↑T : Set E.Vertex) → (↑S : Set V) := fun x =>
    ⟨E.representative x.val,(E.mem_expansion).mpr (by simp)⟩
  have fg (x : (↑T : Set E.Vertex)) : f (g x) = x := Subtype.ext (E.project_rep _)
  have gf (x : (↑S : Set V)) (off : x.val ≠ E.b) : g (f x) = x :=
    Subtype.ext (E.rep_project _ off)
  have hit_b (xb : E.b ∈ S) : (none : E.Vertex) ∈ T := by
    simpa using (E.mem_expansion).mp xb
  letI : Nonempty (↑T : Set E.Vertex) := tree.isConnected.nonempty
  let r : (↑T : Set E.Vertex) :=
    if h : none ∈ T then ⟨none,h⟩ else Classical.choice inferInstance
  have r_none (h : none ∈ T) : r.val = none := by simp [r,h]
  have f_b (x : (↑S : Set V)) (eq : x.val = E.b) : f x = r := by
    apply Subtype.ext
    change E.project x.val = r.val
    have bIn : E.b ∈ S := eq ▸ x.property
    simp [eq,r_none (hit_b bIn)]
  have f_a (x : (↑S : Set V)) (eq : x.val = E.a) : f x = r := by
    have aIn : E.a ∈ S := eq ▸ x.property
    have none : (none : E.Vertex) ∈ T := by simpa using (E.mem_expansion).mp aIn
    apply Subtype.ext
    change E.project x.val = r.val
    simp [eq,r_none none]
  have fb_val (x : (↑S : Set V)) (eq : x.val = E.b) : (g r).val = E.a := by
    change E.representative r.val = E.a
    rw [← f_b x eq]
    change E.representative (E.project x.val) = E.a
    simp [eq]
  obtain ⟨rho,zero,separate,parent⟩ := Catalogue.rooted_tree_rank tree r
  let rank (x : (↑S : Set V)) : ℕ := if x.val = E.b then 1 else 2 * rho (f x)
  have zero_rank (x : (↑S : Set V)) : rank x = 0 ↔ x = g r := by
    by_cases xb : x.val = E.b
    · have ne : x ≠ g r := fun h => E.rep_ne_b r.val ((congrArg Subtype.val h).symm.trans xb)
      simp [rank,xb,ne]
    · simp only [rank,if_neg xb,Nat.mul_eq_zero,show (2 : ℕ) ≠ 0 by decide,false_or,zero]
      exact ⟨fun eq => (gf x xb).symm.trans (congrArg g eq),fun eq => eq.symm ▸ fg r⟩
  have outside_adj {x y : (↑S : Set V)} (xa : x.val ≠ E.a) (xb : x.val ≠ E.b)
      (h : J.Adj x y) : H.Adj (f x) (f y) := by
    rcases E.project_adj_or_eq h with e|same
    · exact e
    · have eq : f x = f y := Subtype.ext same
      by_cases yb : y.val = E.b
      · have hnone : E.project x.val = none := by
          change E.project x.val = E.project y.val at same
          rwa [yb,E.project_b] at same
        exact ((E.project_none_iff _).mp hnone).elim (fun h => (xa h).elim) (fun h => (xb h).elim)
      · exact (h.ne ((gf x xb).symm.trans ((congrArg g eq).trans (gf y yb)))).elim
  have lift_neighbor (x : (↑S : Set V)) (out : x.val ≠ E.a ∧ x.val ≠ E.b)
      (p : (↑T : Set E.Vertex)) (hp : H.Adj (f x) p) :
      ∃! y : (↑S : Set V), J.Adj x y ∧ f y = p := by
    have fx : E.project x.val = some ⟨x.val,out⟩ := E.project_of_other _ out
    have eqp {y : (↑S : Set V)} (eq : f y = p) : E.project y.val = p.val := congrArg Subtype.val eq
    rcases p with ⟨p,pm⟩
    cases p with
    | none =>
      have hits : G.Adj E.a x.val ∨ G.Adj E.b x.val := by
        change E.graph.Adj (E.project x.val) none at hp
        rw [fx] at hp
        exact hp
      let a : (↑S : Set V) := ⟨E.a,(E.mem_expansion).mpr (by simpa using pm)⟩
      let b : (↑S : Set V) := ⟨E.b,(E.mem_expansion).mpr (by simpa using pm)⟩
      have both (y : (↑S : Set V)) (same : f y = ⟨none,pm⟩) : y = a ∨ y = b :=
        ((E.project_none_iff _).mp (eqp same)).imp Subtype.ext Subtype.ext
      rcases hits with ha|hb
      · refine ⟨a,⟨ha.symm,Subtype.ext E.project_a⟩,?_⟩
        intro y hy
        rcases both y hy.2 with ya|yb
        · exact ya
        · rw [yb] at hy
          exact (noCommon x.val ⟨ha.symm,hy.1⟩).elim
      · refine ⟨b,⟨hb.symm,Subtype.ext E.project_b⟩,?_⟩
        intro y hy
        rcases both y hy.2 with ya|yb
        · rw [ya] at hy
          exact (noCommon x.val ⟨hy.1,hb.symm⟩).elim
        · exact yb
    | some w =>
      let y := g ⟨some w,pm⟩
      have adj : J.Adj x y := by
        change E.graph.Adj (E.project x.val) (some w) at hp
        rw [fx] at hp
        exact hp
      refine ⟨y,⟨adj,fg _⟩,?_⟩
      intro z hz
      have off : z.val ≠ E.b := by
        intro eq
        have ps := eqp hz.2
        simp [eq] at ps
      exact (gf z off).symm.trans (congrArg g hz.2)
  apply Catalogue.tree_of_rank (G := J) (g r) rank
  · intro x y edge eq
    by_cases xb : x.val = E.b
    · by_cases yb : y.val = E.b
      · exact edge.ne (Subtype.ext (xb.trans yb.symm))
      · simp [rank,xb,yb] at eq
        omega
    · by_cases yb : y.val = E.b
      · simp [rank,xb,yb] at eq
      · have mapped : H.Adj (f x) (f y) := by
          rcases E.project_adj_or_eq edge with h|h
          · exact h
          · exact (edge.ne ((gf x xb).symm.trans ((congrArg g (Subtype.ext h)).trans (gf y yb)))).elim
        apply separate mapped
        simp [rank,xb,yb] at eq
        omega
  · intro x h
    have hz := (zero_rank (g r)).mpr rfl
    omega
  · intro x xroot
    by_cases xb : x.val = E.b
    · have fgVal := fb_val x xb
      have edge : J.Adj x (g r) := by
        change G.Adj x.val (g r).val
        rw [xb,fgVal]
        exact E.edge.symm
      have r0 := (zero_rank (g r)).mpr rfl
      have x1 : rank x = 1 := by simp [rank,xb]
      refine ⟨g r,⟨edge,by omega⟩,?_⟩
      intro y hy
      apply (zero_rank y).mp
      have ly := hy.2
      omega
    · have xa : x.val ≠ E.a := fun ha => xroot ((gf x xb).symm.trans (congrArg g (f_a x ha)))
      have fNotRoot : f x ≠ r := fun eq => xroot ((gf x xb).symm.trans (congrArg g eq))
      have pos : 0 < rho (f x) := Nat.pos_of_ne_zero (fun h => fNotRoot ((zero _).mp h))
      obtain ⟨p,⟨adj,lt⟩,unique⟩ := parent (f x) fNotRoot
      obtain ⟨y,⟨edge,fy⟩,uniqueLift⟩ := lift_neighbor x ⟨xa,xb⟩ p adj
      have lower : rank y < rank x := by
        by_cases yb : y.val = E.b
        · simp [rank,xb,yb]
          omega
        · simp [rank,xb,yb,fy]
          omega
      refine ⟨y,⟨edge,lower⟩,?_⟩
      intro z hz
      have lt' : rho (f z) < rho (f x) := by
        by_cases zb : z.val = E.b
        · rw [f_b z zb,(zero r).mpr rfl]
          exact pos
        · have t := hz.2
          simp [rank,xb,zb] at t
          omega
      exact uniqueLift z ⟨hz.1,unique (f z) ⟨outside_adj xa xb hz.1,lt'⟩⟩

/-- Splitting the contracted vertex expands any induced tree, because
each outside vertex is adjacent to at most one end of the split edge. -/
theorem treeNumber_le
    (noCommon : ∀ x, ¬ (G.Adj x E.a ∧ G.Adj x E.b)) :
    Catalogue.treeNumber E.graph ≤ Catalogue.treeNumber G := by
  classical
  unfold Catalogue.treeNumber
  apply Finset.sup_le
  intro T ht
  have tree := (Finset.mem_filter.mp ht).2
  change T.card ≤ Catalogue.treeNumber G
  have sub : T.map E.representative ⊆ E.expansion T := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
    exact (E.mem_expansion).mpr (by simpa using hy)
  have card := Finset.card_le_card sub
  rw [Finset.card_map] at card
  exact card.trans (Catalogue.card_le_treeNumber _ (E.expanded_tree tree noCommon))

#print axioms treeNumber_le

end Graffiti199Depleted.ContractedEdge
