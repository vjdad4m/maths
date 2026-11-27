import MatchingBasis
import Mathlib.Combinatorics.SimpleGraph.LineGraph

namespace TriangleMatching1078
open Finset SimpleGraph Graffiti326 AutoGraphForge378 AutoGraphForge1883
variable {V : Type*} (G : SimpleGraph V)

/-- Three cyclic adjacency hypotheses are the triangle predicate used in row 1160. -/
def TriangleFree := ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj z x

/-- GraphCalc calls domination_number on the line graph. -/
def Dominates {W : Type*} (H : SimpleGraph W) (S : Finset W) :=
  ∀ v, v ∈ S ∨ ∃ u ∈ S, H.Adj v u

noncomputable def lineDomination := sInf {k | ∃ D : Finset G.edgeSet,
    D.card = k ∧ Dominates G.lineGraph D}

/-- An edge dominates itself, or another edge sharing an endpoint. -/
theorem dominates_iff (D : Finset G.edgeSet) : Dominates G.lineGraph D ↔
    ∀ e : G.edgeSet, ∃ f ∈ D, ∃ v, v ∈ f.val ∧ v ∈ e.val := by
  constructor
  · intro h e
    rcases h e with mem | ⟨f,mem,adj⟩
    · exact ⟨e,mem,_,Sym2.out_fst_mem _,Sym2.out_fst_mem _⟩
    · obtain ⟨_,v,ve,vf⟩ := lineGraph_adj_iff_exists.mp adj
      exact ⟨f,mem,v,vf,ve⟩
  · intro h e
    obtain ⟨f,mem,v,vf,ve⟩ := h e
    by_cases eq : e = f
    · exact Or.inl (eq ▸ mem)
    · exact Or.inr ⟨f,mem,lineGraph_adj_iff_exists.mpr ⟨eq,v,ve,vf⟩⟩

/-- In a triangle-free graph an edge contains at most one neighbor of x. -/
theorem neighbors_in_edge (ht : TriangleFree G) {x u v : V} (e : G.edgeSet)
    (xu : G.Adj x u) (xv : G.Adj x v) (hu : u ∈ e.val) (hv : v ∈ e.val) : u = v := by
  by_contra different
  have eq := (Sym2.mem_and_mem_iff different).mp ⟨hu,hv⟩
  have uv := e.property
  rw [eq] at uv
  exact ht x u v xu uv xv.symm

/-- Some vertex has all its neighbors incident to selected edges. If there is
an uncovered vertex, any such vertex works. Otherwise every vertex works. -/
theorem neighborhood_covered [Nonempty V] {D : Finset G.edgeSet}
    (dom : Dominates G.lineGraph D) : ∃ x : V, ∀ y, G.Adj x y → ∃ e ∈ D, y ∈ e.val := by
  classical
  by_cases all : ∀ y : V, ∃ e ∈ D, y ∈ e.val
  · exact ⟨Classical.arbitrary V,fun y _ => all y⟩
  push_neg at all
  obtain ⟨x,uncovered⟩ := all
  refine ⟨x,fun y xy => ?_⟩
  obtain ⟨e,he,z,ze,zxy⟩ := (dominates_iff G D).mp dom ⟨s(x,y),xy⟩
  rcases Sym2.mem_iff.mp zxy with rfl|rfl
  · exact (uncovered e he ze).elim
  · exact ⟨e,he,ze⟩

/-- Each neighbor chooses one selected edge. Triangle-freeness makes the
choice injective, even if the selected edges have common endpoints. -/
theorem degree_le_of_dominating [Fintype V] [DecidableRel G.Adj] [Nonempty V]
    (ht : TriangleFree G) {D : Finset G.edgeSet} (dom : Dominates G.lineGraph D) :
    ∃ x : V, G.degree x ≤ D.card := by
  classical
  obtain ⟨x,covered⟩ := neighborhood_covered G dom
  have pick (y : ↥(G.neighborFinset x)) : ∃ e : ↥D, y.val ∈ e.val.val := by
    obtain ⟨e,he,h⟩ := covered y ((G.mem_neighborFinset _ _).mp y.property)
    exact ⟨⟨e,he⟩,h⟩
  choose edge incident using pick
  have inj : Function.Injective edge := by
    intro a b same
    apply Subtype.ext
    exact neighbors_in_edge G ht (edge a).val ((G.mem_neighborFinset _ _).mp a.property)
      ((G.mem_neighborFinset _ _).mp b.property) (incident a) (same ▸ incident b)
  exact ⟨x,by simpa only [Fintype.card_coe, card_neighborFinset_eq_degree] using Fintype.card_le_of_injective edge inj⟩

variable [Fintype V] [DecidableRel G.Adj]

theorem minDegree_le_lineDomination [Nonempty V] (ht : TriangleFree G) :
    G.minDegree ≤ lineDomination G := by
  classical
  have all : Dominates G.lineGraph univ := fun e => Or.inl (mem_univ e)
  obtain ⟨D,sz,dom⟩ := Nat.sInf_mem (s := {k | ∃ D : Finset G.edgeSet,
    D.card = k ∧ Dominates G.lineGraph D}) ⟨_,univ,rfl,all⟩
  obtain ⟨v,hv⟩ := degree_le_of_dominating G ht dom
  exact (G.minDegree_le_degree v).trans (hv.trans_eq sz)

omit [Fintype V] [DecidableRel G.Adj] in
/-- The edge family belonging to a maximal matching dominates the line graph.
The proof applies also to an edgeless graph and its empty matching. -/
theorem lineDomination_le_of_maximal {k : ℕ} (hm : HasMaximalMatching G k) :
    lineDomination G ≤ k := by
  classical
  obtain ⟨f,edges,maximal⟩ := hm
  let edge (i : Fin k) : G.edgeSet := ⟨s(f (i,false),f (i,true)),edges i⟩
  let D := univ.image edge
  suffices dom : Dominates G.lineGraph D by
    exact (Nat.sInf_le (s := {n | ∃ S : Finset G.edgeSet, S.card=n ∧ Dominates G.lineGraph S})
      ⟨D,rfl,dom⟩).trans (by simpa [D] using card_image_le (f:=edge) (s:=univ))
  apply (dominates_iff G D).mpr
  intro e
  obtain ⟨e,ge⟩ := e
  induction e using Sym2.ind with
  | h a b =>
    have hit : a ∈ support f ∨ b ∈ support f := by
      by_contra! miss
      exact maximal a miss.1 b miss.2 ge
    have covered (x : V) (hx : x ∈ support f) : ∃ ed ∈ D, x ∈ ed.val := by
      obtain ⟨i,t,rfl⟩ := (Graffiti326.mem_support f).mp hx
      exact ⟨edge i,mem_image_of_mem _ (mem_univ _),by cases t <;> simp [edge]⟩
    rcases hit with ha|hb
    · obtain ⟨ed,he,h⟩ := covered a ha
      exact ⟨ed,he,a,h,Sym2.mem_iff.mpr (Or.inl rfl)⟩
    · obtain ⟨ed,he,h⟩ := covered b hb
      exact ⟨ed,he,b,h,Sym2.mem_iff.mpr (Or.inr rfl)⟩

omit [DecidableRel G.Adj] in
theorem lineDomination_le_matching : lineDomination G ≤ minMaximalMatching G := by
  obtain ⟨f,edges⟩ := matchingNumber_attained G
  have maximal : HasMaximalMatching G (matchingNumber G) := by
    refine ⟨f,edges,?_⟩
    intro u hu v hv adj
    have impossible := matchingNumber_upper (matching_extend edges hu hv adj)
    omega
  exact lineDomination_le_of_maximal G (Nat.sInf_mem (s:={k | HasMaximalMatching G k}) ⟨_,maximal⟩)

/-- The exact rational value of GraphCalc's sum(degrees)/order. -/
noncomputable def averageDegree : ℚ := (∑ v, (G.degree v : ℚ)) / Fintype.card V

theorem average_regular [Nonempty V] {d : ℕ} (r : G.IsRegularOfDegree d) :
    averageDegree G = d := by
  have deg (v : V) : G.degree v = d := r v
  have hn : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [averageDegree,deg,hn]

theorem row1078 (hn : 2 ≤ Fintype.card V) (regular : ∃ d, G.IsRegularOfDegree d)
    (ht : TriangleFree G) :
    averageDegree G ≤ (lineDomination G : ℚ) ∧
    averageDegree G ≤ (minMaximalMatching G : ℚ) := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨d,reg⟩ := regular
  rw [average_regular G reg]
  have h := (G.le_minDegree_of_forall_le_degree d (fun v => (reg v).ge)).trans
    (minDegree_le_lineDomination G ht)
  exact ⟨by exact_mod_cast h,by exact_mod_cast h.trans (lineDomination_le_matching G)⟩

open AutoGraphForge1080 in
theorem sharp (d : ℕ) (hd : 0 < d) :
    TriangleFree (biclique d) ∧ averageDegree (biclique d) = d ∧
    lineDomination (biclique d) = d ∧ minMaximalMatching (biclique d) = d := by
  haveI := Fin.pos_iff_nonempty.mp hd
  have ht : TriangleFree (biclique d) := by
    have h : ∀ a b c : Bool, a ≠ b → b ≠ c → ¬ c ≠ a := by decide
    exact fun a b c => h a.1 b.1 c.1
  have hn : 2 ≤ Fintype.card (Vertex d) := by simp [Vertex]; omega
  obtain ⟨lower,_⟩ := row1078 (biclique d) hn ⟨d,regular_biclique d⟩ ht
  have avg := average_regular (biclique d) (regular_biclique d)
  rw [avg] at lower
  have upper := lineDomination_le_matching (biclique d)
  rw [matching_exact] at upper
  exact ⟨ht,avg,le_antisymm upper (by exact_mod_cast lower),matching_exact d⟩

#print axioms degree_le_of_dominating
#print axioms minDegree_le_lineDomination
#print axioms lineDomination_le_matching
#print axioms row1078
#print axioms sharp
end TriangleMatching1078
