import OmissionFlanks
import TwoLayerTree
import PairedEntries

namespace Graffiti199Depleted.PathOn

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {z : V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]
variable (p : PathOn G {v | v ≠ z})

/-- The right endpoint together with the predecessors of the
omitted vertex's neighbors. -/
def terminalFlanks : Finset V := insert p.last p.predecessors

theorem terminalFlanks_card (noTrace : ¬ Catalogue.Traceable G) :
    p.terminalFlanks.card = G.degree z + 1 := by
  have off : p.last ∉ p.predecessors := by
    intro h
    obtain ⟨i,_,eq⟩ := p.mem_predecessors.mp h
    exact p.before_ne_last i eq
  rw [terminalFlanks,Finset.card_insert_of_not_mem off,p.predecessors_card noTrace]

omit [Fintype V] in
theorem omitted_off_terminalFlanks : z ∉ p.terminalFlanks := by
  intro mem
  rcases Finset.mem_insert.mp mem with eq|pred
  · exact p.last_mem eq.symm
  · obtain ⟨i,_,eq⟩ := p.mem_predecessors.mp pred
    exact ((p.covers (p.before i)).mp (p.before_mem i)) eq

omit [Fintype V] in
theorem no_edge_from_omitted_to_terminalFlanks (noTrace : ¬ Catalogue.Traceable G)
    (x : V) (mem : x ∈ p.terminalFlanks) : ¬ G.Adj z x := by
  rcases Finset.mem_insert.mp mem with rfl|pred
  · exact (omission_constraints noTrace p).lastOff
  · obtain ⟨i,hi,rfl⟩ := p.mem_predecessors.mp pred
    exact p.predecessor_not_neighbor noTrace i hi

omit [Fintype V] in
theorem terminalFlanks_independent (noTrace : ¬ Catalogue.Traceable G) :
    ∀ x ∈ p.terminalFlanks, ∀ y ∈ p.terminalFlanks, ¬ G.Adj x y := by
  intro x hx y hy
  rcases Finset.mem_insert.mp hx with rfl|xP <;> rcases Finset.mem_insert.mp hy with rfl|yP
  · exact G.loopless _
  · obtain ⟨i,h,rfl⟩ := p.mem_predecessors.mp yP
    exact p.terminal_not_adj_predecessor noTrace i h
  · obtain ⟨i,h,rfl⟩ := p.mem_predecessors.mp xP
    exact fun e => p.terminal_not_adj_predecessor noTrace i h e.symm
  · obtain ⟨i,hi,rfl⟩ := p.mem_predecessors.mp xP
    obtain ⟨j,hj,rfl⟩ := p.mem_predecessors.mp yP
    exact p.predecessors_nonadjacent noTrace i j hi hj

/-- The omitted vertex and the terminal flanks give an independent
set of order two more than the omitted degree. -/
theorem omitted_and_terminalFlanks_independent (noTrace : ¬ Catalogue.Traceable G) :
    (insert z p.terminalFlanks).card = G.degree z + 2 ∧
    ∀ x ∈ insert z p.terminalFlanks, ∀ y ∈ insert z p.terminalFlanks, ¬ G.Adj x y := by
  constructor
  · rw [Finset.card_insert_of_not_mem p.omitted_off_terminalFlanks,p.terminalFlanks_card noTrace]
  · intro x hx y hy
    rcases Finset.mem_insert.mp hx with rfl|xW <;> rcases Finset.mem_insert.mp hy with rfl|yW
    · exact G.loopless _
    · exact p.no_edge_from_omitted_to_terminalFlanks noTrace y yW
    · exact fun e => p.no_edge_from_omitted_to_terminalFlanks noTrace x xW e.symm
    · exact p.terminalFlanks_independent noTrace x xW y yW

noncomputable def uniqueAttachments (A : Finset V) : Finset V := by
  classical
  exact p.terminalFlanks.filter fun x => ∃! y, y ∈ A ∧ G.Adj x y

omit [Fintype V] in
theorem mem_uniqueAttachments (A : Finset V) (x : V) :
    x ∈ p.uniqueAttachments A ↔ x ∈ p.terminalFlanks ∧ ∃! y, y ∈ A ∧ G.Adj x y := by
  classical
  simp only [uniqueAttachments,Finset.mem_filter]

/-- Every independent subset of the omitted neighborhood limits the
number of terminal flanks with a unique attachment to it. -/
theorem unique_attachment_bound (noTrace : ¬ Catalogue.Traceable G)
    (budget : Catalogue.treeNumber G ≤ 5) (A : Finset V)
    (sub : A ⊆ G.neighborFinset z) (ind : ∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b) :
    A.card + (p.uniqueAttachments A).card ≤ 4 := by
  let B := p.uniqueAttachments A
  have hW (x : V) (hx : x ∈ B) : x ∈ p.terminalFlanks :=
    ((p.mem_uniqueAttachments A x).mp hx).1
  have tree := Catalogue.two_layer_tree_bound (G := G) z A B
    (fun h => p.omitted_off_terminalFlanks (hW z h))
    (fun a ha => (G.mem_neighborFinset _ _).mp (sub ha))
    (fun b hb => p.no_edge_from_omitted_to_terminalFlanks noTrace b (hW b hb))
    ind
    (fun a ha b hb => p.terminalFlanks_independent noTrace a (hW a ha) b (hW b hb))
    (fun x hx => ((p.mem_uniqueAttachments A x).mp hx).2)
  change A.card + B.card ≤ 4
  omega

omit [Fintype V] in
private theorem unique_pair_iff {a b x : V} (distinct : a ≠ b) :
    (∃! y, y ∈ ({a,b} : Finset V) ∧ G.Adj x y) ↔ ¬ (G.Adj x a ↔ G.Adj x b) := by
  constructor
  · rintro ⟨y,⟨ym,adj⟩,unique⟩ same
    have choose : y = a ∨ y = b := by simpa using ym
    have both : G.Adj x a ∧ G.Adj x b := by
      rcases choose with rfl|rfl
      · exact ⟨adj,same.mp adj⟩
      · exact ⟨same.mpr adj,adj⟩
    exact distinct ((unique a ⟨by simp,both.1⟩).trans (unique b ⟨by simp,both.2⟩).symm)
  · intro h
    by_cases aEdge : G.Adj x a
    · have bOff : ¬ G.Adj x b := fun bEdge => h (iff_of_true aEdge bEdge)
      refine ⟨a,⟨by simp,aEdge⟩,?_⟩
      rintro y ⟨mem,edge⟩
      rcases (show y = a ∨ y = b by simpa using mem) with eq|rfl
      · exact eq
      · exact (bOff edge).elim
    · have bEdge : G.Adj x b := Classical.byContradiction fun bOff =>
        h (iff_of_false aEdge bOff)
      refine ⟨b,⟨by simp,bEdge⟩,?_⟩
      rintro y ⟨mem,edge⟩
      rcases (show y = a ∨ y = b by simpa using mem) with rfl|eq
      · exact (aEdge edge).elim
      · exact eq

/-- On two nonadjacent neighbors of the omission, at most two
terminal flanks have unequal contacts. -/
theorem neighbor_pair_difference_bound (noTrace : ¬ Catalogue.Traceable G)
    (budget : Catalogue.treeNumber G ≤ 5) {a b : V}
    (distinct : a ≠ b) (za : G.Adj z a) (zb : G.Adj z b) (ab : ¬ G.Adj a b) :
    (p.terminalFlanks.filter (fun x => ¬ (G.Adj x a ↔ G.Adj x b))).card ≤ 2 := by
  classical
  let A : Finset V := {a,b}
  have size : A.card = 2 := Finset.card_pair distinct
  have sub : A ⊆ G.neighborFinset z := by
    intro x hx
    apply (G.mem_neighborFinset _ _).mpr
    rcases (show x = a ∨ x = b by simpa [A] using hx) with rfl|rfl
    · exact za
    · exact zb
  have ind (x : V) (hx : x ∈ A) (y : V) (hy : y ∈ A) : ¬ G.Adj x y := by
    rcases (show x = a ∨ x = b by simpa [A] using hx) with xa|xb <;>
      rcases (show y = a ∨ y = b by simpa [A] using hy) with ya|yb <;> subst x <;> subst y
    · exact G.loopless a
    · exact ab
    · exact fun e => ab e.symm
    · exact G.loopless b
  have limit := p.unique_attachment_bound noTrace budget A sub ind
  have rest : p.terminalFlanks.filter (fun x => ¬ (G.Adj x a ↔ G.Adj x b)) =
      p.uniqueAttachments A := by
    ext x
    simp only [Finset.mem_filter,p.mem_uniqueAttachments,A,unique_pair_iff distinct]
  rw [rest]
  omega

/-- If two flanks have unequal contacts to the pair, all other
terminal flanks have equal contacts to it. -/
theorem remaining_flank_agrees (noTrace : ¬ Catalogue.Traceable G)
    (budget : Catalogue.treeNumber G ≤ 5) {a b u v x : V}
    (distinct : a ≠ b) (za : G.Adj z a) (zb : G.Adj z b) (ab : ¬ G.Adj a b)
    (uW : u ∈ p.terminalFlanks) (vW : v ∈ p.terminalFlanks) (xW : x ∈ p.terminalFlanks)
    (uv : u ≠ v) (ux : u ≠ x) (vx : v ≠ x)
    (diffU : ¬ (G.Adj u a ↔ G.Adj u b)) (diffV : ¬ (G.Adj v a ↔ G.Adj v b)) :
    G.Adj x a ↔ G.Adj x b := by
  by_contra h
  let F := p.terminalFlanks.filter (fun y => ¬ (G.Adj y a ↔ G.Adj y b))
  have cap : F.card ≤ 2 := p.neighbor_pair_difference_bound noTrace budget distinct za zb ab
  have tooMany : 2 < F.card := Finset.two_lt_card.mpr
    ⟨u,Finset.mem_filter.mpr ⟨uW,diffU⟩,v,Finset.mem_filter.mpr ⟨vW,diffV⟩,
      x,Finset.mem_filter.mpr ⟨xW,h⟩,uv,ux,vx⟩
  omega

/-- For two nonadjacent neighbors of a cubic omission, at least two
of the four terminal flanks see both of those neighbors or neither. -/
theorem two_flanks_agree_on_neighbor_pair (noTrace : ¬ Catalogue.Traceable G)
    (budget : Catalogue.treeNumber G ≤ 5) (cubic : G.degree z = 3) {a b : V}
    (distinct : a ≠ b) (za : G.Adj z a) (zb : G.Adj z b) (ab : ¬ G.Adj a b) :
    ∃ x ∈ p.terminalFlanks, ∃ y ∈ p.terminalFlanks, x ≠ y ∧
      (G.Adj x a ↔ G.Adj x b) ∧ (G.Adj y a ↔ G.Adj y b) := by
  classical
  let same (x : V) := G.Adj x a ↔ G.Adj x b
  let S := p.terminalFlanks.filter same
  have bound : (p.terminalFlanks.filter (fun x => ¬ same x)).card ≤ 2 :=
    p.neighbor_pair_difference_bound noTrace budget distinct za zb ab
  have tally : S.card + (p.terminalFlanks.filter (fun x => ¬ same x)).card =
      p.terminalFlanks.card := Finset.filter_card_add_filter_neg_card_eq_card same
  have four := (p.terminalFlanks_card noTrace).trans (by rw [cubic])
  obtain ⟨x,hx,y,hy,ne⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
  have X := Finset.mem_filter.mp hx
  have Y := Finset.mem_filter.mp hy
  exact ⟨x,X.1,y,Y.1,ne,X.2,Y.2⟩

#print axioms omitted_and_terminalFlanks_independent
#print axioms unique_attachment_bound
#print axioms two_flanks_agree_on_neighbor_pair

end Graffiti199Depleted.PathOn
