import FirstForm180
import TriangleDefect180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem flat_add_levels (J : SimpleGraph V) (jc : J.Connected) (r u v : V)
    (flat : J.dist u r=J.dist v r) : ∀ x, (J⊔SimpleGraph.edge u v).dist x r=J.dist x r := by
  let G := J⊔SimpleGraph.edge u v
  apply (layers G r (fun x => J.dist x r) J.dist_self _ _).2
  · intro a b e
    change J.dist a r ≤ J.dist b r + 1
    rcases e with j|h
    · have tri := jc.dist_triangle (u:=a) (v:=b) (w:=r)
      rw [dist_eq_one_iff_adj.mpr j] at tri
      omega
    · rcases ((edge_adj ..).mp h).1 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
  · intro x ne
    obtain ⟨z,e,d⟩ := Graffiti169.exists_predecessor J jc r x ne
    exact ⟨z,Or.inl e,d⟩

omit [DecidableEq V] in
theorem parity_add_flat (J : SimpleGraph V) (jc : J.Connected) (r u v : V)
    (flat : J.dist u r=J.dist v r) (odd : Bool) :
    parity (J⊔SimpleGraph.edge u v) r odd=parity J r odd := by
  ext x
  simp only [mem_parity,flat_add_levels J jc r u v flat]

/-- A lower rooted equality with full bipartite order and two root neighbors
forces the independent mark to be precisely the selected parity. -/
theorem full_tight_marks (J : SimpleGraph V) (jc : J.Connected) (hn : 1<Fintype.card V)
    (r : V) (odd : Bool) (A : Finset V) (ai : Indep J A)
    (two : ∃ s t, J.Adj r s ∧ J.Adj r t ∧ s≠t)
    (rank : bipartiteNum J=Fintype.card V)
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card) :
    A=parity J r odd := by
  classical
  let P := parity J r odd
  let p (v:V) := if h : v=r then r else (Graffiti169.exists_predecessor J jc r v h).choose
  have pred (x:V) (ne:x≠r) : J.Adj x (p x) ∧ J.dist x r=J.dist (p x) r+1 := by
    simpa only [p,dif_neg ne] using (Graffiti169.exists_predecessor J jc r x ne).choose_spec
  obtain ⟨T,sub,tr,cross,_,star⟩ := predecessor_tree J jc r odd p pred
  obtain ⟨s,t,rs,rt,st⟩ := two
  have intr : r∉leaves T := fun lf => st (leaf_unique T lf (star s rs) (star t rt))
  let D := (A∪P)\(A∩P)
  by_contra ne
  have nonempty : D.Nonempty := by
    by_contra! no
    apply ne
    ext x
    have out : x∉D := fun h => no ⟨x,h⟩
    change x∈A ↔ x∈P
    simp only [D,mem_sdiff,mem_union,mem_inter] at out
    tauto
  have forest := forest_strict T tr D nonempty
  have eqn := tree_defect T tr hn r intr A P (fun x hx y hy neq e => ai x hx y hy neq (sub e)) cross
  change Fintype.card V+_+(T.edgeFinset∩D.sym2).card=1+A.card+P.card+D.card+_ at eqn
  have cap := score_of_tree J T sub tr (eligible A P r)
  change weightedLeaves J (eligible A P r)+bipartiteNum J=1+A.card+P.card at tight
  omega

/-- Every rank-critical flat triangle with bipartite lower graph, lower
tightness and two root neighbors has a two-component certificate. -/
theorem bipartite_lower_first (J : SimpleGraph V) (jc : J.Connected) (hn : 2<Fintype.card V)
    (r u v w : V) (uv : u≠v) (old : ¬J.Adj u v) (uw : J.Adj u w) (wv : J.Adj w v)
    (flat : J.dist u r=J.dist v r) (two : ∃ s t, J.Adj r s ∧ J.Adj r t ∧ s≠t) (odd : Bool) (A : Finset V)
    (ai : Indep (J⊔SimpleGraph.edge u v) A) (full : bipartiteNum J=Fintype.card V)
    (drop : bipartiteNum J=bipartiteNum (J⊔SimpleGraph.edge u v)+1)
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card) :
    FirstForm J (eligible A (parity J r odd) r) u v w := by
  let G := J⊔SimpleGraph.edge u v
  let P := parity J r odd
  obtain ⟨s,t,rs,rt,st⟩ := two
  have bound := rank_one_rooted G (jc.mono le_sup_left) (by omega) r
    ⟨s,t,Or.inl rs,Or.inl rt,st⟩ (by change Fintype.card V≤bipartiteNum (J⊔SimpleGraph.edge u v)+1; omega) odd A ai
  have par := parity_add_flat J jc r u v flat odd
  change parity G r odd=P at par
  change 1+A.card+(parity G r odd).card≤weightedLeaves G (eligible A (parity G r odd) r)+bipartiteNum G at bound
  rw [par] at bound
  have same : A=P := full_tight_marks J jc (by omega) r odd A
    (fun x hx y hy neq e => ai x hx y hy neq (Or.inl e)) ⟨s,t,rs,rt,st⟩ full tight
  have edge : G.Adj u v := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,uv⟩)
  have pp : u∈P ↔ v∈P := by simp only [P,mem_parity,flat]
  have nu : u∉P := fun h => ai u (same ▸ h) v (same ▸ pp.mp h) uv edge
  have nv : v∉P := fun h => nu (pp.mpr h)
  change weightedLeaves J (eligible A P r)+bipartiteNum J=1+A.card+P.card at tight
  change bipartiteNum J=bipartiteNum G+1 at drop
  apply first_of_supported_tips J jc hn u v w uv old uw wv _ _ (by change weightedLeaves J (eligible A P r)<weightedLeaves G (eligible A P r); omega)
  intro x xt xu
  have xp : x∈P := (eligible_iff.mp xu).1.elim (fun xa => same ▸ xa) id
  rcases (show x=u ∨ x=v by simpa using xt) with rfl|rfl
  · exact (nu xp).elim
  · exact (nv xp).elim

/-- At arbitrary rank, an equally large independent replacement supported on
the selected parity pays for a gain with both endpoint weights erased. -/
theorem first_of_confined_replacement (J : SimpleGraph V) (jc : J.Connected) (hn : 2<Fintype.card V)
    (r u v w : V) (uv : u≠v) (old : ¬J.Adj u v) (uw : J.Adj u w) (wv : J.Adj w v)
    (flat : J.dist u r=J.dist v r) (odd : Bool) (A I : Finset V)
    (ii : Indep (J⊔SimpleGraph.edge u v) I) (sub : I⊆parity J r odd) (sz : A.card≤I.card)
    (keep : eligible I (parity J r odd) r⊆(eligible A (parity J r odd) r)\{u,v})
    (drop : bipartiteNum J=bipartiteNum (J⊔SimpleGraph.edge u v)+1)
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card) :
    FirstForm J (eligible A (parity J r odd) r) u v w := by
  classical
  let G := J⊔SimpleGraph.edge u v
  let P := parity J r odd
  have par := parity_add_flat J jc r u v flat odd
  change parity G r odd=P at par
  have a := confined_parity G (jc.mono le_sup_left) (by omega) r odd.toNat I ii (show I⊆parity G r odd by rwa [par])
  change 1+I.card+(parity G r odd).card≤weightedLeaves G (eligible I (parity G r odd) r)+markedBip G (I∩parity G r odd) at a
  rw [par] at a
  have b : markedBip G (I∩P)≤bipartiteNum G := by
    apply Finset.sup_le
    intro S h
    exact size_bip G (mem_filter.mp h).2.2
  have c := eligible_mono G keep
  change weightedLeaves G (eligible I P r)≤weightedLeaves G ((eligible A P r)\{u,v}) at c
  change weightedLeaves J (eligible A P r)+bipartiteNum J=1+A.card+P.card at tight
  change bipartiteNum J=bipartiteNum G+1 at drop
  apply (first_iff_erased_gain J jc hn u v w uv old uw wv _).mpr
  change weightedLeaves J (eligible A P r)<weightedLeaves G ((eligible A P r)\{u,v})
  omega

/-- In the confined case, any crossing common neighbor forces both ends to
be ineligible: the upper bound gives a gain, and every winning set contains
that common neighbor. This gives the two-component repair at every rank. -/
theorem confined_crossing_first (J : SimpleGraph V) (jc : J.Connected) (hn : 2<Fintype.card V)
    (r u v w : V) (uv : u≠v) (old : ¬J.Adj u v) (flat : J.dist u r=J.dist v r)
    (odd : Bool) (A : Finset V) (ai : Indep (J⊔SimpleGraph.edge u v) A) (ap : A⊆parity J r odd)
    (uw : (alternating J (parity J r odd)).Adj u w) (vw : (alternating J (parity J r odd)).Adj v w)
    (drop : bipartiteNum J=bipartiteNum (J⊔SimpleGraph.edge u v)+1)
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card) :
    FirstForm J (eligible A (parity J r odd) r) u v w := by
  classical
  let G := J⊔SimpleGraph.edge u v
  let P := parity J r odd
  let U := eligible A P r
  have par := parity_add_flat J jc r u v flat odd
  change parity G r odd=P at par
  have bound := confined_parity G (jc.mono le_sup_left) (by omega) r odd.toNat A ai (show A⊆parity G r odd by rwa [par])
  change 1+A.card+(parity G r odd).card≤weightedLeaves G (eligible A (parity G r odd) r)+markedBip G (A∩parity G r odd) at bound
  rw [par] at bound
  have cap : markedBip G (A∩P)≤bipartiteNum G := by
    apply Finset.sup_le
    intro S h
    exact size_bip G (mem_filter.mp h).2.2
  change weightedLeaves J U+bipartiteNum J=1+A.card+P.card at tight
  change bipartiteNum J=bipartiteNum G+1 at drop
  change 1+A.card+P.card≤weightedLeaves G U+_ at bound
  have gain : weightedLeaves J U<weightedLeaves G U := by omega
  obtain ⟨C,cu,middle,_,_⟩ := (triangle_gain_iff_core J jc hn u v w uv old uw.1 vw.1.symm U).mp gain
  have only (z:V) (h:z∈U) : z∈P := (eligible_iff.mp h).1.elim (fun a => ap a) id
  have wp := only w (cu middle)
  apply first_of_supported_tips J jc hn u v w uv old uw.1 vw.1.symm U _ gain
  intro x xt xu
  rcases (show x=u ∨ x=v by simpa using xt) with rfl|rfl
  · exact (uw.2.mp (only x xu) wp).elim
  · exact (vw.2.mp (only x xu) wp).elim

#print axioms confined_crossing_first
#print axioms full_tight_marks
#print axioms bipartite_lower_first
#print axioms first_of_confined_replacement
end Minimal180
