import ForkTree180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Disjoint full stars, away from the root and its neighbors, fit in a
single spanning tree with the root internal. Distances are allowed to
change in this construction. -/
theorem packed_stars (G H : SimpleGraph V) (gc : G.Connected) (hc : H.Connected) (hg : H≤G)
    (r s t : V) (rs : H.Adj r s) (rt : H.Adj r t) (st : s≠t) (C : Finset V)
    (deep : ∀ c∈C,3≤G.dist c r) (sep : ∀ c∈C,∀ d∈C,c≠d → 3≤G.dist c d) :
    ∃ T≤H,T.IsTree ∧ r∉leaves T ∧ ∀ c∈C,∀ x,H.Adj c x → T.Adj c x := by
  classical
  let L := C.biUnion (fun x => H.neighborFinset x)
  have adjL (x : V) (xl : x∈L) : ∃ c∈C,H.Adj c x := by
    obtain ⟨c,cm,cx⟩ := mem_biUnion.mp xl
    exact ⟨c,cm,(H.mem_neighborFinset c x).mp cx⟩
  let f (x : V) := if h : x∈L then (adjL x h).choose else r
  have spec (x : V) (xl : x∈L) : f x∈C ∧ H.Adj (f x) x := by
    simpa [f,xl] using (adjL x xl).choose_spec
  have only (x c d : V) (cm : c∈C) (dm : d∈C) (cx : H.Adj c x) (dx : H.Adj d x) : c=d := by
    by_contra ne
    have apart := sep c cm d dm ne
    have tri := gc.dist_triangle (u:=c) (v:=x) (w:=d)
    rw [dist_eq_one_iff_adj.mpr (hg cx),dist_eq_one_iff_adj.mpr (hg dx.symm)] at tri
    omega
  have dis : Disjoint C L := disjoint_left.mpr (by
    intro x xc xl
    obtain ⟨c,cm,cx⟩ := adjL x xl
    have low := dist_eq_one_iff_adj.mpr (hg cx)
    have high := sep c cm x xc cx.ne
    omega)
  have far (x : V) (lo : G.dist x r≤1) : x∉C∪L := by
    intro mem
    rcases mem_union.mp mem with xc|xl
    · have := deep x xc; omega
    · obtain ⟨c,cm,cx⟩ := adjL x xl
      have tri := gc.dist_triangle (u:=c) (v:=x) (w:=r)
      rw [dist_eq_one_iff_adj.mpr (hg cx)] at tri
      have := deep c cm
      omega
  have free : ∀ z∈({r,r,s,t}:Finset V),z∉C∪L := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with eq|eq|eq|eq <;> subst z <;> apply far
    · simp [dist_self]
    · simp [dist_self]
    · rw [dist_eq_one_iff_adj.mpr (hg rs.symm)]
    · rw [dist_eq_one_iff_adj.mpr (hg rt.symm)]
  obtain ⟨T,sub,tr,nr,_,arm⟩ := fork_tree H hc r r s t C L f dis free rs rt st
    (fun x xl => ⟨(spec x xl).1,(spec x xl).2.symm⟩)
  refine ⟨T,sub,tr,nr,?_⟩
  intro c cm x cx
  have xl : x∈L := mem_biUnion.mpr ⟨c,cm,(H.mem_neighborFinset c x).mpr cx⟩
  have eq := only x (f x) c (spec x xl).1 cm (spec x xl).2 cx
  simpa only [eq] using (arm x xl).symm

/-- A distance-three packing of marked centers at distance at least three
from r has total vertical degree excess strictly below the transversal
number minus one in every failed rooted marking. -/
theorem packing_budget (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (two : ∃ s t,G.Adj r s ∧ G.Adj r t ∧ s≠t) (odd : Bool)
    (A : Finset V) (ai : Indep G A) (C : Finset V) :
    let P := parity G r odd
    let H := alternating G P
    C⊆A∪P → (∀ c∈C,3≤G.dist c r) → (∀ c∈C,∀ d∈C,c≠d → 3≤G.dist c d) →
    weightedLeaves G (eligible A P r)+bipartiteNum G<1+A.card+P.card →
    1+(∑ c∈C,(H.degree c-2))+bipartiteNum G<Fintype.card V := by
  classical
  intro P H cx deep sep bad
  obtain ⟨s,t,rs,rt,st⟩ := two
  obtain ⟨hc,star⟩ := alternating_parity G gc r odd
  have hg : H≤G := fun _ _ e => e.1
  obtain ⟨T,sub,tr,nr,full⟩ := packed_stars G H gc hc hg r s t (star s rs) (star t rt) st C deep sep
  have budget := marked_tree_budget G T gc hn r odd A ai (sub.trans hg) tr nr (fun e => (sub e).2) bad
  have same : (∑ c∈C,(H.degree c-2))=∑ c∈C,(T.degree c-2) := by
    apply sum_congr rfl
    intro c cm
    have eq : H.neighborFinset c=T.neighborFinset c := by
      ext x; simp only [mem_neighborFinset]; exact ⟨full c cm x,fun e => sub e⟩
    simp only [←card_neighborFinset_eq_degree,eq]
  have sm := sum_le_sum_of_subset_of_nonneg (f:=fun c => T.degree c-2) cx (fun _ _ _ => Nat.zero_le _)
  change (∑ c∈C,(T.degree c-2))≤∑ c∈A∪P,(T.degree c-2) at sm
  change 1+(∑ v∈A∪P,(T.degree v-2))+bipartiteNum G<Fintype.card V at budget
  omega

#print axioms packed_stars
#print axioms packing_budget
end Minimal180.HigherRank
