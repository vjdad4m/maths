import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.List.Chain

namespace Graffiti199Depleted

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A nonempty simple path that visits exactly the given set. -/
structure PathOn (G : SimpleGraph V) (U : Set V) where
  vertices : List V
  nonempty : vertices ≠ []
  chain : vertices.Chain' G.Adj
  nodup : vertices.Nodup
  covers : ∀ v, v ∈ vertices ↔ v ∈ U

def PathOn.first {U : Set V} (p : PathOn G U) : V := p.vertices.head p.nonempty

def PathOn.last {U : Set V} (p : PathOn G U) : V := p.vertices.getLast p.nonempty

theorem PathOn.last_mem {U : Set V} (p : PathOn G U) : p.last ∈ U :=
  (p.covers p.last).mp (List.getLast_mem _)

/-- Join two spanning paths through an edge between their endpoints. -/
def PathOn.join {U W : Set V} (p : PathOn G U) (q : PathOn G W)
    (dis : Disjoint U W) (edge : G.Adj p.last q.first) : PathOn G (U ∪ W) := by
  refine ⟨p.vertices ++ q.vertices, ?_, ?_, ?_, ?_⟩
  · exact fun h => p.nonempty (List.append_eq_nil_iff.mp h).1
  · apply p.chain.append q.chain
    intro a ha b hb
    have aEq : a = p.last := by
      obtain ⟨_, h⟩ := List.mem_getLast?_eq_getLast ha
      exact h
    have bEq : b = q.first := by
      rw [List.head?_eq_head q.nonempty] at hb
      exact (Option.mem_some.mp hb).symm
    simpa only [aEq,bEq] using edge
  · exact List.nodup_append.mpr ⟨p.nodup,q.nodup,fun v vp vq =>
      Set.disjoint_left.mp dis ((p.covers v).mp vp) ((q.covers v).mp vq)⟩
  · intro v
    simp only [List.mem_append,p.covers,q.covers,Set.mem_union]

/-- A list certificate lifts along any injective labelling into the graph. -/
def liftLabelPath {ι : Type*} (f : ι ↪ V) {P : ι → Prop} (xs : List ι)
    (ne : xs ≠ []) (nd : xs.Nodup) (chain : xs.Chain' (fun a b => G.Adj (f a) (f b)))
    (cover : ∀ i, i ∈ xs ↔ P i) : PathOn G {v | ∃ i, P i ∧ f i = v} :=
  ⟨xs.map f,by simpa using ne,(List.chain'_map _).mpr chain,nd.map f.injective,fun _ => by
    simp only [List.mem_map,Set.mem_setOf_eq,cover]⟩

/-- Every walk from the inside to the outside provides a crossing edge. -/
theorem crossingOnWalk {U : Set V} {x y : V} (w : G.Walk x y) :
    x ∈ U → y ∉ U → ∃ a ∈ U, ∃ b ∉ U, G.Adj a b := by
  induction w with
  | nil => exact fun i o => (o i).elim
  | @cons x y z xy w ih =>
    intro hx hz
    by_cases hy : y ∈ U
    · exact ih hy hz
    · exact ⟨x,hx,y,hy,xy⟩

/-- The edge-to-edge reachability property used for the small cut in the
remaining counterexample. A surviving isolated vertex need not be reachable. -/
def EdgeReachAfterSmallDeletion (G : SimpleGraph V) : Prop :=
  ∀ (D : Finset V), D.card ≤ 3 →
    ∀ (a b c d : {v : V // v ∉ D}), G.Adj a.val b.val → G.Adj c.val d.val →
      (G.induce {v | v ∉ D}).Reachable a c

theorem crossingAfterSmallDeletion
    (reach : EdgeReachAfterSmallDeletion G) {D : Finset V} (small : D.card ≤ 3)
    {U : Set V} {a b c d : V} (au : a ∈ U) (cu : c ∉ U)
    (aD : a ∉ D) (bD : b ∉ D) (cD : c ∉ D) (dD : d ∉ D)
    (ab : G.Adj a b) (cd : G.Adj c d) :
    ∃ x ∈ U, ∃ y ∉ U, x ∉ D ∧ y ∉ D ∧ G.Adj x y := by
  obtain ⟨w⟩ := reach D small ⟨a,aD⟩ ⟨b,bD⟩ ⟨c,cD⟩ ⟨d,dD⟩ ab cd
  let W : Set {v : V // v ∉ D} := {v | v.val ∈ U}
  obtain ⟨x,hx,y,hy,xy⟩ := crossingOnWalk (U := W) w au cu
  exact ⟨x.val,hx,y.val,hy,x.property,y.property,xy⟩

#print axioms crossingAfterSmallDeletion

end Graffiti199Depleted
