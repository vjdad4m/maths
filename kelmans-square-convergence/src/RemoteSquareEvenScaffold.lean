import RemoteSquareConvergence
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace KelmansCactus.AtomicBridge.RemoteSquareEvenScaffold
open SimpleGraph
open scoped Sym2
open RemoteSquareConvergence
variable {V I : Type*} [Fintype V]

/-- In a finite graph of even degrees there is an alternate walk for every edge.
Delete an alleged bridge and restrict to one side; its endpoint becomes the
unique odd-degree vertex, contradicting the handshaking lemma. -/
theorem even_degree_alternate (G : SimpleGraph V) [DecidableRel G.Adj]
    (degreeEven : ∀ x, Even (G.degree x)) {a b : V} (ab : G.Adj a b) :
    (G.deleteEdges {s(a,b)}).Reachable a b := by
  classical
  by_contra non
  let D := G.deleteEdges {s(a,b)}
  let S : Set V := {x | D.Reachable a x}
  let a' : S := ⟨a,SimpleGraph.Reachable.refl _⟩
  letI : DecidablePred (· ∈ S) := Classical.decPred _
  have delA : D.neighborFinset a = (G.neighborFinset a).erase b := by
    ext x
    simp only [D,SimpleGraph.mem_neighborFinset,SimpleGraph.deleteEdges_adj,
      Set.mem_singleton_iff,Finset.mem_erase,Sym2.eq_iff,true_and]
    constructor
    · rintro ⟨e,ne⟩
      exact ⟨fun h=>ne (Or.inl h),e⟩
    · rintro ⟨ne,e⟩
      exact ⟨e,fun h=>h.elim ne (fun h=>(G.ne_of_adj ab) h.1)⟩
  have da : D.degree a = G.degree a - 1 := by
    rw [←SimpleGraph.card_neighborFinset_eq_degree,delA,
      Finset.card_erase_of_mem ((SimpleGraph.mem_neighborFinset G a b).mpr ab),
      SimpleGraph.card_neighborFinset_eq_degree]
  have daOdd : Odd (D.degree a) := by
    have pos : 0 < G.degree a :=
      Finset.card_pos.mpr ⟨b,(SimpleGraph.mem_neighborFinset G a b).mpr ab⟩
    obtain ⟨k,eq⟩ := degreeEven a
    exact ⟨k-1,by omega⟩
  have induced_deg (x : S) : (D.induce S).degree x = D.degree x := by
    apply D.degree_induce_of_neighborSet_subset
    intro y e
    exact x.property.trans ((SimpleGraph.mem_neighborSet _ _ _).mp e).reachable
  rw [← induced_deg a'] at daOdd
  obtain ⟨u,une,uodd⟩ := (D.induce S).exists_ne_odd_degree_of_exists_odd_degree a' daOdd
  have ua : u.val ≠ a := fun e => une (Subtype.ext e)
  have ub : u.val ≠ b := by
    intro e
    have h : D.Reachable a u.val := u.property
    rw [e] at h
    exact non h
  have other : D.neighborFinset u.val = G.neighborFinset u.val := by
    ext x
    simp only [D,SimpleGraph.mem_neighborFinset,SimpleGraph.deleteEdges_adj,Set.mem_singleton_iff,
      Sym2.eq_iff]
    exact ⟨And.left,fun h => ⟨h,fun p=>p.elim (fun e=>ua e.1) (fun e=>ub e.1)⟩⟩
  rw [induced_deg,←SimpleGraph.card_neighborFinset_eq_degree,other,
    SimpleGraph.card_neighborFinset_eq_degree] at uodd
  exact (Nat.not_even_iff_odd.mpr uodd) (degreeEven u.val)

omit [Fintype V] in
theorem alternate_mono {X Y : SimpleGraph V} (sub : X≤Y) {a b : V}
    (r : (X.deleteEdges {s(a,b)}).Reachable a b) :
    (Y.deleteEdges {s(a,b)}).Reachable a b := by
  apply r.mono
  intro u v e
  exact SimpleGraph.deleteEdges_adj.mpr ⟨sub (SimpleGraph.deleteEdges_adj.mp e).1,
    (SimpleGraph.deleteEdges_adj.mp e).2⟩

/-- The actual square edges may be contained in different even-degree supporting
subgraphs, chosen independently for each present edge and state. -/
theorem convergence_of_even_scaffolds [DecidableEq I]
    (B : SimpleGraph V) (gates : I→Quad V)
    (evenSupport : ∀ s i, let q := (gates i).orient (s i)
      ∀ x y, pair q.a q.b x y ∨ pair q.c q.d x y →
        ∃ (E : SimpleGraph V) (_ : DecidableRel E.Adj),
          E ≤ network B gates s ∧ (∀ z, Even (E.degree z)) ∧ E.Adj x y)
    (start : I→Bool) :
    ∃ final,
      Relation.ReflTransGen (fun s t=> ∃ i, t=RemoteSquareConvergence.flip s i ∧
        ¬(network B gates s).Reachable ((gates i).orient (s i)).a ((gates i).orient (s i)).c)
        start final ∧
      ∀ x y, (network B gates final).Reachable x y ↔ (unionNetwork B gates).Reachable x y := by
  apply square_convergence B gates _ start
  apply bypass_of_alternate
  intro s i
  let q := (gates i).orient (s i)
  have h (x y : V) (e : pair q.a q.b x y ∨ pair q.c q.d x y) :
      ((network B gates s).deleteEdges {s(x,y)}).Reachable x y := by
    obtain ⟨E,inst,sub,even,adj⟩ := evenSupport s i x y e
    letI := inst
    exact alternate_mono sub (even_degree_alternate E even adj)
  exact ⟨h q.a q.b (Or.inl (Or.inl ⟨rfl,rfl⟩)),h q.c q.d (Or.inr (Or.inl ⟨rfl,rfl⟩))⟩

#print axioms even_degree_alternate
#print axioms convergence_of_even_scaffolds
end KelmansCactus.AtomicBridge.RemoteSquareEvenScaffold
