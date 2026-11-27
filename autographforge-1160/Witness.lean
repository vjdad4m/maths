import Criterion

namespace CubicBridges1160
open SimpleGraph Finset

/-- One common hub and three seven-vertex lobes. -/
abbrev Vertex := Option (Fin 3 × Fin 7)

/-- Subdivide edge 1--4 of K₃,₃ by vertex 0. -/
def edges : List (Fin 7 × Fin 7) :=
  [(0,1),(0,4),(1,5),(1,6),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6)]

def inside (u v : Fin 7) := (u,v) ∈ edges ∨ (v,u) ∈ edges
instance (u v : Fin 7) : Decidable (inside u v) := inferInstanceAs (Decidable (_ ∨ _))

def adjacent : Vertex → Vertex → Prop
  | none, none => False
  | none, some (_,v) => v = 0
  | some (_,u), none => u = 0
  | some (i,u), some (j,v) => i=j ∧ inside u v

instance : DecidableRel adjacent := by
  intro x y
  cases x <;> cases y <;> dsimp [adjacent] <;> infer_instance

def graph : SimpleGraph Vertex where
  Adj := adjacent
  symm := by
    have h : ∀ x y, adjacent x y → adjacent y x := by decide
    intro x y hxy
    exact h x y hxy
  loopless := by
    change ∀ x, ¬ adjacent x x
    decide

instance : DecidableRel graph.Adj := inferInstanceAs (DecidableRel adjacent)

theorem order : Fintype.card Vertex = 22 := by decide

theorem cubic : graph.IsRegularOfDegree 3 := by
  have h : ∀ x, (graph.neighborFinset x).card = 3 := by decide
  exact h

set_option maxRecDepth 8192 in
theorem no_triangle : TriangleFree graph := by unfold TriangleFree; decide

theorem connected : graph.Connected := by
  have short : ∀ u : Fin 7, u=0 ∨ inside u 0 ∨ ∃ z, inside u z ∧ inside z 0 := by decide
  have reach (x : Vertex) : graph.Reachable x none := by
    rcases x with _|⟨i,u⟩
    · exact Reachable.rfl
    have finish : graph.Adj (some (i,0)) none := rfl
    rcases short u with e|e|⟨z,uz,zz⟩
    · subst u; exact finish.reachable
    · exact (show graph.Adj (some (i,u)) (some (i,0)) from ⟨rfl,e⟩).reachable.trans finish.reachable
    · have a : graph.Adj (some (i,u)) (some (i,z)) := ⟨rfl,uz⟩
      have b : graph.Adj (some (i,z)) (some (i,0)) := ⟨rfl,zz⟩
      exact a.reachable.trans (b.reachable.trans finish.reachable)
  exact ⟨fun x y => (reach x).trans (reach y).symm⟩

/-- Pair 1 with 5, 2 with 6, and 3 with 4. The hub joins lobe 0's remaining class. -/
def palette : Vertex → Fin 3 × Fin 4
  | none => (0,0)
  | some (i,u) => (i, if u=0 then 0 else if u=1 ∨ u=5 then 1 else if u=2 ∨ u=6 then 2 else 3)

theorem cover_exact : cliqueCover graph = 12 := by
  have valid : ∀ x y, graphᶜ.Adj x y → palette x ≠ palette y := by decide
  let coloring : graphᶜ.Coloring (Fin 3 × Fin 4) := Coloring.mk palette (fun h => valid _ _ h)
  have upper : graphᶜ.Colorable 12 := by simpa [Fintype.card_prod] using coloring.colorable
  apply le_antisymm (Nat.sInf_le upper)
  classical
  obtain ⟨c⟩ := cover_attained graph
  let emb (i : Fin 3) (u : Fin 7) : Vertex := some (i,u)
  let colors (i : Fin 3) := univ.image (fun u => c (emb i u))
  have localBound (i : Fin 3) : 4 ≤ (colors i).card := by
    let fiber (k : Fin (cliqueCover graph)) := univ.filter (fun u => c (emb i u)=k)
    have count : 7 = ∑ k ∈ colors i, (fiber k).card :=
      card_eq_sum_card_fiberwise (s:=univ) (t:=colors i) (f:=fun u => c (emb i u))
        (fun u _ => mem_image.mpr ⟨u,mem_univ _,rfl⟩)
    have small (k) : (fiber k).card ≤ 2 := by
      apply le_trans _ (fiber_small graph no_triangle c k)
      apply card_le_card_of_injOn (emb i)
      · intro u hu
        exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hu).2⟩
      · intro u _ v _ eq
        exact (Prod.mk.inj (Option.some.inj eq)).2
    have cap := sum_le_sum (s:=colors i) (fun k _ => small k)
    rw [← count] at cap
    simp only [sum_const,smul_eq_mul] at cap
    omega
  have apart : (univ : Finset (Fin 3)).toSet.PairwiseDisjoint colors := by
    intro i _ j _ ne
    apply disjoint_left.mpr
    intro k ki kj
    obtain ⟨u,_,eu⟩ := mem_image.mp ki
    obtain ⟨v,_,ev⟩ := mem_image.mp kj
    have different : emb i u ≠ emb j v := fun h => ne (Prod.mk.inj (Option.some.inj h)).1
    exact ne (adj_of_same graph c different (eu.trans ev.symm)).1
  calc
    12 = ∑ _ : Fin 3, (4:ℕ) := by decide
    _ ≤ ∑ i, (colors i).card := sum_le_sum (fun i _ => localBound i)
    _ = (univ.biUnion colors).card := (card_biUnion apart).symm
    _ ≤ cliqueCover graph := by simpa using card_le_univ (univ.biUnion colors)

theorem annihilation_exact : annihilation graph = 11 := by
  rw [regular_annihilation graph (by decide : 0<3) cubic,order]

/-- The numeric counterexample and the exact physical row's hypotheses. -/
theorem row1160_false : 1 < Fintype.card Vertex ∧ graph.IsRegularOfDegree 3 ∧
    TriangleFree graph ∧ graph.Connected ∧ ¬ cliqueCover graph ≤ annihilation graph := by
  exact ⟨by rw [order]; decide,cubic,no_triangle,connected,by rw [cover_exact,annihilation_exact]; decide⟩

theorem no_perfect_matching : ¬ ∃ M : graph.Subgraph, M.IsPerfectMatching :=
  fun h => row1160_false.2.2.2.2 ((regular_triangleFree_criterion graph (by decide : 0<3) cubic no_triangle).mpr h)

#print axioms connected
#print axioms cover_exact
#print axioms annihilation_exact
#print axioms no_perfect_matching
#print axioms row1160_false
end CubicBridges1160
