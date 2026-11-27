import Structure

namespace Hereditary105
open Finset SimpleGraph AutoGraphPowerBurning CographRadius

/-- The path and cycle on the same four labeled vertices, selected by the closing edge. -/
def edges (close : Bool) (i j : Fin 4) :=
  if close then TriangleChain.consecutive i j else Graffiti137.Consecutive i j

instance (close : Bool) : DecidableRel (edges close) := by
  intro i j
  cases close <;> dsimp [edges,TriangleChain.consecutive,Graffiti137.Consecutive] <;> infer_instance

def four (close : Bool) : SimpleGraph (Fin 4) where
  Adj := edges close
  symm := (by decide : ∀ t, ∀ i j, edges t i j → edges t j i) close
  loopless := (by decide : ∀ t, ∀ i, ¬edges t i i) close

instance (close : Bool) : DecidableRel (four close).Adj := inferInstanceAs (DecidableRel (edges close))

theorem four_optima (close : Bool) : domination (four close) = 2 ∧ power (four close) = 1 := by
  let H := four close
  let pair : Finset (Fin 4) := {1,2}
  have dom : Dominates H pair :=
    (by decide : ∀ t : Bool, ∀ v : Fin 4, v ∈ ({1,2} : Finset (Fin 4)) ∨
      ∃ u ∈ ({1,2} : Finset (Fin 4)), (four t).Adj v u) close
  have hi : domination H ≤ pair.card := Nat.sInf_le
    (s:={r | ∃ S : Finset (Fin 4), S.card=r ∧ Dominates H S}) ⟨pair,rfl,dom⟩
  have sc : pair.card = 2 := by decide
  obtain ⟨S,sz,hit⟩ := dom_attained H
  have lo : 2 ≤ S.card := by
    by_contra! few
    obtain ⟨a,sub⟩ := card_le_one_iff_subset_singleton.mp (show S.card ≤ 1 by omega)
    obtain ⟨w,wa,miss⟩ := (by decide : ∀ t : Bool, ∀ a : Fin 4, ∃ w, w ≠ a ∧ ¬(four t).Adj w a) close a
    obtain hw|⟨v,hv,e⟩ := hit w
    · exact wa (mem_singleton.mp (sub hw))
    · exact miss (mem_singleton.mp (sub hv) ▸ e)
  have near (v : Fin 4) (ne : v ≠ 3) : Observed H {1} v := by
    by_cases atSeed : v = 1
    · exact .root (mem_singleton.mpr atSeed)
    · exact .neighbor (mem_singleton_self 1)
        ((by decide : ∀ t : Bool, ∀ v : Fin 4, v ≠ 3 → v ≠ 1 → (four t).Adj v 1) close v ne atSeed)
  have allSeen : ∀ v, Observed H {1} v := by
    intro v
    by_cases ne : v = 3
    · subst v
      exact .force ((by decide : ∀ t : Bool, (four t).Adj 3 2) close)
        (near 2 (by decide)) (fun u _ n => near u n)
    · exact near v ne
  have phi : power H ≤ 1 := by simpa using power_le_card H allSeen
  letI : DecidableEq H.ConnectedComponent := Classical.decEq _
  letI := Fintype.ofSurjective H.connectedComponentMk (fun c => c.exists_rep)
  have pos : 0 < components H := Nat.card_pos
  have plo := components_le_power H
  change domination H = 2 ∧ power H = 1
  omega

/-- All finite induced subgraphs, represented by injections of a finite vertex list. -/
def HereditaryEquality {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (n : ℕ) (f : Fin n ↪ V), domination (G.comap f) = power (G.comap f)

theorem no_long_hole {V : Type*} (G : SimpleGraph V) (hp : Cograph G) (hc : SquareFree G) :
    TriangleChain.Chordal G := by
  intro k hk hole
  by_cases eq : k = 4
  · subst k; exact hc hole
  obtain ⟨f,rel⟩ := hole
  let g : Fin 4 ↪ Fin k := ⟨fun i => ⟨i.val,by omega⟩,fun a b e => Fin.ext (congrArg (fun v : Fin k => v.val) e)⟩
  apply hp
  refine ⟨g.trans f,fun i j => (rel (g i) (g j)).trans ?_⟩
  dsimp [g,TriangleChain.consecutive,Graffiti137.Consecutive]
  omega

/-- Testing the catalogue inequality just on injections of four vertices is sufficient. -/
theorem four_vertex_test {V : Type*} (G : SimpleGraph V) :
    (∀ f : Fin 4 ↪ V, domination (G.comap f) ≤ power (G.comap f)) ↔
      TriangleChain.Chordal G ∧ Cograph G := by
  constructor
  · intro test
    have avoid (t : Bool) (f : Fin 4 ↪ V) (e : ∀ i j, G.Adj (f i) (f j) ↔ (four t).Adj i j) : False := by
      have ident : G.comap f = four t := by ext i j; exact e i j
      have h := test f
      rw [ident] at h
      obtain ⟨a,b⟩ := four_optima t
      omega
    have hp : Cograph G := fun ⟨f,rel⟩ => avoid false f rel
    have hc : SquareFree G := fun ⟨f,rel⟩ => avoid true f rel
    exact ⟨no_long_hole G hp hc,hp⟩
  · rintro ⟨hc,hp⟩ f
    obtain ⟨a,b⟩ := exact (G.comap f) (cograph_restrict G f hp)
      (square_restrict G f (hc 4 (by decide)))
    exact (a.trans b.symm).le

/-- Hereditary equality of the two optimization problems characterizes trivially perfect graphs. -/
theorem characterization {V : Type*} (G : SimpleGraph V) :
    HereditaryEquality G ↔ TriangleChain.Chordal G ∧ Cograph G := by
  constructor
  · exact fun h => (four_vertex_test G).mp (fun f => (h 4 f).le)
  · rintro ⟨hc,hp⟩ n f
    obtain ⟨a,b⟩ := exact (G.comap f) (cograph_restrict G f hp)
      (square_restrict G f (hc 4 (by decide)))
    exact a.trans b.symm

/-- The exact values directly on the usual induced-subgraph API, including the empty set. -/
theorem on_induced {V : Type*} [Finite V] (G : SimpleGraph V)
    (chordal : TriangleChain.Chordal G) (cog : Cograph G) (s : Set V) :
    domination (G.induce s) = components (G.induce s) ∧
      power (G.induce s) = components (G.induce s) := by
  classical
  letI : Fintype s := Fintype.ofFinite _
  let f := Function.Embedding.subtype (· ∈ s)
  exact Hereditary105.exact _ (cograph_restrict G f cog)
    (square_restrict G f (chordal 4 (by decide)))

#print axioms four_optima
#print axioms four_vertex_test
#print axioms characterization
#print axioms on_induced
end Hereditary105
