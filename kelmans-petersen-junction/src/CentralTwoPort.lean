import Substitute

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open Substitute
set_option maxHeartbeats 5500000

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

private theorem boundary_tile {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) (ac : a≠c) :
    Closed G ({a,b,c}:Finset V) := by
  have h : ({a,b,c}:Finset V).card=3 := by simp [ab.ne,bc.ne,ac]
  exact tile_closed ⟨h,(Kelmans.tile_iff_path G _ h).mpr
    ⟨a,b,c,ab.ne,ac,bc.ne,ab,bc,rfl⟩⟩

/-- A centered cap root gives two distinct exported singletons; two
disjoint outside edges absorb them independently. The rest of both
shores is left unchanged. -/
theorem join_two_singletons_to_two_edges {A R : Finset V} {a b u v w z : V}
    (aA : a∈A) (bA : b∈A) (ab : a≠b)
    (UR : ({u,v}:Finset V)⊆R) (WR : ({w,z}:Finset V)⊆R)
    (split : Disjoint ({u,v}:Finset V) {w,z})
    (ar : Disjoint A R) (au : G.Adj a u) (uv : G.Adj u v)
    (bw : G.Adj b w) (wz : G.Adj w z)
    (atom : Closed G (A\{a,b}))
    (core : Closed G (R\({u,v} ∪ {w,z}))) : Closed G (A∪R) := by
  have notinside {q : V} (h : q∈R) : q∉A :=
    fun hq=>disjoint_left.mp ar hq h
  have av : a≠v := fun h=>notinside (UR (by simp)) (h ▸ aA)
  have bz : b≠z := fun h=>notinside (WR (by simp)) (h ▸ bA)
  have mix : Disjoint ({a,u,v}:Finset V) {b,w,z} := by
    apply disjoint_left.mpr
    intro q l r
    by_cases qa : q=a
    · subst q
      rcases mem_insert.mp r with aEq|aIn
      · exact ab aEq
      · exact notinside (WR aIn) aA
    · by_cases qb : q=b
      · subst q
        exact notinside (UR ((mem_insert.mp l).resolve_left qa)) bA
      · exact disjoint_left.mp split ((mem_insert.mp l).resolve_left qa)
          ((mem_insert.mp r).resolve_left qb)
  have t : Closed G (({a,u,v}:Finset V) ∪ {b,w,z}) :=
    add_closed (boundary_tile au uv av) (boundary_tile bw wz bz) mix
  have al : Disjoint (A\{a,b}) (R\({u,v} ∪ {w,z})) := ar.mono sdiff_subset sdiff_subset
  have rem : Closed G ((A\{a,b}) ∪ (R\({u,v} ∪ {w,z}))) := add_closed atom core al
  have d : Disjoint ((A\{a,b}) ∪ (R\({u,v} ∪ {w,z}))) ({a,u,v} ∪ {b,w,z}) := by
    apply disjoint_left.mpr
    intro q qrem qt
    have tcase : q=a ∨ q=b ∨ q∈({u,v} ∪ {w,z}:Finset V) := by
      simp only [mem_union,mem_insert,mem_singleton] at qt ⊢
      tauto
    rcases mem_union.mp qrem with qa|qr
    · rcases tcase with same|same|qR
      · exact (mem_sdiff.mp qa).2 (by simp [same])
      · exact (mem_sdiff.mp qa).2 (by simp [same])
      · exact disjoint_left.mp ar (mem_sdiff.mp qa).1 ((mem_union.mp qR).elim (fun h=>UR h) (fun h=>WR h))
    · rcases tcase with same|same|qR
      · exact notinside (mem_sdiff.mp qr).1 (same.symm ▸ aA)
      · exact notinside (mem_sdiff.mp qr).1 (same.symm ▸ bA)
      · exact (mem_sdiff.mp qr).2 qR
  have h := add_closed rem t d
  have inside : ({a,b}:Finset V)⊆A := insert_subset_iff.mpr ⟨aA,singleton_subset_iff.mpr bA⟩
  have outside : ({u,v} ∪ {w,z}:Finset V)⊆R := union_subset UR WR
  have shape : ({a,u,v}:Finset V) ∪ {b,w,z} = ({a,b}:Finset V) ∪ ({u,v} ∪ {w,z}) := by
    ext q
    simp only [mem_union,mem_insert,mem_singleton]
    tauto
  have eq : ((A\{a,b}) ∪ (R\({u,v} ∪ {w,z}))) ∪ ({a,u,v} ∪ {b,w,z}) = A∪R := by
    rw [shape]
    calc
      _ = ((A\{a,b}) ∪ {a,b}) ∪ ((R\({u,v} ∪ {w,z})) ∪ ({u,v} ∪ {w,z})) := by ac_rfl
      _ = _ := by rw [sdiff_union_of_subset inside,sdiff_union_of_subset outside]
  exact eq ▸ h

#print axioms join_two_singletons_to_two_edges
end KelmansCactus.AtomicBridge
