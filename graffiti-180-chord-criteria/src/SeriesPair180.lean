import WitnessExtension180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Append two adjacent new vertices. The first has precisely the old
neighbor u, the second precisely the old neighbor v. -/
noncomputable def series (u v : V) :=
  ear (ear G {u}) ({Sum.inl v,Sum.inr ()} : Finset (V ⊕ Unit))

theorem series_rank (u v : V) : bipartiteNum G+1≤bipartiteNum (series G u v) := by
  classical
  obtain ⟨X,⟨C,D,dis,rfl,ic,id⟩,top⟩ := optB G
  rw [card_union_of_disjoint dis] at top
  have up : bipartiteNum G<bipartiteNum (ear G {u}) := by
    apply (color_gain_iff G {u}).mpr
    by_cases c : u∈C
    · have d : u∉D := fun ud => disjoint_left.mp dis c ud
      exact ⟨D,C,id,ic,dis.symm,(Nat.add_comm ..).trans top,by simpa using d⟩
    · exact ⟨C,D,ic,id,dis,top,by simpa using c⟩
  exact up.trans_le (rank_mono (ear G {u}) _)

/-- Keep the serial path from the old u. Its last vertex is a new leaf
and u is the only old vertex whose eligible leaf can be lost. -/
theorem series_hang (hc : G.Connected) (hn : 2<Fintype.card V) (u v : V) (U : Finset V) (e f : Bool) :
    weightedLeaves G (U.erase u)+f.toNat ≤ weightedLeaves (series G u v) (lift (lift U e) f) := by
  classical
  let K := ear G {u}
  let z : V ⊕ Unit := .inr ()
  let M := ({Sum.inl v,z} : Finset (V ⊕ Unit))
  have kc := ear_connected G hc {u} (singleton_nonempty _)
  have ksize : 2<Fintype.card (V ⊕ Unit) := by simp only [Fintype.card_sum,Fintype.card_unit]; omega
  have h := attach K kc ksize M (lift U e) f z (mem_insert_of_mem (mem_singleton_self _))
  have er : (lift U e).erase z=lift U false := by
    ext w
    rcases w with a|a
    · simp [z]
    · cases a; simp [z]
  rw [er] at h
  have a := attach_lower G (by omega) U {u} u (mem_singleton_self _)
  exact (Nat.add_le_add_right a f.toNat).trans h

/-- A pair of degree-two vertices along a serial path is safely reducible
when the inherited parity is unchanged jointly and the two vertices
carry at most the single membership at the free end of that path.
The intermediate graph's parity is unrestricted. -/
theorem series_reduce (hc : G.Connected) (hn : 2<Fintype.card V) (u v r : V) (odd : Bool)
    (A : Finset V) (a p b q : Bool)
    (stable : parity (series G u v) (.inl (.inl r)) odd=lift (lift (parity G r odd) p) q)
    (one : a.toNat+p.toNat+b.toNat+q.toNat≤(b||q).toNat)
    (base : let P := parity G r odd
            1+A.card+P.card≤weightedLeaves G (eligible A P r)+bipartiteNum G) :
    let H := series G u v
    let B := lift (lift A a) b
    let P := parity H (.inl (.inl r)) odd
    1+B.card+P.card≤weightedLeaves H (eligible B P (.inl (.inl r)))+bipartiteNum H := by
  dsimp only at *
  rw [stable,eligible_lift,eligible_lift]
  simp only [card_lift]
  have rank := series_rank G u v
  have leaf := series_hang G hc hn u v (eligible A (parity G r odd) r) (a||p) (b||q)
  have cost := erase_cost G (eligible A (parity G r odd) r) u
  omega

#print axioms series_rank
#print axioms series_hang
#print axioms series_reduce
end Minimal180
