import OrbitArms

namespace Graffiti384b.OddStars.HallArms
open Finset SimpleGraph PositivePalette OneEar
open private OddStars.true_ear from TriangleBlocks
open private OddStars.no_zero_neighbor from ZeroTwoLayout
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In an original-graph failure with a degree-two zero z and any count-one
ear e, there are disjoint simple arms between the two pairs of neighbors.
Their edges lie in triangles and their vertices avoid both e and z. -/
theorem failure_disjoint_arms (bad : bound G<gamma G) {z e : V} (zz : trianglesAt G z=0)
    (dz : G.degree z=2) (one : trianglesAt G e=1) :
    let J := patch G {z}
    let K := inside J ({e,z}ᶜ)
    ∃a b c d : V, J.neighborFinset e={a,b} ∧ J.neighborFinset z={c,d} ∧
      a≠b ∧ c≠d ∧ ∃n m : ℕ, ∃p : Route K e a c n, ∃q : Route K e b d m,
      ∀i≤n,∀j≤m,p.atIdx i≠q.atIdx j := by
  classical
  let J := patch G {z}
  have ee := (zero_two_forces_ears G bad zz dz).2 e one
  have ed := OddStars.true_ear G one ee {z}
  have zd : J.degree z=2 := (center_degree G (mem_singleton_self _)).trans dz
  have ez : e≠z := fun eq => by rw [eq,zz] at one; contradiction
  have off : ¬J.Adj e z := fun h => OddStars.no_zero_neighbor G ee one zz h.1
  have survive (c : V) (ec : e≠c) (zc : z≠c) : (inside J ({c}ᶜ)).Reachable e z :=
    (zero_ear_in_block G bad zz dz one zc ec).symm
  have matching := hall_matching J ez off ed survive
  have score : 0<trianglesAt J e := by rw [show trianglesAt J e=trianglesAt G e from patch_scores ..,one]; decide
  obtain ⟨a,b,nb,ea,eb,ab⟩ := Prerequisites.ear_pair J ed score
  have dom {u : V} (eu : J.Adj e u) : u∈domain J e z := by
    apply mem_compl.mpr
    intro m
    rcases mem_union.mp m with uez|zu
    · rcases mem_insert.mp uez with ue|uz
      · exact eu.ne ue.symm
      · exact off (mem_singleton.mp uz ▸ eu)
    · exact disjoint_zero_ear G bad zz dz one ((J.mem_neighborFinset ..).mp zu).1 eu.1
  obtain ⟨c,d,zc,zd',cd,n,m,p,q,indep⟩ := extract_arms J ab.ne ea eb (dom ea) (dom eb) matching
  have sub : ({c,d}:Finset V)⊆J.neighborFinset z := insert_subset ((J.mem_neighborFinset ..).mpr zc)
    (singleton_subset_iff.mpr ((J.mem_neighborFinset ..).mpr zd'))
  have mz := eq_of_subset_of_card_le sub (by rw [card_pair cd,card_neighborFinset_eq_degree,zd])
  exact ⟨a,b,c,d,nb,mz.symm,ab.ne,cd,n,m,p,q,indep⟩

end Graffiti384b.OddStars.HallArms
#print axioms Graffiti384b.OddStars.HallArms.failure_disjoint_arms