import NestedCoreCleanArms133
import NestedCoreSingletonGate133

namespace Graffiti133NestedSingleGate
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133MultiC7
  Graffiti133NestedFour
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def cycleArm4 (i : Fin 7) (reverse : Bool) : Fin 4→Fin 7 :=
  if reverse then ![i,i-1,i-2,i-3] else ![i,i+1,i+2,i+3]

theorem cycleArm4_checks : ∀ i reverse,
    (∀ a b : Fin 4,cycleArm4 i reverse a=cycleArm4 i reverse b→a=b) ∧
    (∀ a b : Fin 4,a<b→
      (Cyclic (cycleArm4 i reverse a) (cycleArm4 i reverse b)↔a.val+1=b.val)) := by decide

theorem short_cycle_contact_arm :
    ∀ A : Finset (Fin 7),A.Nonempty→A.card≤2→
      ∃ i reverse,∀ t : Fin 4,cycleArm4 i reverse t∈A↔t=0 := by decide

theorem four_cycle_vertices_extend_any_short_gate (H : Hole G 7) (z : V)
    (hit : (contactSet H z).Nonempty) (short : (contactSet H z).card≤2) :
    Arm (G:=G) (Set.range H.c) z := by
  obtain ⟨i,rev,h⟩ := short_cycle_contact_arm (contactSet H z) hit short
  have cert := cycleArm4_checks i rev
  refine ⟨H.c ∘ cycleArm4 i rev,⟨H.inj.comp (fun a b e=>cert.1 a b e),?_⟩,?_,?_⟩
  · intro a b lt
    exact (H.adj _ _).trans (cert.2 a b lt)
  · intro j
    exact ⟨cycleArm4 i rev j,rfl⟩
  · intro j
    exact (mem_contactSet H z (cycleArm4 i rev j)).symm.trans (h j)

theorem short_gate_excludes_remote_clean_arm
    (H : Hole G 7) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    {W : Set V} (remote : ∀ x∈W, Remote H x)
    (z : V) (off : Outside H.c z)
    (hit : (contactSet H z).Nonempty) (short : (contactSet H z).card≤2) :
    ¬Arm (G:=G) W z := by
  intro farArm
  have gateNotRemote : z∉W := by
    intro zw
    obtain ⟨i,im⟩ := hit
    exact (remote z zw).2 i ((mem_contactSet H z i).mp im)
  have gateOffCycle : z∉Set.range H.c := by
    rintro ⟨i,ei⟩
    exact off i ei.symm
  have apart : Disjoint W (Set.range H.c) := by
    apply Set.disjoint_left.mpr
    rintro x xm ⟨i,rfl⟩
    exact (remote _ xm).1 i rfl
  have noEdge (x : V) (xm : x∈W) (y : V) (ym : y∈Set.range H.c) : ¬G.Adj x y := by
    obtain ⟨i,rfl⟩ := ym
    exact (remote x xm).2 i
  exact h9 (two_clean_arms_induced_P9 gateNotRemote gateOffCycle apart noEdge farArm
    (four_cycle_vertices_extend_any_short_gate H z hit short))

#print axioms four_cycle_vertices_extend_any_short_gate
#print axioms short_gate_excludes_remote_clean_arm
end Graffiti133NestedSingleGate
