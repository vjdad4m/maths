import ColorRepair180
import BagBlocks180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)

/-- A module has identical external adjacencies at all its vertices. -/
def Homogeneous (M : Finset V) : Prop := ∀ x∉M,∀ a∈M,∀ b∈M,H.Adj x a ↔ H.Adj x b

def Prime (H : SimpleGraph V) : Prop := ∀ M : Finset V,Homogeneous H M → 1<M.card → M=univ

noncomputable def reps (M : Finset V) (a : V) : Finset V := insert a (univ\M)

noncomputable def collapse (M : Finset V) (a : V) (x : V) : ↥(reps M a) :=
  if h : x∈M then ⟨a,mem_insert_self ..⟩ else ⟨x,mem_insert_of_mem (mem_sdiff.mpr ⟨mem_univ _,h⟩)⟩

theorem collapse_val (M : Finset V) (a : V) (x : V) :
    (collapse M a x).val=if x∈M then a else x := by
  by_cases m : x∈M <;> simp [collapse,m]

theorem module_bags (M : Finset V) (hom : Homogeneous H M) (a : V) (am : a∈M) :
    Bags H (side H (reps M a)) (collapse M a) := by
  classical
  refine ⟨fun i => ?_,fun {x y} ne => ?_⟩
  · refine ⟨i.val,Subtype.ext ?_⟩
    rw [collapse_val]
    rcases mem_insert.mp i.property with ia|im
    · simp [ia,am]
    · exact if_neg (mem_sdiff.mp im).2
  · change H.Adj x y ↔ H.Adj (collapse M a x).val (collapse M a y).val
    rw [collapse_val,collapse_val]
    by_cases xm : x∈M <;> by_cases ym : y∈M
    · exact (ne (Subtype.ext (by simp [collapse_val,xm,ym]))).elim
    · simp only [xm,ym,if_true,if_false]
      exact ⟨fun h => ((hom y ym x xm a am).mp h.symm).symm,
        fun h => ((hom y ym x xm a am).mpr h.symm).symm⟩
    · simp [xm,ym,hom x xm y ym a am]
    · simp [xm,ym]

theorem quotient_order (M : Finset V) (a : V) (am : a∈M) (fat : 1<M.card) (proper : M≠univ) :
    1<Fintype.card ↥(reps M a) ∧ Fintype.card ↥(reps M a)<Fintype.card V := by
  classical
  have out : (univ\M).Nonempty := sdiff_nonempty.mpr (fun sub => proper (Subset.antisymm (subset_univ _) sub))
  have ct := card_sdiff_add_card_eq_card (subset_univ M)
  have pos := card_pos.mpr out
  rw [Fintype.card_coe,reps,card_insert_of_not_mem (by simp [am])]
  rw [card_univ] at ct
  omega

theorem quotient_connected (hc : H.Connected) (M : Finset V) (hom : Homogeneous H M) (a : V) (am : a∈M) :
    (side H (reps M a)).Connected := by
  have bags := module_bags H M hom a am
  exact (side H (reps M a)).connected_iff.mpr ⟨bags.preDown hc.preconnected,⟨⟨a,mem_insert_self ..⟩⟩⟩

/-- External neighbors of a module, evaluated at any member. -/
noncomputable def outside (M : Finset V) (a : V) : Finset V := H.neighborFinset a\M

theorem quotient_degree (M : Finset V) (a : V) :
    (side H (reps M a)).degree ⟨a,mem_insert_self ..⟩=(outside H M a).card := by
  classical
  let i : ↥(reps M a) := ⟨a,mem_insert_self ..⟩
  have eq : push ((side H (reps M a)).neighborFinset i)=outside H M a := by
    ext x
    constructor
    · intro xm
      obtain ⟨y,ym,rfl⟩ := mem_map.mp xm
      have e : H.Adj a y.val := ((side H (reps M a)).mem_neighborFinset _ _).mp ym
      have om := (mem_insert.mp y.property).resolve_left e.ne.symm
      exact mem_sdiff.mpr ⟨(H.mem_neighborFinset _ _).mpr e,(mem_sdiff.mp om).2⟩
    · intro xm
      obtain ⟨xn,om⟩ := mem_sdiff.mp xm
      let j : ↥(reps M a) := ⟨x,mem_insert_of_mem (mem_sdiff.mpr ⟨mem_univ _,om⟩)⟩
      have ed : (side H (reps M a)).Adj i j := (H.mem_neighborFinset _ _).mp xn
      exact (in_push j).mpr (((side H (reps M a)).mem_neighborFinset _ _).mpr ed)
  rw [←eq,card_push,card_neighborFinset_eq_degree]

theorem quotient_nonclique (M : Finset V) (a : V) (i : ↥(reps M a))
    (hit : NonCliqueBag H (collapse M a) i) : i.val=a := by
  classical
  obtain ⟨x,y,xi,yi,ne,_⟩ := hit
  by_contra off
  have up (z : V) (zi : collapse M a z=i) : z=i.val := by
    have h := congrArg Subtype.val zi
    rw [collapse_val] at h
    split_ifs at h with zm
    · exact (off h.symm).elim
    · exact h
  exact ne ((up x xi).trans (up y yi).symm)

/-- Contracting any proper module with at most three external neighbors
transfers a failed root and parity to the strictly smaller induced quotient. -/
theorem low_module_descent (hc : H.Connected) (M : Finset V) (hom : Homogeneous H M)
    (a : V) (am : a∈M) (fat : 1<M.card) (proper : M≠univ) (low : (outside H M a).card≤3)
    (r : V) (p : Bool) (bad : ¬localBound H r (parity H r p)) :
    let J := side H (reps M a)
    let j := collapse M a r
    1<Fintype.card ↥(reps M a) ∧ Fintype.card ↥(reps M a)<Fintype.card V ∧
      J.Connected ∧ ¬localBound J j (parity J j p) := by
  intro J j
  obtain ⟨order,smaller⟩ := quotient_order M a am fat proper
  have gc := quotient_connected H hc M hom a am
  refine ⟨order,smaller,gc,fun old => bad ((module_bags H M hom a am).lowDegreeRooted ?_ gc order r p old)⟩
  intro i hit
  have eq : i=⟨a,mem_insert_self ..⟩ := Subtype.ext (quotient_nonclique H M a i hit)
  rw [eq,quotient_degree H M a]; exact low

#print axioms module_bags
#print axioms quotient_order
#print axioms quotient_degree
#print axioms low_module_descent
end Minimal180.Substitution
