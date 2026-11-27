import TwoEarFront
namespace Graffiti384b.TwoEars
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In a failure, the exterior anchors of two ears with a common hub
have no common neighbor other than that hub. -/
theorem outer_separation {e f a b c : V} (ef : e≠f) (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (en : G.neighborFinset e={a,b}) (fn' : G.neighborFinset f={a,c})
    (sep : Disjoint ({e,f}:Finset V) {a,b,c}) (bad : bound G<gamma G) :
    G.neighborFinset b∩G.neighborFinset c⊆{a} := by
  classical
  intro w wm
  by_contra no
  have wa := fun h : w=a => no (mem_singleton.mpr h)
  have bw := (G.mem_neighborFinset ..).mp (mem_inter.mp wm).1
  have cw := (G.mem_neighborFinset ..).mp (mem_inter.mp wm).2
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  have fa : G.Adj f a := (G.mem_neighborFinset ..).mp (fn' ▸ mem_insert_self ..)
  have fc : G.Adj f c := (G.mem_neighborFinset ..).mp (fn' ▸ mem_insert_of_mem (mem_singleton_self _))
  have we : w≠e := by intro eq; subst w; have m := (G.mem_neighborFinset ..).mpr cw.symm; simp [en,ac.symm,bc.symm] at m
  have wf : w≠f := by intro eq; subst w; have m := (G.mem_neighborFinset ..).mpr bw.symm; simp [fn',ab.symm,bc] at m
  let L : Finset V := insert w {e,f}
  let R : Finset V := {a,b,c}
  have fr : EarFrame33.Frame G L R := by
    refine ⟨disjoint_left.mpr ?_,?_,?_⟩
    · intro i il ir; rcases mem_insert.mp il with eq|m
      · rw [eq] at ir; simp only [R,mem_insert,mem_singleton] at ir
        exact ir.elim wa (fun h => h.elim bw.ne.symm cw.ne.symm)
      · exact disjoint_left.mp sep m ir
    · intro i il; simp only [L,mem_insert,mem_singleton] at il
      rcases il with rfl|rfl|rfl
      · exact PinnedColor34.two G bc bw.symm cw.symm (by simp [R]) (by simp [R])
      · exact PinnedColor34.two G ab ea eb (by simp [R]) (by simp [R])
      · exact PinnedColor34.two G ac fa fc (by simp [R]) (by simp [R])
    · intro i ir; simp only [R,mem_insert,mem_singleton] at ir
      rcases ir with rfl|rfl|rfl
      · exact PinnedColor34.two G ef ea.symm fa.symm (by simp [L]) (by simp [L])
      · exact PinnedColor34.two G we bw eb.symm (by simp [L]) (by simp [L])
      · exact PinnedColor34.two G wf cw fc.symm (by simp [L]) (by simp [L])
  exact ef (Squares29.sparse G bad _ _ fr e (mem_union_left _ (by simp [L])) f (mem_union_left _ (by simp [L]))
    (by rw [←card_neighborFinset_eq_degree,en,card_pair ab]) (by rw [←card_neighborFinset_eq_degree,fn',card_pair ac]))
end Graffiti384b.TwoEars
#print axioms Graffiti384b.TwoEars.outer_separation
