import P5CliqueMixedPairKernel133

namespace Graffiti133P5CliqueArms.MixedPairCertificate
open SimpleGraph Graffiti133 Graffiti133Camby
open scoped Classical

/-- Fill all optional edges directly from the host adjacency. To use an exact
forbidden model it is enough to certify the fixed pairs of that model. -/
theorem optional_edges_fill {n : Nat} {V : Type*} {G : SimpleGraph V}
    (S : Model n) (f : Fin n→V)
    (fixedFit : ∀ x y,optionalCode S x y=none→
      (G.Adj (f x) (f y) ↔ (S.forced x).testBit y.val=true)) :
    ∃ m : Nat, ∀ x y,G.Adj (f x) (f y) ↔ edge S m x y=true := by
  classical
  let vals := S.optional.map (fun t=>decide (G.Adj (f t.1) (f t.2)))
  let m := (BitVec.ofBoolListLE vals).toNat
  refine ⟨m,?_⟩
  intro x y
  unfold edge
  cases eq : optionalCode S x y with
  | none => exact fixedFit x y eq
  | some i =>
    change S.optional.findIdx? (_ : Fin n×Fin n→Bool)=some i at eq
    obtain ⟨iok,form,_⟩ := List.findIdx?_eq_some_iff_getElem.mp eq
    have orient : S.optional[i].1=min x y ∧ S.optional[i].2=max x y := by
      simpa only [Bool.and_eq_true,beq_iff_eq] using form
    have read : m.testBit i=decide (G.Adj (f S.optional[i].1) (f S.optional[i].2)) := by
      change (BitVec.ofBoolListLE vals).getLsbD i=_
      rw [BitVec.getLsb_ofBoolListLE,List.getD_eq_getElem?_getD]
      unfold vals
      rw [List.getElem?_map,List.getElem?_eq_getElem iok]
      rfl
    change G.Adj (f x) (f y)↔m.testBit i=true
    rw [read,orient.1,orient.2,decide_eq_true_eq]
    rcases le_total x y with le|le
    · rw [min_eq_left le,max_eq_right le]
    · rw [min_eq_right le,max_eq_left le,SimpleGraph.adj_comm]

#print axioms optional_edges_fill
end Graffiti133P5CliqueArms.MixedPairCertificate
