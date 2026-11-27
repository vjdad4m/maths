import FullMaskCover

namespace Graffiti199Depleted.WiderOmission

/-- The earlier-neighbor certificate can be checked by counting
rather than searching separately for each candidate parent. -/
def fastClause {n : ℕ} (p : Pattern n) (c : TreeClause n) : Bool :=
  let I := List.finRange 6
  (I.all fun i => I.all fun j => decide (i = j) || !(c.order i == c.order j)) &&
  (I.all fun i => I.all fun j => p.known c.domain (c.order i) (c.order j)) &&
  (I.all fun i =>
    if i = 0 then true
    else decide ((I.filter fun j => decide (j < i) && p.edge c.value (c.order i) (c.order j)).length = 1))

theorem fastClause_sound {n : ℕ} {p : Pattern n} {c : TreeClause n}
    (h : fastClause p c = true) : c.Valid p := by
  let I := List.finRange 6
  have hm (i : Fin 6) : i ∈ I := List.mem_finRange i
  unfold fastClause at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨d,kn⟩,earlier⟩ := h
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i j eq
    have rel := List.all_eq_true.mp (List.all_eq_true.mp d i (hm i)) j (hm j)
    simpa [eq] using rel
  · intro i nz
    have one := List.all_eq_true.mp earlier i (hm i)
    let B := I.filter (fun j => decide (j < i) && p.edge c.value (c.order i) (c.order j))
    have size : B.length = 1 := by
      simpa only [if_neg nz,decide_eq_true_eq] using one
    obtain ⟨j,only⟩ := List.length_eq_one_iff.mp size
    have mem : j ∈ B := by rw [only]; simp
    have spec : j < i ∧ p.edge c.value (c.order i) (c.order j) = true := by
      simpa only [B,List.mem_filter,Bool.and_eq_true,decide_eq_true_eq,hm j,true_and] using mem
    refine ⟨j,spec.2,spec.1,?_⟩
    intro t edge lt
    have mt : t ∈ B := by simpa only [B,List.mem_filter,hm t,true_and,Bool.and_eq_true,decide_eq_true_eq] using And.intro lt edge
    simpa only [only,List.mem_singleton] using mt
  · intro i j
    exact List.all_eq_true.mp (List.all_eq_true.mp kn i (hm i)) j (hm j)

theorem fastClauses_sound {n : ℕ} {p : Pattern n} {cs : List (TreeClause n)}
    (h : cs.all (fastClause p) = true) (i : Fin cs.length) : (cs.get i).Valid p :=
  fastClause_sound (List.all_eq_true.mp h _ (List.get_mem _ _))

end Graffiti199Depleted.WiderOmission
