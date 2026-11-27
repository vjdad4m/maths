import FlankAttachment
import CompactRows

open private three_names_exhaust_neighbors from DepletedFootprint

namespace Graffiti199Depleted.CompactOmission

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {z : V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

omit [DecidableEq V] [Fintype V] in
private theorem pred_mem {p : PathOn G {v | v ≠ z}} {L R : List V} {x y : V}
    (split : p.vertices = L ++ x :: y :: R) (h : G.Adj z y) :
    x ∈ p.predecessors := by
  have k : L.length < p.vertices.length - 1 := by rw [split]; simp
  let i : p.EdgePosition := ⟨L.length,k⟩
  have l : p.before i = x := by
    simp only [PathOn.before,i,split,List.getElem_append_right (le_refl L.length),Nat.sub_self,
      List.getElem_cons_zero]
  have r : p.after i = y := by
    simp only [PathOn.after,i,split,List.getElem_append_right (Nat.le_succ L.length),
      show L.length.succ - L.length = 1 by omega,List.getElem_cons_succ,List.getElem_cons_zero]
  exact p.mem_predecessors.mpr ⟨i,r.symm ▸ h,l⟩

omit [DecidableEq V] [Fintype V] in
private theorem succ_mem {p : PathOn G {v | v ≠ z}} {L R : List V} {x y : V}
    (split : p.vertices = L ++ x :: y :: R) (h : G.Adj z x) :
    y ∈ p.rev.predecessors := by
  apply pred_mem (L := R.reverse) (R := L.reverse) ?_ h
  change p.vertices.reverse = _
  simp [split,List.reverse_append,List.reverse_cons,List.append_assoc]

omit [DecidableEq V] in
private theorem no_extra_neighbor (f : Fin 8 ↪ V) {k a b c x : Fin 8}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (degree : G.degree (f k) = 3)
    (ka : G.Adj (f k) (f a)) (kb : G.Adj (f k) (f b)) (kc : G.Adj (f k) (f c))
    (off : x ∉ [a,b,c]) : ¬ G.Adj (f k) (f x) := by
  intro e
  obtain ⟨i,hi,ix⟩ := three_names_exhaust_neighbors f ab ac bc degree ka kb kc (f x) e
  exact off (f.injective ix ▸ hi)

/-- For the consecutive block P-A-X-B-Y-C-Q, with A,B,C independent
neighbors of the omitted vertex and one of them cubic, only six
adjacency rows survive the tree bound and the splice constraints. -/
theorem compact_cubic_omission_rows (noTrace : ¬ Catalogue.Traceable G)
    (budget : Catalogue.treeNumber G ≤ 5) (f : Fin 8 ↪ V)
    (p : PathOn G {v | v ≠ f 7}) (L R : List V)
    (split : p.vertices = L ++ [f 0,f 1,f 2,f 3,f 4,f 5,f 6] ++ R)
    (z1 : G.Adj (f 7) (f 1)) (z3 : G.Adj (f 7) (f 3)) (z5 : G.Adj (f 7) (f 5))
    (off13 : ¬ G.Adj (f 1) (f 3)) (off15 : ¬ G.Adj (f 1) (f 5))
    (off35 : ¬ G.Adj (f 3) (f 5))
    (cubic : G.degree (f 1) = 3 ∨ G.degree (f 3) = 3 ∨ G.degree (f 5) = 3) :
    G.Adj (f 0) (f 6) ∧ L ≠ [] ∧ R ≠ [] ∧
      ∃ r : Row, allowed r = true ∧
        ∀ i j : Fin 8, G.Adj (f i) (f j) ↔ adjacent r i j = true := by
  classical
  have full : (L ++ ([f 0,f 1,f 2,f 3,f 4,f 5,f 6] ++ R)).Chain' G.Adj := by
    rw [← List.append_assoc,← split]
    exact p.chain
  have middle := full.right_of_append.left_of_append
  simp only [List.chain'_cons,List.chain'_singleton,and_true] at middle
  obtain ⟨e01,e12,e23,e34,e45,e56⟩ := middle
  have pred0 : f 0 ∈ p.predecessors := pred_mem
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split) z1
  have pred2 : f 2 ∈ p.predecessors := pred_mem
    (L := L ++ [f 0,f 1])
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split) z3
  have pred4 : f 4 ∈ p.predecessors := pred_mem
    (L := L ++ [f 0,f 1,f 2,f 3])
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split) z5
  have suc2 : f 2 ∈ p.rev.predecessors := succ_mem
    (L := L ++ [f 0])
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split) z1
  have suc4 : f 4 ∈ p.rev.predecessors := succ_mem
    (L := L ++ [f 0,f 1,f 2])
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split) z3
  have suc6 : f 6 ∈ p.rev.predecessors := succ_mem
    (L := L ++ [f 0,f 1,f 2,f 3,f 4])
    (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using split) z5
  have off02 := p.terminalFlanks_independent noTrace _ (Finset.mem_insert_of_mem pred0)
    _ (Finset.mem_insert_of_mem pred2)
  have off04 := p.terminalFlanks_independent noTrace _ (Finset.mem_insert_of_mem pred0)
    _ (Finset.mem_insert_of_mem pred4)
  have off24 := p.terminalFlanks_independent noTrace _ (Finset.mem_insert_of_mem pred2)
    _ (Finset.mem_insert_of_mem pred4)
  have off26 := p.rev.terminalFlanks_independent noTrace _ (Finset.mem_insert_of_mem suc2)
    _ (Finset.mem_insert_of_mem suc6)
  have off46 := p.rev.terminalFlanks_independent noTrace _ (Finset.mem_insert_of_mem suc4)
    _ (Finset.mem_insert_of_mem suc6)
  have off07 : ¬ G.Adj (f 0) (f 7) := fun e =>
    p.no_edge_from_omitted_to_terminalFlanks noTrace _ (Finset.mem_insert_of_mem pred0) e.symm
  have off27 : ¬ G.Adj (f 2) (f 7) := fun e =>
    p.no_edge_from_omitted_to_terminalFlanks noTrace _ (Finset.mem_insert_of_mem pred2) e.symm
  have off47 : ¬ G.Adj (f 4) (f 7) := fun e =>
    p.no_edge_from_omitted_to_terminalFlanks noTrace _ (Finset.mem_insert_of_mem pred4) e.symm
  have off67 : ¬ G.Adj (f 6) (f 7) := fun e =>
    p.rev.no_edge_from_omitted_to_terminalFlanks noTrace _ (Finset.mem_insert_of_mem suc6) e.symm
  let r : Row := ⟨decide (G.Adj (f 0) (f 3)),decide (G.Adj (f 0) (f 5)),
    decide (G.Adj (f 0) (f 6)),decide (G.Adj (f 2) (f 5)),decide (G.Adj (f 1) (f 4)),
    decide (G.Adj (f 1) (f 6)),decide (G.Adj (f 3) (f 6))⟩
  have chart_cubic : hasCubicSlot r = true := by
    rcases cubic with d|d|d
    · have h14 := no_extra_neighbor f (x := 4) (by decide) (by decide) (by decide) d
        e01.symm e12 z1.symm (by decide)
      have h16 := no_extra_neighbor f (x := 6) (by decide) (by decide) (by decide) d
        e01.symm e12 z1.symm (by decide)
      simp [hasCubicSlot,flags,r,h14,h16]
    · have h30 := no_extra_neighbor f (x := 0) (by decide) (by decide) (by decide) d
        e23.symm e34 z3.symm (by decide)
      have h36 := no_extra_neighbor f (x := 6) (by decide) (by decide) (by decide) d
        e23.symm e34 z3.symm (by decide)
      have h03 : ¬ G.Adj (f 0) (f 3) := fun e => h30 e.symm
      simp [hasCubicSlot,flags,r,h03,h36]
    · have h50 := no_extra_neighbor f (x := 0) (by decide) (by decide) (by decide) d
        e45.symm e56 z5.symm (by decide)
      have h52 := no_extra_neighbor f (x := 2) (by decide) (by decide) (by decide) d
        e45.symm e56 z5.symm (by decide)
      have h05 : ¬ G.Adj (f 0) (f 5) := fun e => h50 e.symm
      have h25 : ¬ G.Adj (f 2) (f 5) := fun e => h52 e.symm
      simp [hasCubicSlot,flags,r,h05,h25]
  have forward (i j : Fin 8) (ij : i ≤ j) : G.Adj (f i) (f j) ↔ adjacent r i j = true := by
    fin_cases i <;> fin_cases j <;> first
    | exact ((by decide : ¬ (_ ≤ _)) ij).elim
    | simp [adjacent,directed,flags,r,
        e01,e12,e23,e34,e45,e56,z1.symm,z3.symm,z5.symm,off13,off15,off35,
        off02,off04,off24,off26,off46,off07,off27,off47,off67]
  have chart (i j : Fin 8) : G.Adj (f i) (f j) ↔ adjacent r i j = true := by
    rcases le_total i j with a|b
    · exact forward i j a
    · rw [G.adj_comm]
      simpa only [adjacent,Bool.or_comm] using forward j i b
  have survives : allowed r = true := by
    rcases coverage r chart_cubic with ok|⟨inj,parents⟩
    · exact ok
    · let g : Fin 6 ↪ V := ⟨f ∘ treeOrder (mask r),fun i j h => inj i j (f.injective h)⟩
      have six := Catalogue.six_le_treeNumber_of_ordering (G := G) g (by
        intro i i0
        obtain ⟨j,ij,lt,uniq⟩ := parents i i0
        exact ⟨j,(chart _ _).mpr ij,lt,fun k h lk => uniq k ((chart _ _).mp h) lk⟩)
      omega
  have chord : G.Adj (f 0) (f 6) := (chart 0 6).mpr (allowed_outer_chord r survives)
  have offL : L ≠ [] := by
    rintro rfl
    have first : p.first = f 0 := by
      have h : p.vertices.head? = some (f 0) := by simp [split]
      rw [List.head?_eq_head p.nonempty] at h
      exact Option.some.inj h
    have terminal : f 0 ∈ p.rev.terminalFlanks := by
      rw [PathOn.terminalFlanks,PathOn.rev_last,first]
      exact Finset.mem_insert_self _ _
    exact p.rev.terminalFlanks_independent noTrace _ terminal _
      (Finset.mem_insert_of_mem suc6) chord
  have offR : R ≠ [] := by
    rintro rfl
    have last : p.last = f 6 := by
      have h : p.vertices.getLast? = some (f 6) := by
        rw [split,List.append_nil,List.getLast?_append_of_ne_nil L (by simp)]
        rfl
      rw [List.getLast?_eq_getLast p.nonempty] at h
      exact Option.some.inj h
    have terminal : f 6 ∈ p.terminalFlanks := by
      rw [PathOn.terminalFlanks,last]
      exact Finset.mem_insert_self _ _
    exact p.terminalFlanks_independent noTrace _ (Finset.mem_insert_of_mem pred0) _ terminal chord
  exact ⟨chord,offL,offR,r,survives,chart⟩

#print axioms compact_cubic_omission_rows

end Graffiti199Depleted.CompactOmission
