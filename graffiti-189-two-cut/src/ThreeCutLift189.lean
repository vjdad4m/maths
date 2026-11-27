import ThreeSide189
namespace Graffiti189LongestPath.FourCut.Three
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- A hypothetical three-component deletion gives the abstract three-side data. -/
theorem exists_sides (hc : G.Connected) (a b : V) (ab : a≠b)
    (d2 : ∀ x, (DistanceTwo G x).card≤4)
    (even : ∀ x, (EvenFrom G x).card≤5)
    (degree : ∀ u v : V, u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    (del : ∀ b : V, (G.induce {x : V | x≠b}).Connected)
    (many : 3≤Nat.card (G.induce {x : V | x≠a ∧ x≠b}).ConnectedComponent) :
    Nonempty (Sides G a b) := by
  classical
  let J := G.induce {x : V | x≠a ∧ x≠b}
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c => c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  have n : Fintype.card (Fin 3) ≤ Fintype.card J.ConnectedComponent := by
    rw [Fintype.card_fin,←Nat.card_eq_fintype_card]
    exact many
  obtain ⟨C⟩ := Function.Embedding.nonempty_of_card_le n
  let H (i : Fin 3) : Finset V := Finset.univ.filter (fun x =>
    ∃ (hx : x≠a ∧ x≠b), J.connectedComponentMk ⟨x,hx⟩=C i)
  have mem {i : Fin 3} {x : V} : x∈H i ↔
      ∃ (hx : x≠a ∧ x≠b), J.connectedComponentMk ⟨x,hx⟩=C i := by simp [H]
  have ds (i j : Fin 3) (ij : i≠j) : Disjoint (H i) (H j) := by
    apply disjoint_left.mpr
    intro x xi xj
    obtain ⟨hx,hi⟩ := mem.mp xi
    obtain ⟨_,hj⟩ := mem.mp xj
    exact ij (C.injective (hi.symm.trans hj))
  have off (i : Fin 3) : a∉H i ∧ b∉H i :=
    ⟨fun ha => (mem.mp ha).choose.1 rfl,fun hb => (mem.mp hb).choose.2 rfl⟩
  have closed (i : Fin 3) (x : V) (hx : x∈H i) (y : V) (xy : G.Adj x y) :
      y=a ∨ y=b ∨ y∈H i := by
    by_cases ya : y=a
    · exact Or.inl ya
    by_cases yb : y=b
    · exact Or.inr (Or.inl yb)
    obtain ⟨hx',hx''⟩ := mem.mp hx
    have edge : J.Adj ⟨x,hx'⟩ ⟨y,⟨ya,yb⟩⟩ := xy
    exact Or.inr (Or.inr (mem.mpr ⟨⟨ya,yb⟩,
      (ConnectedComponent.sound ⟨Walk.cons edge Walk.nil⟩).symm.trans hx''⟩))
  have joins (i : Fin 3) (x : V) (xi : x∈H i) (y : V) (yi : y∈H i) :
      ∃ q : G.Walk x y, ∀ z∈q.support,z∈H i := by
    obtain ⟨xoff,xc⟩ := mem.mp xi
    obtain ⟨yoff,yc⟩ := mem.mp yi
    obtain ⟨w⟩ := ConnectedComponent.exact (xc.trans yc.symm)
    let f : J →g G := { toFun := Subtype.val, map_rel' := fun a => a }
    refine ⟨w.map f,?_⟩
    intro z zw
    rw [support_map,List.mem_map] at zw
    obtain ⟨u,uw,rfl⟩ := zw
    have e := ConnectedComponent.sound ((show J.Reachable ⟨x,xoff⟩ u from ⟨w.takeUntil u uw⟩).symm)
    exact mem.mpr ⟨u.property,e.trans xc⟩
  have non (i : Fin 3) : (H i).Nonempty := by
    obtain ⟨x,hx⟩ := (C i).exists_rep
    exact ⟨x.val,mem.mpr ⟨x.property,hx⟩⟩
  have hit (i : Fin 3) (s t : V) (st : s≠t) (sout : s∉H i) (tout : t∉H i)
      (cl : ∀ x∈H i, ∀ y, G.Adj x y → y=s ∨ y=t ∨ y∈H i) :
      ∃ x∈H i,G.Adj s x := by
    by_cases h : ∃ x∈H i,G.Adj s x
    · exact h
    exfalso
    obtain ⟨x,xi⟩ := non i
    let K := G.induce {x : V | x≠t}
    let u : {x : V // x∈{x : V | x≠t}} := ⟨x,fun e => tout (e ▸ xi)⟩
    let v : {x : V // x∈{x : V | x≠t}} := ⟨s,st⟩
    obtain ⟨w⟩ := (del t) u v
    have stay {u v : {x : V // x∈{x : V | x≠t}}} (q : K.Walk u v)
        (hu : (u : V) ∈ H i) : (v : V) ∈ H i := by
      induction q with
      | nil => exact hu
      | @cons u v w uv q ih =>
        apply ih
        have uv' : G.Adj u.val v.val := uv
        rcases cl u.val hu v.val uv' with vs|vt|vv
        · exact (h ⟨u.val,hu,by simpa only [vs] using uv'.symm⟩).elim
        · exact (v.property vt).elim
        · exact vv
    exact sout (stay w xi)
  have ha (i : Fin 3) := hit i a b ab (off i).1 (off i).2 (closed i)
  have hb (i : Fin 3) := hit i b a ab.symm (off i).2 (off i).1
    (fun x hx y xy => (closed i x hx y xy).elim (fun h => Or.inr (Or.inl h))
      (fun h => h.elim Or.inl (fun h => Or.inr (Or.inr h))))
  refine ⟨⟨hc,ab,d2,even,degree,H,ds,off,closed,joins,ha,hb,?_⟩⟩
  intro i two
  let T := (H i).filter (fun x => G.Adj a x ∨ G.Adj b x)
  change 2≤T.card
  by_cases ht : 2≤T.card
  · exact ht
  exfalso
  obtain ⟨c,ci,ac⟩ := ha i
  have ct : c∈T := mem_filter.mpr ⟨ci,Or.inl ac⟩
  have ex : ∃ x∈H i,x≠c := by
    have e := card_erase_of_mem ci
    obtain ⟨x,hx⟩ := card_pos.mp (show 0<((H i).erase c).card by omega)
    exact ⟨x,(mem_erase.mp hx).2,(mem_erase.mp hx).1⟩
  obtain ⟨x,xi,xc⟩ := ex
  have offa : a≠c := fun e => (off i).1 (e.symm ▸ ci)
  let K := G.induce {x : V | x≠c}
  let u : {x : V // x∈{x : V | x≠c}} := ⟨x,xc⟩
  let v : {x : V // x∈{x : V | x≠c}} := ⟨a,offa⟩
  obtain ⟨w⟩ := (del c) u v
  have stay {u v : {x : V // x∈{x : V | x≠c}}} (q : K.Walk u v)
      (hu : (u : V) ∈ H i) : (v : V) ∈ H i := by
    induction q with
    | nil => exact hu
    | @cons u v w uv q ih =>
      apply ih
      have uv' : G.Adj u.val v.val := uv
      have no : ¬u.val∈T := fun ut => u.property (card_le_one.mp (by omega : T.card≤1) u.val ut c ct)
      rcases closed i u.val hu v.val uv' with va|vb|vv
      · exact (no (mem_filter.mpr ⟨hu,Or.inl (by simpa only [va] using uv'.symm)⟩)).elim
      · exact (no (mem_filter.mpr ⟨hu,Or.inr (by simpa only [vb] using uv'.symm)⟩)).elim
      · exact vv
  exact (off i).1 (stay w xi)

#print axioms exists_sides

namespace Sides
variable {a b : V} (S : Sides G a b)

def reorder (f : Equiv.Perm (Fin 3)) : Sides G a b where
  con := S.con
  ab := S.ab
  d2 := S.d2
  even := S.even
  degree := S.degree
  H i := S.H (f i)
  dis i j ne := S.dis (f i) (f j) (fun e => ne (f.injective e))
  off i := S.off (f i)
  closed i := S.closed (f i)
  joined i := S.joined (f i)
  hita i := S.hita (f i)
  hitb i := S.hitb (f i)
  plenty i := S.plenty (f i)

theorem size_not_two (i : Fin 3) : (S.H i).card ≠ 2 := by
  intro eq
  obtain ⟨x,xi,y,yi,xy⟩ := one_lt_card.mp (show 1<(S.H i).card by omega)
  have low {v : V} (vi : v∈S.H i) : ¬4≤G.degree v := by
    have sub : G.neighborFinset v ⊆ insert a (insert b ((S.H i).erase v)) := by
      intro w hw
      have vw := (mem_neighborFinset G v w).mp hw
      rcases S.closed i v vi w vw with rfl|rfl|wi
      · simp
      · simp
      · exact mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inr (mem_erase.mpr ⟨vw.ne.symm,wi⟩))))
    have c := card_le_card sub
    have c1 := card_insert_le a (insert b ((S.H i).erase v))
    have c2 := card_insert_le b ((S.H i).erase v)
    rw [card_neighborFinset_eq_degree] at c
    rw [card_erase_of_mem vi] at c2
    omega
  exact (S.degree x y xy).elim (low xi) (low yi)
end Sides

end Graffiti189LongestPath.FourCut.Three
