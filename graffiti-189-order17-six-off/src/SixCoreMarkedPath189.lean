import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace Graffiti189SixCore

open Finset SimpleGraph
open scoped Classical
set_option linter.unusedSectionVars false

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (D : SimpleGraph W) [DecidableRel D.Adj]

private theorem path3 {x a b y : W}
    (xa : D.Adj x a) (ab : D.Adj a b) (by' : D.Adj b y)
    (xb : x ≠ b) (xy : x ≠ y) (ay : a ≠ y) :
    ∃ q : D.Walk x y, q.IsPath ∧ 3 ≤ q.length := by
  refine ⟨.cons xa (.cons ab (.cons by' .nil)), ?_, by simp⟩
  simp [Walk.IsPath, xa.ne, xb, xy, ab.ne, ay, by'.ne]

private theorem path4 {x a c b y : W}
    (xa : D.Adj x a) (ac : D.Adj a c) (cb : D.Adj c b) (by' : D.Adj b y)
    (xc : x ≠ c) (xb : x ≠ b) (xy : x ≠ y) (ab : a ≠ b) (ay : a ≠ y) (cy : c ≠ y) :
    ∃ q : D.Walk x y, q.IsPath ∧ 3 ≤ q.length := by
  refine ⟨.cons xa (.cons ac (.cons cb (.cons by' .nil))), ?_, by simp⟩
  simp [Walk.IsPath, xa.ne, xc, xb, xy, ac.ne, ab, ay, cb.ne, cy, by'.ne]

private def contacts (x y : W) := (D.neighborFinset x).erase y

private theorem contacts_spec {x y a : W} :
    a ∈ contacts D x y ↔ a ≠ y ∧ D.Adj x a := by simp [contacts]

private theorem two_contacts_of_high {x y : W} (hx : 3 ≤ D.degree x) :
    2 ≤ (contacts D x y).card := by
  have incl : D.neighborFinset x ⊆ insert y (contacts D x y) := by
    intro a ha
    by_cases ay : a = y
    · simp [ay]
    · exact mem_insert_of_mem ((contacts_spec D).mpr ⟨ay,(mem_neighborFinset D _ _).mp ha⟩)
  have h := (card_le_card incl).trans (card_insert_le _ _)
  rw [card_neighborFinset_eq_degree] at h
  omega

private theorem contacts_nonempty {x y : W} (hx : 1 ≤ D.degree x)
    (hn : D.neighborFinset x ≠ {y}) : (contacts D x y).Nonempty := by
  by_contra he
  have hf := not_nonempty_iff_eq_empty.mp he
  have inc : D.neighborFinset x ⊆ {y} := by
    intro a ha
    by_cases ay : a=y
    · simpa using ay
    · have h := (contacts_spec D).2 ⟨ay,(mem_neighborFinset D _ _).mp ha⟩
      simp [hf] at h
  have e : (D.neighborFinset x).Nonempty := by
    rw [← card_pos,card_neighborFinset_eq_degree]
    omega
  obtain ⟨a,ha⟩ := e
  exact hn (Subset.antisymm inc (by
    have ay : a=y := by simpa using inc ha
    simpa [ay] using ha))

private theorem reverse_exists {x y : W} :
    (∃ q : D.Walk x y, q.IsPath ∧ 3 ≤ q.length) ↔
    (∃ q : D.Walk y x, q.IsPath ∧ 3 ≤ q.length) := by
  constructor <;> intro ⟨q,hq,hn⟩ <;>
    exact ⟨q.reverse,hq.reverse,by simpa using hn⟩

private theorem no_cross {x y a b : W}
    (xy : x ≠ y) (none : ¬∃ q : D.Walk x y, q.IsPath ∧ 3 ≤ q.length)
    (ha : a ∈ contacts D x y) (hb : b ∈ contacts D y x) :
    ¬D.Adj a b := by
  obtain ⟨ay,xa⟩ := (contacts_spec D).mp ha
  obtain ⟨bx,yb⟩ := (contacts_spec D).mp hb
  exact fun ab => none (path3 D xa ab yb.symm bx.symm xy ay)

private theorem exclusive_low {x y a : W} (six : Fintype.card W = 6)
    (xy : x ≠ y) (none : ¬∃ q : D.Walk x y, q.IsPath ∧ 3 ≤ q.length)
    (btwo : 2 ≤ (contacts D y x).card)
    (ha : a ∈ contacts D x y) (na : a ∉ contacts D y x) :
    D.degree a ≤ 2 := by
  obtain ⟨ay,xa⟩ := (contacts_spec D).mp ha
  have ya : ¬D.Adj y a := fun h => na ((contacts_spec D).mpr ⟨xa.ne.symm,h⟩)
  let bad := insert a (insert y (contacts D y x))
  have yc : y ∉ contacts D y x := by simp [contacts_spec]
  have ab : a ∉ insert y (contacts D y x) := by simp [ay,na]
  have four : 4 ≤ bad.card := by
    rw [show bad=insert a (insert y (contacts D y x)) from rfl,
      card_insert_of_not_mem ab,card_insert_of_not_mem yc]
    omega
  have incl : D.neighborFinset a ⊆ univ \ bad := by
    intro v hv
    have h := (mem_neighborFinset D _ _).mp hv
    simp only [mem_sdiff,mem_univ,true_and,bad,mem_insert,not_or]
    exact ⟨h.ne.symm, (fun e => ya (e ▸ h.symm)),fun hb => no_cross D xy none ha hb h⟩
  have h := card_le_card incl
  rw [card_neighborFinset_eq_degree,card_sdiff (subset_univ bad),card_univ,six] at h
  omega

private theorem ripe_neighbor {x y a : W} (xy : x≠y)
    (none : ¬∃ q : D.Walk x y, q.IsPath ∧ 3 ≤ q.length)
    (ha : a ∈ contacts D x y) (hdeg : 3 ≤ D.degree a) :
    ∃ c, D.Adj a c ∧ c≠x ∧ c≠y ∧ c∉contacts D y x := by
  by_contra he
  have bound : D.neighborFinset a ⊆ {x,y} := by
    intro c hc
    have ac := (mem_neighborFinset D _ _).mp hc
    by_cases cx : c=x
    · simp [cx]
    by_cases cy : c=y
    · simp [cy]
    by_cases cb : c∈contacts D y x
    · exact (no_cross D xy none ha cb ac).elim
    · exact (he ⟨c,ac,cx,cy,cb⟩).elim
  have h := card_le_card bound
  rw [card_neighborFinset_eq_degree,card_insert_of_not_mem (by simp [xy]),card_singleton] at h
  omega

private theorem outside_high_has_edge {x y c b : W} (six : Fintype.card W = 6)
    (xy : x≠y) (cx : c≠x) (cy : c≠y) (bx : b≠x) (by' : b≠y) (bc : b≠c)
    (hc : 3≤ D.degree c) (ncx : ¬D.Adj c x) (ncy : ¬D.Adj c y) :
    D.Adj c b := by
  by_contra no
  let bad : Finset W := {b,c,x,y}
  have four : bad.card = 4 := by
    simp [bad,card_insert_of_not_mem,bc,bx,by',cx,cy,xy]
  have incl : D.neighborFinset c ⊆ univ \ bad := by
    intro v hv
    have e := (mem_neighborFinset D _ _).mp hv
    simp only [mem_sdiff,mem_univ,true_and,bad,mem_insert,mem_singleton,not_or]
    exact ⟨fun h => no (h ▸ e),e.ne.symm,fun h => ncx (h ▸ e),fun h => ncy (h ▸ e)⟩
  have h := card_le_card incl
  rw [card_neighborFinset_eq_degree,card_sdiff (subset_univ bad),card_univ,six,four] at h
  omega

private theorem nested_exists {x y : W} (six : Fintype.card W = 6)
    (wide : ∀ a b : W, a ≠ b → 3 ≤ D.degree a ∨ 3 ≤ D.degree b)
    (xy : x≠y) (sub : contacts D x y ⊆ contacts D y x)
    (anyA : (contacts D x y).Nonempty) (twoB : 2 ≤ (contacts D y x).card) :
    ∃ q : D.Walk x y, q.IsPath ∧ 3 ≤ q.length := by
  by_contra none
  obtain ⟨a,ha,high⟩ : ∃ a∈contacts D x y, 3≤D.degree a := by
    obtain ⟨a,ha⟩ := anyA
    by_cases h : 3≤D.degree a
    · exact ⟨a,ha,h⟩
    have xhigh := (wide x a ((contacts_spec D).mp ha).2.ne).resolve_right h
    obtain ⟨b,hb,ba⟩ := Finset.exists_mem_ne (two_contacts_of_high D (y:=y) xhigh) a
    exact ⟨b,hb,(wide b a ba).resolve_right h⟩
  obtain ⟨c,ac,cx,cy,cb⟩ := ripe_neighbor D xy none ha high
  have ncx : ¬D.Adj c x := fun e => cb (sub ((contacts_spec D).2 ⟨cy,e.symm⟩))
  have ncy : ¬D.Adj c y := fun e => cb ((contacts_spec D).2 ⟨cx,e.symm⟩)
  obtain ⟨ay,xa⟩ := (contacts_spec D).mp ha
  by_cases chigh : 3≤D.degree c
  · obtain ⟨b,hb,ba⟩ := Finset.exists_mem_ne twoB a
    have bc : b≠c := fun e => cb (e ▸ hb)
    obtain ⟨bx,yb⟩ := (contacts_spec D).mp hb
    have cb' := outside_high_has_edge D six xy cx cy bx yb.ne.symm bc chigh ncx ncy
    exact none (path4 D xa ac cb' yb.symm cx.symm bx.symm xy ba.symm ay cy)
  · have xhigh := (wide x c cx.symm).resolve_right chigh
    obtain ⟨a',ha',a'a⟩ := Finset.exists_mem_ne (two_contacts_of_high D (y:=y) xhigh) a
    have haB := sub ha'
    obtain ⟨a'x,ya'⟩ := (contacts_spec D).mp haB
    have a'c : a'≠c := fun e => cb (e ▸ haB)
    have a'high := (wide a' c a'c).resolve_right chigh
    obtain ⟨d,a'd,dx,dy,db⟩ := ripe_neighbor D xy none ha' a'high
    by_cases dc : d=c
    · subst d
      exact none (path4 D xa ac a'd.symm ya'.symm cx.symm a'x.symm xy a'a.symm ay cy)
    · have dhigh := (wide d c dc).resolve_right chigh
      have ndx : ¬D.Adj d x := fun e => db (sub ((contacts_spec D).2 ⟨dy,e.symm⟩))
      have ndy : ¬D.Adj d y := fun e => db ((contacts_spec D).2 ⟨dx,e.symm⟩)
      have ad : a≠d := fun e => db (e ▸ sub ha)
      have da := outside_high_has_edge D six xy dx dy xa.ne.symm ay ad dhigh ndx ndy
      exact none (path4 D xa da.symm a'd.symm ya'.symm dx.symm a'x.symm xy a'a.symm ay dy)

/-- In a simple graph on six vertices with no isolated vertices and at most
one vertex of degree below three, any marked pair has a simple path of at
least three edges between it, unless one is a leaf adjacent to the other. -/
theorem six_core_marked_path (six : Fintype.card W = 6)
    (minDeg : ∀ x : W, 1≤D.degree x)
    (wide : ∀ a b : W, a ≠ b → 3 ≤ D.degree a ∨ 3 ≤ D.degree b)
    {x y : W} (xy : x≠y) :
    (∃ q : D.Walk x y,q.IsPath ∧ 3≤q.length) ∨
      D.neighborFinset x={y} ∨ D.neighborFinset y={x} := by
  by_cases h : ∃ q : D.Walk x y,q.IsPath ∧ 3≤q.length
  · exact .inl h
  by_cases hx : D.neighborFinset x={y}
  · exact .inr (.inl hx)
  by_cases hy : D.neighborFinset y={x}
  · exact .inr (.inr hy)
  have anyX := contacts_nonempty D (minDeg x) hx
  have anyY := contacts_nonempty D (minDeg y) hy
  have noRev : ¬∃ q : D.Walk y x,q.IsPath ∧ 3≤q.length :=
    fun e => h ((reverse_exists D).mpr e)
  have ordered {s t : W} (st : s≠t)
      (hs : (contacts D s t).Nonempty) (ht : (contacts D t s).Nonempty)
      (none : ¬∃ q : D.Walk s t,q.IsPath ∧ 3≤q.length)
      (noneR : ¬∃ q : D.Walk t s,q.IsPath ∧ 3≤q.length)
      (th : 3≤D.degree t) : False := by
    have bTwo := two_contacts_of_high D (y:=s) th
    by_cases sub : contacts D s t ⊆ contacts D t s
    · exact none (nested_exists D six wide st sub hs bTwo)
    obtain ⟨a,ha,hab⟩ : ∃ a∈contacts D s t, a∉contacts D t s := by
      by_contra he
      apply sub
      intro a ha
      by_cases hmem : a ∈ contacts D t s
      · exact hmem
      · exact (he ⟨a,ha,hmem⟩).elim
    have alow := exclusive_low D six st none bTwo ha hab
    have as : a≠s := ((contacts_spec D).mp ha).2.ne.symm
    have shigh := (wide a s as).resolve_left (by omega)
    have aTwo := two_contacts_of_high D (y:=t) shigh
    have rev : contacts D t s ⊆ contacts D s t := by
      intro b hb
      by_cases hba : b ∈ contacts D s t
      · exact hba
      exfalso
      have blow := exclusive_low D six st.symm noneR aTwo hb hba
      have ab : a≠b := fun e => hab (e ▸ hb)
      rcases wide a b ab with x|x <;> omega
    exact noneR (nested_exists D six wide st.symm rev ht aTwo)
  exact False.elim ((wide x y xy).elim
    (ordered xy.symm anyY anyX noRev h) (ordered xy anyX anyY h noRev))

/-- In a five-vertex simple graph of minimum degree three, every marked
pair is joined by a simple path of at least three edges. -/
theorem five_core_marked_path (five : Fintype.card W = 5)
    (wide : ∀ a : W, 3 ≤ D.degree a) {x y : W} (xy : x≠y) :
    ∃ q : D.Walk x y,q.IsPath ∧ 3≤q.length := by
  by_contra none
  have noRev : ¬∃ q : D.Walk y x,q.IsPath ∧ 3≤q.length :=
    fun ex => none ((reverse_exists D).mpr ex)
  let A := contacts D x y
  let B := contacts D y x
  have sizeA : 2≤A.card := two_contacts_of_high D (wide x)
  have sizeB : 2≤B.card := two_contacts_of_high D (wide y)
  have incl : A ∪ B ⊆ (univ : Finset W) \ {x,y} := by
    intro a ha
    have h : a≠x ∧ a≠y := by
      rcases mem_union.mp ha with ha|hb
      · obtain ⟨ay,e⟩ := (contacts_spec D).mp ha
        exact ⟨e.ne.symm,ay⟩
      · obtain ⟨ax,e⟩ := (contacts_spec D).mp hb
        exact ⟨ax,e.ne.symm⟩
    simpa using h
  have cap := card_le_card incl
  have two : ({x,y} : Finset W).card=2 := by simp [card_insert_of_not_mem,xy]
  rw [card_sdiff (subset_univ _),card_univ,five,two] at cap
  have sum := card_union_add_card_inter A B
  have common : (A∩B).Nonempty := by
    rw [← card_pos]
    omega
  obtain ⟨a,ha⟩ := common
  have haA := (mem_inter.mp ha).1
  have haB := (mem_inter.mp ha).2
  obtain ⟨c,ac,cx,cy,cb⟩ := ripe_neighbor D xy none haA (wide a)
  have ca : c∉A := fun h => no_cross D xy.symm noRev haB h ac
  have ncx : ¬D.Adj c x := fun e => ca ((contacts_spec D).2 ⟨cy,e.symm⟩)
  have ncy : ¬D.Adj c y := fun e => cb ((contacts_spec D).2 ⟨cx,e.symm⟩)
  let bad : Finset W := {c,x,y}
  have three : bad.card = 3 := by
    simp [bad,card_insert_of_not_mem,cx,cy,xy]
  have inc : D.neighborFinset c ⊆ univ \ bad := by
    intro v hv
    have e := (mem_neighborFinset D _ _).mp hv
    simp only [mem_sdiff,mem_univ,true_and,bad,mem_insert,mem_singleton,not_or]
    exact ⟨e.ne.symm,fun h => ncx (h ▸ e),fun h => ncy (h ▸ e)⟩
  have h := card_le_card inc
  rw [card_neighborFinset_eq_degree,card_sdiff (subset_univ bad),card_univ,five,three] at h
  have := wide c
  omega

#print axioms six_core_marked_path
#print axioms five_core_marked_path
end Graffiti189SixCore
