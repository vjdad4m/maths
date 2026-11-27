import ThreeSide189
import Mathlib.Data.Finset.Sum

namespace Graffiti189LongestPath.FourCut.Three
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

structure SingleRoot (G : SimpleGraph V) [DecidableRel G.Adj] (r a b : V) where
  con : G.Connected
  ab : a≠b
  left : G.Adj r a
  right : G.Adj r b
  only : ∀ x, G.Adj r x → x=a ∨ x=b
  even : ∀ x, (EvenFrom G x).card≤5

namespace SingleRoot
variable {r a b : V} (S : SingleRoot G r a b)
def off3 (_ : SingleRoot G r a b) : Finset V := univ \ {r,a,b}
def ports : Finset V := S.off3.filter (fun x=>G.Adj a x ∨ G.Adj b x)
def inner : Finset V := S.off3 \ S.ports
noncomputable def shells (_ : SingleRoot G r a b) : Finset (V ⊕ V) :=
  (DistanceTwo G a).disjSum (DistanceTwo G b)
noncomputable def tags : Finset (V ⊕ V) :=
  (S.inner.filter (· ∈ DistanceTwo G a)).disjSum (S.inner.filter (· ∈ DistanceTwo G b))

lemma mem_off3 {x : V} : x∈S.off3 ↔ x≠r ∧ x≠a ∧ x≠b := by
  simp [off3,not_or]
lemma mem_inner {x : V} : x∈S.inner ↔ x∈S.off3 ∧ ¬ G.Adj a x ∧ ¬ G.Adj b x := by
  by_cases h : x∈S.off3 <;> simp [inner,ports,h]

lemma ports_sub : S.ports ⊆ DistanceTwo G r := by
  intro x hx
  obtain ⟨h,ha|hb⟩ := mem_filter.mp hx
  all_goals
    obtain ⟨xr,xa,xb⟩ := S.mem_off3.mp h
    have nrx : ¬G.Adj r x := fun rx=>(S.only x rx).elim xa xb
  · exact Sides.mem_d2.mpr (Sides.dist_two S.con xr.symm nrx S.left ha)
  · exact Sides.mem_d2.mpr (Sides.dist_two S.con xr.symm nrx S.right hb)

lemma near (four : S.ports.card=4) (x : V) : G.dist r x≤3 := by
  by_contra! h
  have cap := S.even r
  have big := distanceTwo_add_two_le_even_of_far S.con (show 4≤G.dist r x by omega)
  have sub := card_le_card S.ports_sub
  omega

lemma adjacent_to_port (four : S.ports.card=4) {x : V} (xi : x∈S.inner) :
    ∃ y∈S.ports, G.Adj x y := by
  obtain ⟨hi,na,nb⟩ := S.mem_inner.mp xi
  obtain ⟨xr,xa,xb⟩ := S.mem_off3.mp hi
  have rx : ¬G.Adj r x := fun rx=>(S.only x rx).elim xa xb
  have last {y : V} (yx : G.Adj y x) (hit : G.Adj a y ∨ G.Adj b y) :
      y∈S.ports := by
    have hy : y≠r ∧ y≠a ∧ y≠b :=
      ⟨fun e=>rx (e ▸ yx),fun e=>na (e ▸ yx),fun e=>nb (e ▸ yx)⟩
    exact mem_filter.mpr ⟨S.mem_off3.mpr hy,hit⟩
  obtain ⟨q,qe⟩ := S.con.exists_walk_length_eq_dist r x
  have upper : q.length≤3 := qe ▸ S.near four x
  cases q with
  | nil => exact (xr rfl).elim
  | @cons r t x rt q =>
    rcases S.only t rt with rfl|rfl
    all_goals
      cases q with
      | nil => exact (rx rt).elim
      | @cons u y x uy q =>
        cases q with
        | nil => exact (by first | exact (na uy).elim | exact (nb uy).elim)
        | @cons y z x yz q =>
          cases q with
          | nil =>
            first
            | exact ⟨y,last yz (Or.inl uy),yz.symm⟩
            | exact ⟨y,last yz (Or.inr uy),yz.symm⟩
          | cons => simp [Walk.length_cons] at upper

lemma inner_cover (four : S.ports.card=4) {x : V} (xi : x∈S.inner) :
    x∈DistanceTwo G a ∨ x∈DistanceTwo G b := by
  obtain ⟨hi,na,nb⟩ := S.mem_inner.mp xi
  obtain ⟨_,xa,xb⟩ := S.mem_off3.mp hi
  obtain ⟨y,hy,xy⟩ := S.adjacent_to_port four xi
  rcases (mem_filter.mp hy).2 with ay|by'
  · exact Or.inl (Sides.mem_d2.mpr (Sides.dist_two S.con xa.symm na ay xy.symm))
  · exact Or.inr (Sides.mem_d2.mpr (Sides.dist_two S.con xb.symm nb by' xy.symm))

lemma tags_count (four : S.ports.card=4) : S.inner.card≤S.tags.card := by
  have eq : S.inner.filter (· ∈ DistanceTwo G a) ∪ S.inner.filter (· ∈ DistanceTwo G b) = S.inner := by
    ext x
    simp only [mem_union,mem_filter]
    refine ⟨fun hx => hx.elim And.left And.left,?_⟩
    intro hx
    exact (S.inner_cover four hx).elim (fun e=>Or.inl ⟨hx,e⟩) (fun e=>Or.inr ⟨hx,e⟩)
  have h := card_union_le (S.inner.filter (· ∈ DistanceTwo G a)) (S.inner.filter (· ∈ DistanceTwo G b))
  rw [eq] at h
  simpa [tags,card_disjSum] using h

lemma tags_sub : S.tags⊆S.shells := by
  intro z hz
  cases z with
  | inl x => exact inl_mem_disjSum.mpr (mem_filter.mp (inl_mem_disjSum.mp hz)).2
  | inr x => exact inr_mem_disjSum.mpr (mem_filter.mp (inr_mem_disjSum.mp hz)).2

lemma shells_card : S.shells.card≤8 := by
  rw [shells,card_disjSum]
  have da := distanceTwo_le_of_even 4 a (S.even a)
  have db := distanceTwo_le_of_even 4 b (S.even b)
  omega

lemma total_card (four : S.ports.card=4) : Fintype.card V = S.inner.card+7 := by
  have f := card_sdiff_add_card_eq_card (filter_subset _ S.off3)
    (s := S.ports) (t := S.off3)
  have total := card_sdiff_add_card_eq_card
    (show ({r,a,b}:Finset V)⊆univ from subset_univ _)
  change S.off3.card+({r,a,b}:Finset V).card=univ.card at total
  change S.inner.card + S.ports.card = S.off3.card at f
  have cf : ({r,a,b}:Finset V).card=3 := by simp [S.left.ne,S.right.ne,S.ab]
  rw [cf,card_univ] at total
  omega

/-- A degree-two root with four distinct second-layer contacts makes the
degree-four even-distance case a graph of order at most fifteen. -/
theorem order_le_fifteen (four : S.ports.card=4) : Fintype.card V≤15 := by
  have t := S.total_card four
  have k := S.tags_count four
  have b := (card_le_card S.tags_sub).trans S.shells_card
  omega

/-- If the two neighbors of the root are nonadjacent, their mutual distance
two consumes two shell slots, dropping the order cutoff to thirteen. -/
theorem order_le_thirteen_of_nonadj (four : S.ports.card=4) (e : ¬G.Adj a b) :
    Fintype.card V≤13 := by
  have dh : b∈DistanceTwo G a := Sides.mem_d2.mpr (Sides.dist_two S.con S.ab e S.left.symm S.right)
  have dt : a∈DistanceTwo G b := Sides.mem_d2.mpr (Sides.dist_two S.con S.ab.symm
    (fun h=>e h.symm) S.right.symm S.left)
  have na : a∉S.inner := fun h => (S.mem_off3.mp (S.mem_inner.mp h).1).2.1 rfl
  have nb : b∉S.inner := fun h => (S.mem_off3.mp (S.mem_inner.mp h).1).2.2 rfl
  have nt : Sum.inl b ∉ S.tags := fun h => nb (mem_filter.mp (inl_mem_disjSum.mp h)).1
  have nu : Sum.inr a ∉ S.tags := fun h => na (mem_filter.mp (inr_mem_disjSum.mp h)).1
  have nlast : Sum.inl b ∉ insert (Sum.inr a) S.tags := by simp [nt]
  have sub : insert (Sum.inl b) (insert (Sum.inr a) S.tags) ⊆ S.shells :=
    insert_subset_iff.mpr ⟨inl_mem_disjSum.mpr dh,
      insert_subset_iff.mpr ⟨inr_mem_disjSum.mpr dt,S.tags_sub⟩⟩
  have cap := (card_le_card sub).trans S.shells_card
  rw [card_insert_of_not_mem nlast,card_insert_of_not_mem nu] at cap
  have t := S.total_card four
  have k := S.tags_count four
  omega

lemma cap_from_extras (four : S.ports.card=4) {x y : V ⊕ V}
    (ne : x≠y) (xs : x∈S.shells) (ys : y∈S.shells)
    (xt : x∉S.tags) (yt : y∉S.tags) : Fintype.card V≤13 := by
  have nr : x∉insert y S.tags := by simp [ne,xt]
  have sub : insert x (insert y S.tags) ⊆ S.shells :=
    insert_subset_iff.mpr ⟨xs,insert_subset_iff.mpr ⟨ys,S.tags_sub⟩⟩
  have cap := (card_le_card sub).trans S.shells_card
  rw [card_insert_of_not_mem nr,card_insert_of_not_mem yt] at cap
  have t := S.total_card four
  have k := S.tags_count four
  omega

theorem order_le_eleven_of_common (four : S.ports.card=4)
    (common : (∀ y∈S.ports, G.Adj a y) ∨ (∀ y∈S.ports, G.Adj b y)) : Fintype.card V≤11 := by
  have k : S.inner.card≤4 := by
    rcases common with A|B
    · apply (card_le_card (t:=DistanceTwo G a) ?_).trans (distanceTwo_le_of_even 4 a (S.even a))
      intro x xi
      obtain ⟨hi,na,_⟩ := S.mem_inner.mp xi
      obtain ⟨_,xa,_⟩ := S.mem_off3.mp hi
      obtain ⟨y,hy,xy⟩ := S.adjacent_to_port four xi
      exact Sides.mem_d2.mpr (Sides.dist_two S.con xa.symm na (A _ hy) xy.symm)
    · apply (card_le_card (t:=DistanceTwo G b) ?_).trans (distanceTwo_le_of_even 4 b (S.even b))
      intro x xi
      obtain ⟨hi,_,nb⟩ := S.mem_inner.mp xi
      obtain ⟨_,_,xb⟩ := S.mem_off3.mp hi
      obtain ⟨y,hy,xy⟩ := S.adjacent_to_port four xi
      exact Sides.mem_d2.mpr (Sides.dist_two S.con xb.symm nb (B _ hy) xy.symm)
  have t := S.total_card four
  omega

/-- The four total attachments force order at most thirteen regardless of
whether the two cut vertices are adjacent. -/
theorem order_le_thirteen (four : S.ports.card=4) : Fintype.card V≤13 := by
  by_cases edge : G.Adj a b
  · by_cases c : (∀ y∈S.ports, G.Adj a y) ∨ (∀ y∈S.ports, G.Adj b y)
    · exact (S.order_le_eleven_of_common four c).trans (by decide)
    · push_neg at c
      obtain ⟨u,up,ua⟩ := c.1
      obtain ⟨v,vp,vb⟩ := c.2
      have ub := ((mem_filter.mp up).2).resolve_left ua
      have va := ((mem_filter.mp vp).2).resolve_right vb
      have une : a≠u := (S.mem_off3.mp (mem_filter.mp up).1).2.1.symm
      have vne : b≠v := (S.mem_off3.mp (mem_filter.mp vp).1).2.2.symm
      have us : Sum.inl u ∈ S.shells := inl_mem_disjSum.mpr (Sides.mem_d2.mpr (Sides.dist_two S.con une ua edge ub))
      have vs : Sum.inr v ∈ S.shells := inr_mem_disjSum.mpr (Sides.mem_d2.mpr (Sides.dist_two S.con vne vb edge.symm va))
      have un : Sum.inl u ∉ S.tags := fun h => (mem_sdiff.mp (mem_filter.mp (inl_mem_disjSum.mp h)).1).2 up
      have vn : Sum.inr v ∉ S.tags := fun h => (mem_sdiff.mp (mem_filter.mp (inr_mem_disjSum.mp h)).1).2 vp
      exact S.cap_from_extras four (x:=Sum.inl u) (y:=Sum.inr v) (by simp) us vs un vn
  · exact S.order_le_thirteen_of_nonadj four edge

noncomputable def exclusiveTags : Finset (V ⊕ V) :=
  (S.ports.filter (fun u=> ¬G.Adj a u)).disjSum (S.ports.filter (fun u=> ¬G.Adj b u))

theorem order_plus_exclusive_le_fifteen (four : S.ports.card=4) (edge : G.Adj a b) :
    Fintype.card V + S.exclusiveTags.card ≤ 15 := by
  have dis : Disjoint S.tags S.exclusiveTags := by
    apply disjoint_left.mpr
    intro w wt we
    cases w with
    | inl u =>
      exact (mem_sdiff.mp (mem_filter.mp (inl_mem_disjSum.mp wt)).1).2
        (mem_filter.mp (inl_mem_disjSum.mp we)).1
    | inr u =>
      exact (mem_sdiff.mp (mem_filter.mp (inr_mem_disjSum.mp wt)).1).2
        (mem_filter.mp (inr_mem_disjSum.mp we)).1
  have other : S.exclusiveTags ⊆ S.shells := by
    intro w hw
    cases w with
    | inl u =>
      obtain ⟨up,ua⟩ := mem_filter.mp (inl_mem_disjSum.mp hw)
      have ub := (mem_filter.mp up).2.resolve_left ua
      have une : a≠u := (S.mem_off3.mp (mem_filter.mp up).1).2.1.symm
      exact inl_mem_disjSum.mpr (Sides.mem_d2.mpr (Sides.dist_two S.con une ua edge ub))
    | inr u =>
      obtain ⟨up,ub⟩ := mem_filter.mp (inr_mem_disjSum.mp hw)
      have ua := (mem_filter.mp up).2.resolve_right ub
      have une : b≠u := (S.mem_off3.mp (mem_filter.mp up).1).2.2.symm
      exact inr_mem_disjSum.mpr (Sides.mem_d2.mpr (Sides.dist_two S.con une ub edge.symm ua))
  have h := (card_le_card (union_subset S.tags_sub other)).trans S.shells_card
  rw [card_union_of_disjoint dis] at h
  have k := S.tags_count four
  have t := S.total_card four
  omega

#print axioms order_plus_exclusive_le_fifteen
#print axioms order_le_thirteen
#print axioms order_le_fifteen
#print axioms order_le_thirteen_of_nonadj
end SingleRoot
end Graffiti189LongestPath.FourCut.Three
