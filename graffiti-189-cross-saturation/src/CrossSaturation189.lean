import SmallSeparator189
namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

structure Split (G : SimpleGraph V) (a b : V) where
  L : Finset V
  R : Finset V
  dis : Disjoint L R
  leftOff : a ∉ L ∧ b ∉ L
  rightOff : a ∉ R ∧ b ∉ R
  leftConnected : (G.induce (↑L : Set V)).Connected
  cross : ∀ x∈L, ∀ y∈R, ¬G.Adj x y
  leftA : ∃ x∈L, G.Adj a x
  leftB : ∃ x∈L, G.Adj b x
  cover : ∀ z : V, z=a ∨ z=b ∨ z∈L ∨ z∈R

namespace Split
variable {a b : V} (S : Split G a b)
def foreignA : Finset V := S.R.filter (G.Adj a)
def localA : Finset V := S.L.filter (G.Adj a)

private theorem d2 {x y z : V} (hc : G.Connected) (xz : x≠z)
    (na : ¬G.Adj x z) (xy : G.Adj x y) (yz : G.Adj y z) :
    z ∈ DistanceTwo G x := by
  classical
  have h := hc.one_lt_dist_of_ne_of_not_adj xz na
  have le := G.dist_le (Walk.cons xy (Walk.cons yz .nil))
  simp at le
  simp [DistanceTwo, show G.dist x z=2 by omega]

private theorem foreign_subset (hc : G.Connected) {x : V}
    (xl : x∈S.L) (ax : G.Adj a x) : S.foreignA ⊆ DistanceTwo G x := by
  intro z hz
  obtain ⟨zr,az⟩ := mem_filter.mp hz
  exact d2 hc (fun e=>disjoint_left.mp S.dis xl (e ▸ zr))
    (S.cross x xl z zr) ax.symm az

private theorem local_card (d : ℕ) (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ d + 1) (nonempty : S.foreignA.Nonempty) :
    S.localA.card ≤ d := by
  obtain ⟨z,hz⟩ := nonempty
  obtain ⟨zr,az⟩ := mem_filter.mp hz
  have sub : S.localA ⊆ DistanceTwo G z := by
    intro x hx
    obtain ⟨xl,ax⟩ := mem_filter.mp hx
    exact d2 hc (fun e=>disjoint_left.mp S.dis xl (e ▸ zr))
      (fun e=>S.cross x xl z zr e.symm) az.symm ax
  exact (card_le_card sub).trans (distanceTwo_le_of_even d z (even z))

private theorem reaches_all_left (hc : G.Connected) {x : V}
    (xl : x∈S.L) (sat : DistanceTwo G x = S.foreignA)
    {y : V} (yl : y∈S.L) : y=x ∨ G.Adj x y := by
  let xl' : ↑(↑S.L : Set V) := ⟨x,xl⟩
  let yl' : ↑(↑S.L : Set V) := ⟨y,yl⟩
  obtain ⟨p⟩ := S.leftConnected.preconnected xl' yl'
  have walk_step {u v : ↑(↑S.L : Set V)} (q : (G.induce (↑S.L : Set V)).Walk u v) :
      (u.val=x ∨ G.Adj x u.val) → (v.val=x ∨ G.Adj x v.val) := by
    induction q with
    | nil => exact id
    | @cons t u v tu q ih =>
        intro ht
        apply ih
        by_cases ux : u.val=x
        · exact Or.inl ux
        right
        change G.Adj t.val u.val at tu
        rcases ht with tx|xt
        · exact tx ▸ tu
        by_contra bad
        have ud := d2 hc (Ne.symm ux) bad xt tu
        rw [sat] at ud
        exact (disjoint_left.mp S.dis u.property (mem_filter.mp ud).1).elim
  exact walk_step p (Or.inl rfl)

private theorem no_far (d : ℕ) (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ d + 1)
    {x : V} (sat : DistanceTwo G x = S.foreignA) (four : S.foreignA.card=d) :
    ∀ y, G.dist x y ≤ 3 := by
  intro y
  by_contra bad
  have far := distanceTwo_add_two_le_even_of_far hc (x:=x) (y:=y) (by omega)
  rw [sat,four] at far
  have e := even x
  omega

private theorem first_step {x y : V} (xl : x∈S.L) (xy : G.Adj x y) :
    y=a ∨ y=b ∨ y∈S.L := by
  rcases S.cover y with rfl|rfl|yl|yr
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr yl)
  · exact (S.cross x xl y yr xy).elim

private theorem final_step {x y : V} (yr : y∈S.R) (xy : G.Adj x y) :
    x=a ∨ x=b ∨ x∈S.R := by
  rcases S.cover x with rfl|rfl|xl|xr
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact (S.cross x xl y yr xy).elim
  · exact Or.inr (Or.inr xr)

private theorem few_steps {x y : V} (xl : x∈S.L) (yr : y∈S.R)
    (q : G.Walk x y) (short : q.length ≤ 3) :
    (G.Adj a y ∨ G.Adj b y) ∨
      ∃ z∈S.R, (G.Adj a z ∨ G.Adj b z) ∧ G.Adj z y := by
  have direct (v : V) (e : v=a ∨ v=b) (vy : G.Adj v y) :
      G.Adj a y ∨ G.Adj b y := by rcases e with rfl|rfl; exact Or.inl vy; exact Or.inr vy
  cases q with
  | nil => exact (disjoint_left.mp S.dis xl yr).elim
  | @cons x t y xt q =>
    have tf := first_step S xl xt
    cases q with
    | nil => exact (S.cross _ xl _ yr xt).elim
    | @cons t u y tu q =>
      cases q with
      | nil =>
        left
        rcases tf with ta|tb|tl
        · exact direct t (Or.inl ta) tu
        · exact direct t (Or.inr tb) tu
        · exact (S.cross _ tl _ yr tu).elim
      | @cons u v y uv q =>
        have qzero : q.length=0 := by simp at short; omega
        cases q with
        | nil =>
          have uf := final_step S yr uv
          rcases uf with ua|ub|ur
          · exact Or.inl (direct u (Or.inl ua) uv)
          · exact Or.inl (direct u (Or.inr ub) uv)
          · right
            refine ⟨u,ur,?_,uv⟩
            rcases tf with rfl|rfl|tl
            · exact Or.inl tu
            · exact Or.inr tu
            · exact (S.cross _ tl _ ur tu).elim
        | cons => simp at qzero

theorem order_le_three_times_budget_plus_two (d : ℕ) (positive : 0 < d) (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ d + 1) (four : S.foreignA.card=d) :
    Fintype.card V ≤ 3*d+2 := by
  classical
  obtain ⟨x,xl,ax⟩ := S.leftA
  have sub := foreign_subset S hc xl ax
  have dcap := distanceTwo_le_of_even d x (even x)
  have sat : DistanceTwo G x = S.foreignA :=
    (eq_of_subset_of_card_le sub (by omega)).symm
  have univL (y : V) (yl : y∈S.L) := reaches_all_left S hc xl sat yl
  have bx : G.Adj b x := by
    obtain ⟨y,yl,by'⟩ := S.leftB
    rcases univL y yl with rfl|xy
    · exact by'
    by_contra bad
    have e := d2 (x:=x) (z:=b) hc (fun ee=> S.leftOff.2 (ee ▸ xl)) (fun e=>bad e.symm) xy by'.symm
    rw [sat] at e
    exact S.rightOff.2 (mem_filter.mp e).1
  have included (z : V) (zr : z∈S.R) (bz : G.Adj b z) : G.Adj a z := by
    have e := d2 (x:=x) (z:=z) hc (fun ee=>disjoint_left.mp S.dis xl (ee ▸ zr))
      (S.cross _ xl _ zr) bx.symm bz
    rw [sat] at e
    exact (mem_filter.mp e).2
  have lc := local_card S d hc even (card_pos.mp (by omega))
  have dc := distanceTwo_le_of_even d a (even a)
  have covered : (univ : Finset V) ⊆ insert a (insert b ((S.localA ∪ S.foreignA) ∪ DistanceTwo G a)) := by
    intro z _
    rcases S.cover z with rfl|rfl|zl|zr
    · simp
    · simp
    all_goals
      simp only [mem_insert,mem_union]
      right; right
    · by_cases az : G.Adj a z
      · exact Or.inl (Or.inl (mem_filter.mpr ⟨zl,az⟩))
      right
      rcases univL z zl with rfl|xz
      · exact (az ax).elim
      · exact d2 hc (fun e=>S.leftOff.1 (e ▸ zl)) az ax xz
    · obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist x z
      have short := no_far S d hc even sat four z
      rcases few_steps S xl zr q (by omega) with p|⟨w,wr,p,wz⟩
      · exact Or.inl (Or.inr (mem_filter.mpr ⟨zr,p.elim id (included z zr)⟩))
      · by_cases az : G.Adj a z
        · exact Or.inl (Or.inr (mem_filter.mpr ⟨zr,az⟩))
        · exact Or.inr (d2 hc (fun e=>S.rightOff.1 (e ▸ zr)) az
            (p.elim id (included w wr)) wz)
  have c := card_le_card covered
  rw [card_univ] at c
  have c1 := card_insert_le a (insert b ((S.localA ∪ S.foreignA) ∪ DistanceTwo G a))
  have c2 := card_insert_le b ((S.localA ∪ S.foreignA) ∪ DistanceTwo G a)
  have c3 := card_union_le (S.localA ∪ S.foreignA) (DistanceTwo G a)
  have c4 := card_union_le S.localA S.foreignA
  omega
theorem order_le_fourteen_of_four_shared_ports (hc : G.Connected)
    (even : ∀ x, (EvenFrom G x).card ≤ 5) (four : S.foreignA.card=4) :
    Fintype.card V ≤ 14 :=
  order_le_three_times_budget_plus_two S 4 (by decide) hc even four

#print axioms order_le_three_times_budget_plus_two
#print axioms order_le_fourteen_of_four_shared_ports
end Split
end Graffiti189LongestPath.CrossSaturation
