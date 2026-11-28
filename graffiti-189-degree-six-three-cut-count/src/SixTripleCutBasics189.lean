import CrossSaturation189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
open scoped BigOperators
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

def ThreeConnected (G : SimpleGraph V) : Prop :=
  ∀ R : Finset V,R.card<3 → (G.induce ((↑R : Set V)ᶜ)).Connected

structure Shore (G : SimpleGraph V) (S A : Finset V) : Prop where
  nonempty : A.Nonempty
  disjoint : Disjoint A S
  closed : ∀ x∈A,∀ y,G.Adj x y → y∈A ∨ y∈S

def ports (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (a : V) :=
  A.filter (G.Adj a)

def visible (G : SimpleGraph V) [DecidableRel G.Adj] (S A : Finset V) : Finset V :=
  A.filter (fun a => ∃ b∈S,G.Adj a b)

noncomputable def localTwo (G : SimpleGraph V) (A : Finset V) (a : V) :=
  A ∩ DistanceTwo G a

theorem two_of_common (hc : G.Connected) {x y z : V} (xz : x≠z)
    (na : ¬G.Adj x z) (xy : G.Adj x y) (yz : G.Adj y z) :
    z ∈ DistanceTwo G x := by
  classical
  have h := hc.one_lt_dist_of_ne_of_not_adj xz na
  have le := G.dist_le (Walk.cons xy (Walk.cons yz .nil))
  simp at le
  simp [DistanceTwo,show G.dist x z=2 by omega]

private theorem no_invariant_shore {R A : Finset V}
    (h : (G.induce ((↑R : Set V)ᶜ)).Connected)
    {a b : V} (ha : a∈A) (hb : b∉A) (ar : a∉R) (br : b∉R)
    (cl : ∀ x∈A,∀ y,G.Adj x y → y∉R → y∈A) : False := by
  let X := ((↑R : Set V)ᶜ)
  obtain ⟨p⟩ := h.preconnected (⟨a,ar⟩ : X) (⟨b,br⟩ : X)
  have prop {x y : X} (q : (G.induce X).Walk x y) : x.val∈A → y.val∈A := by
    induction q with
    | nil => exact id
    | @cons x z y e p ih =>
      intro xm
      exact ih (cl x.val xm z.val e z.property)
  exact hb (prop p ha)

theorem Shore.hit {S A : Finset V} (sh : Shore G S A) (ss : S.card=3)
    (conn : ThreeConnected G) {t : V} (ts : t∈S) :
    ∃ x∈A,G.Adj t x := by
  classical
  by_contra! no
  obtain ⟨a,aa⟩ := sh.nonempty
  let R := S.erase t
  refine no_invariant_shore (conn R (by dsimp [R]; rw [card_erase_of_mem ts]; omega))
    aa (fun v => disjoint_left.mp sh.disjoint v ts) ?_ ?_ ?_
  · exact fun z => disjoint_left.mp sh.disjoint aa (mem_erase.mp z).2
  · exact fun z => (mem_erase.mp z).1 rfl
  · intro x xm y e yr
    rcases sh.closed x xm y e with ya|ys
    · exact ya
    · by_cases yt : y=t
      · exact (no x xm (yt ▸ e.symm)).elim
      · exact (yr (mem_erase.mpr ⟨yt,ys⟩)).elim

theorem Shore.degree_bound {S A : Finset V} (sh : Shore G S A)
    {v : V} (vm : v∈A) :
    G.degree v≤A.card-1+S.card := by
  have sub : G.neighborFinset v⊆A.erase v ∪ S := by
    intro w wm
    have e := (G.mem_neighborFinset ..).mp wm
    rcases sh.closed v vm w e with wa|ws
    · exact mem_union_left _ (mem_erase.mpr ⟨e.ne.symm,wa⟩)
    · exact mem_union_right _ ws
  have c := (card_le_card sub).trans (card_union_le _ _)
  rwa [card_neighborFinset_eq_degree,card_erase_of_mem vm] at c

theorem Shore.visible_lower {S A : Finset V} (sh : Shore G S A)
    (ss : S.card=3) (conn : ThreeConnected G) (aa : 3≤A.card) :
    3≤(visible G S A).card := by
  classical
  by_contra! small
  let R := visible G S A
  have n : (A\R).Nonempty := by
    apply card_pos.mp
    have incl : R⊆A := filter_subset _ _
    rw [card_sdiff incl]
    change R.card<3 at small
    omega
  obtain ⟨u,um⟩ := n
  obtain ⟨ua,ur⟩ := mem_sdiff.mp um
  obtain ⟨s,sm⟩ := card_pos.mp (show 0<S.card by omega)
  have sa : s∉A := fun z => disjoint_left.mp sh.disjoint z sm
  refine no_invariant_shore (conn R small) um
    (fun h => sa (mem_sdiff.mp h).1) ur (fun z => sa ((mem_filter.mp z).1)) ?_
  intro x hx y xy yr
  obtain ⟨xa,xR⟩ := mem_sdiff.mp hx
  rcases sh.closed x xa y xy with ya|ys
  · exact mem_sdiff.mpr ⟨ya,yr⟩
  · exact (xR (mem_filter.mpr ⟨xa,y,ys,xy⟩)).elim

theorem Shore.port_cost {S A : Finset V} (sh : Shore G S A) (hc : G.Connected)
    (ss : S.card=3) {a x : V} (aS : a∈S) (xp : x∈ports G A a) :
    G.degree x≤(ports G A a).card+(localTwo G A a).card+2 := by
  classical
  let P := ports G A a
  let Q := localTwo G A a
  let M := P∪Q
  have px : x∈M := mem_union_left _ xp
  have sub : G.neighborFinset x⊆insert a (M.erase x ∪ S.erase a) := by
    intro y ym
    have xy := (G.mem_neighborFinset ..).mp ym
    by_cases ya : y=a
    · exact mem_insert.mpr (Or.inl ya)
    apply mem_insert_of_mem
    rcases sh.closed x (mem_filter.mp xp).1 y xy with yA|yS
    · apply mem_union_left _
      refine mem_erase.mpr ⟨xy.ne.symm,?_⟩
      by_cases ay : G.Adj a y
      · exact mem_union_left _ (mem_filter.mpr ⟨yA,ay⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨yA,two_of_common hc (Ne.symm ya) ay (mem_filter.mp xp).2 xy⟩)
    · exact mem_union_right _ (mem_erase.mpr ⟨ya,yS⟩)
  have c := card_le_card sub
  rw [card_neighborFinset_eq_degree] at c
  have dep := card_insert_le a (M.erase x ∪ S.erase a)
  have hu := card_union_le (M.erase x) (S.erase a)
  have hm := card_union_le P Q
  change M.card≤P.card+Q.card at hm
  rw [card_erase_of_mem px,card_erase_of_mem aS,ss] at hu
  have pos := card_pos.mpr ⟨x,px⟩
  change G.degree x≤P.card+Q.card+2
  omega

theorem Shore.foreign_distance_two {S A B : Finset V} (sh : Shore G S A)
    (bsh : Shore G S B) (dis : Disjoint A B) (hc : G.Connected)
    {t x y : V} (xt : x∈ports G A t) (yt : y∈ports G B t) :
    y∈DistanceTwo G x := by
  obtain ⟨xa,tx⟩ := mem_filter.mp xt
  obtain ⟨yb,ty⟩ := mem_filter.mp yt
  have ne : x≠y := fun e => disjoint_left.mp dis xa (e ▸ yb)
  have na : ¬G.Adj x y := fun e =>
    (sh.closed x xa y e).elim (fun h => disjoint_left.mp dis h yb)
      (fun h => disjoint_left.mp bsh.disjoint yb h)
  exact two_of_common hc ne na tx.symm ty

#print axioms Shore.hit
#print axioms Shore.degree_bound
#print axioms Shore.visible_lower
#print axioms Shore.port_cost
#print axioms Shore.foreign_distance_two
end Graffiti189LongestPath.ThresholdSix.ThreeCut
