import SixCutFar189
import TwoCutOrderCenters189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore mem_shore shore_off shore_closed shore_disjoint shore_connected shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private Cmp DeletionConnected split_at_shore aPorts bPorts aTwos bTwos two_local_counts three_local_counts
  from SixCutFar189
open private d2 foreign_subset reaches_all_left from CrossSaturation189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

private theorem three_shores (big : 3≤Nat.card (Cmp G a b)) :
    ∃ C D E : Cmp G a b,C≠D ∧ C≠E ∧ D≠E := by
  let J := CutGraph (G:=G) a b
  haveI : Finite (Cmp G a b) := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype (Cmp G a b) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at big
  let F := Fintype.equivFin (Cmp G a b)
  let C := F.symm ⟨0,by omega⟩
  let D := F.symm ⟨1,by omega⟩
  let E := F.symm ⟨2,by omega⟩
  exact ⟨C,D,E,
    fun z=>(by decide : (0:Nat)≠1) (congrArg Fin.val (F.symm.injective z)),
    fun z=>(by decide : (0:Nat)≠2) (congrArg Fin.val (F.symm.injective z)),
    fun z=>(by decide : (1:Nat)≠2) (congrArg Fin.val (F.symm.injective z))⟩

private theorem port_cost (hc : G.Connected) (C : Cmp G a b)
    {x : V} (xp : x∈aPorts C) :
    G.degree x ≤ (aPorts C).card + (aTwos C).card + if G.Adj b x then 1 else 0 := by
  classical
  obtain ⟨xc,ax⟩ := mem_filter.mp xp
  let R := ((aPorts C).erase x) ∪ aTwos C
  let B := if G.Adj b x then ({b} : Finset V) else ∅
  have sub : G.neighborFinset x ⊆ insert a (R ∪ B) := by
    intro z hz
    have xz := (mem_neighborFinset G x z).mp hz
    rcases shore_closed C x xc z xz with rfl|rfl|zc
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_union_right _ (by simp [B,xz.symm]))
    by_cases az : G.Adj a z
    · exact mem_insert_of_mem (mem_union_left _ (mem_union_left _ (mem_erase.mpr
        ⟨xz.ne.symm,mem_filter.mpr ⟨zc,az⟩⟩)))
    have anz : a≠z := fun h=>(shore_off C).1 (h.symm ▸ zc)
    exact mem_insert_of_mem (mem_union_left _ (mem_union_right _
      (mem_inter.mpr ⟨zc,d2 hc anz az ax xz⟩)))
  have n := card_le_card sub
  rw [card_neighborFinset_eq_degree] at n
  have i := card_insert_le a (R∪B)
  have u := card_union_le R B
  have r := card_union_le ((aPorts C).erase x) (aTwos C)
  change R.card ≤ ((aPorts C).erase x).card + (aTwos C).card at r
  have c := card_erase_add_one xp
  have j : B.card = if G.Adj b x then 1 else 0 := by by_cases p : G.Adj b x <;> simp [B,p]
  omega

private theorem distinct_shore_ports_dis {C D : Cmp G a b} (cd : C≠D) :
    Disjoint (aPorts C) (aPorts D) :=
  (shore_disjoint cd).mono (filter_subset _ _) (filter_subset _ _)

private theorem distinct_shore_twos_dis {C D : Cmp G a b} (cd : C≠D) :
    Disjoint (aTwos C) (aTwos D) := (shore_disjoint cd).mono inter_subset_left inter_subset_left

private theorem each_foreign_port_is_distance_two (hc : G.Connected)
    {C D : Cmp G a b} (cd : C≠D) {x z : V}
    (xp : x∈aPorts C) (zp : z∈aPorts D) : z∈DistanceTwo G x := by
  obtain ⟨xc,ax⟩ := mem_filter.mp xp
  obtain ⟨zd,az⟩ := mem_filter.mp zp
  have no : z∉Shore C := fun zc=>disjoint_left.mp (shore_disjoint cd) zc zd
  have ne : x≠z := fun e=>no (e ▸ xc)
  have nx : ¬G.Adj x z := by
    intro q
    rcases shore_closed C x xc z q with h|h|h
    · exact (shore_off D).1 (h ▸ zd)
    · exact (shore_off D).2 (h ▸ zd)
    exact no h
  exact d2 hc ne nx ax.symm az

private theorem two_foreign_ports_budget (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤7) {C D E : Cmp G a b}
    (cd : C≠D) (ce : C≠E) (de : D≠E) {x : V} (xp : x∈aPorts C) :
    (aPorts D).card+(aPorts E).card≤6 :=
  (two_local_counts _ _ (distinct_shore_ports_dis de) _ (fun _=>each_foreign_port_is_distance_two hc cd xp)
    (fun _=>each_foreign_port_is_distance_two hc ce xp)).trans (distanceTwo_le_of_even 6 x (even x))

private theorem local_universal_of_two_foreign_saturation (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤7) (ab : a≠b) (conn : DeletionConnected G)
    {C D E : Cmp G a b} (cd : C≠D) (ce : C≠E) (de : D≠E)
    {x : V} (xp : x∈aPorts C)
    (six : (aPorts D).card+(aPorts E).card=6) :
    ∀ z∈Shore C,z=x ∨ G.Adj x z := by
  classical
  obtain ⟨S,L,R⟩ := split_at_shore ab conn C
  obtain ⟨xc,ax⟩ := mem_filter.mp xp
  have xl : x∈S.L := L.symm ▸ xc
  have sub' (H : Cmp G a b) (ch : C≠H) : aPorts H⊆S.foreignA := by
    intro z hz
    obtain ⟨zh,az⟩ := mem_filter.mp hz
    have nn := (mem_shore.mp zh).choose
    have nz : z∉Shore C := fun zc=>disjoint_left.mp (shore_disjoint ch) zc zh
    exact mem_filter.mpr ⟨R.symm ▸ (mem_filter.mpr ⟨mem_univ _,nn.1,nn.2,nz⟩),az⟩
  have f := two_local_counts _ _ (distinct_shore_ports_dis de) _ (sub' D cd) (sub' E ce)
  have e := distanceTwo_le_of_even 6 x (even x)
  have sat := (eq_of_subset_of_card_le (foreign_subset S hc xl ax) (by omega)).symm
  intro z zh
  exact reaches_all_left S hc xl sat (L.symm ▸ zh)

private theorem no_three_with_all_shores_high (hc : G.Connected) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (big : 3≤Nat.card (Cmp G a b))
    (high : ∀ C : Cmp G a b, ∃ x∈aPorts C,6≤G.degree x) : False := by
  classical
  obtain ⟨C,D,E,cd,ce,de⟩ := three_shores big
  obtain ⟨x,xp,xh⟩ := high C
  obtain ⟨y,yp,yh⟩ := high D
  obtain ⟨z,zp,zh⟩ := high E
  have cd6 := two_foreign_ports_budget hc even ce.symm de.symm cd zp
  have ce6 := two_foreign_ports_budget hc even cd.symm de ce yp
  have de6 := two_foreign_ports_budget hc even cd ce de xp
  have d₂ := distanceTwo_le_of_even 6 a (even a)
  have q₃ := three_local_counts _ _ _
    (distinct_shore_twos_dis cd) (distinct_shore_twos_dis ce) (distinct_shore_twos_dis de)
    (DistanceTwo G a) inter_subset_right inter_subset_right inter_subset_right
  have cost_x := port_cost hc C xp
  have cost_y := port_cost hc D yp
  have cost_z := port_cost hc E zp
  split at cost_x <;> split at cost_y <;> split at cost_z <;> try omega
  have bx : G.Adj b x := by assumption
  have by' : G.Adj b y := by assumption
  have axy := (mem_filter.mp xp).2
  have axz : G.Adj a x := axy
  have adj : G.Adj a b := by
    by_contra bad
    have ba : b∈DistanceTwo G a := d2 hc ab bad axz bx.symm
    have noC : b∉aTwos C := fun h=>(shore_off C).2 (mem_inter.mp h).1
    have noD : b∉aTwos D := fun h=>(shore_off D).2 (mem_inter.mp h).1
    have noE : b∉aTwos E := fun h=>(shore_off E).2 (mem_inter.mp h).1
    let A := (aTwos C∪aTwos D)∪aTwos E
    have hN : b∉A := by simp [A,noC,noD,noE]
    have hA : insert b A ⊆ DistanceTwo G a :=
      insert_subset ba (union_subset (union_subset inter_subset_right inter_subset_right) inter_subset_right)
    have m := card_le_card hA
    rw [card_insert_of_not_mem hN] at m
    have key : A.card=(aTwos C).card+(aTwos D).card+(aTwos E).card := by
      dsimp only [A]
      rw [card_union_of_disjoint (disjoint_union_left.mpr
        ⟨distinct_shore_twos_dis ce,distinct_shore_twos_dis de⟩),
        card_union_of_disjoint (distinct_shore_twos_dis cd)]
    omega
  have univC := local_universal_of_two_foreign_saturation hc even ab conn cd ce de xp (by omega)
  have splitC : Shore C ⊆ aPorts C∪aTwos C := by
    intro w wc
    by_cases aw : G.Adj a w
    · exact mem_union_left _ (mem_filter.mpr ⟨wc,aw⟩)
    have nz : w≠x := fun h=>aw (h.symm ▸ axz)
    have an : a≠w := fun h=>(shore_off C).1 (h.symm ▸ wc)
    exact mem_union_right _ (mem_inter.mpr ⟨wc,d2 hc an aw axz ((univC w wc).resolve_left nz)⟩)
  have nC := card_le_card splitC
  have uC := card_union_le (aPorts C) (aTwos C)
  have qC : (aTwos C).card=2 := by omega
  obtain ⟨f,g,fg,fgset⟩ := card_eq_two.mp qC
  have flo {w : V} (wm : w∈aTwos C) : G.degree w≤5 := by
    have wc := (mem_inter.mp wm).1
    have wan : ¬G.Adj a w := by
      intro aw
      have h := (mem_filter.mp (mem_inter.mp wm).2).2
      have n := dist_eq_one_iff_adj.mpr aw
      omega
    have sub : G.neighborFinset w ⊆ insert b ((Shore C).erase w) := by
      intro t tm
      have wt := (mem_neighborFinset _ _ _).mp tm
      rcases shore_closed C w wc t wt with rfl|rfl|tc
      · exact (wan wt.symm).elim
      · exact mem_insert_self _ _
      exact mem_insert_of_mem (mem_erase.mpr ⟨wt.ne.symm,tc⟩)
    have c := card_le_card sub
    rw [card_neighborFinset_eq_degree] at c
    have b₁ := card_insert_le b ((Shore C).erase w)
    have b₂ := card_erase_add_one wc
    omega
  have lf := flo (w:=f) (by rw [fgset]; simp)
  have lg := flo (w:=g) (by rw [fgset]; simp)
  rcases degree f g fg with h|h <;> omega

/-- Near an actual separating pair, if three shores occur, at least one shore
has no high vertex among the neighbors of either terminal (possibly different
shores). This preliminary result does not use the cut-pair distance. -/
theorem exists_shore_without_high_ports_at_six (hc : G.Connected) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (big : 3≤Nat.card (Cmp G a b)) :
    (∃ C : Cmp G a b, ∀ x∈aPorts C,G.degree x<6) ∧
    (∃ D : Cmp G a b, ∀ x∈bPorts D,G.degree x<6) := by
  classical
  constructor
  · by_contra no
    push_neg at no
    exact no_three_with_all_shores_high hc ab even conn degree big no
  by_contra no
  push_neg at no
  have bign : 3≤Nat.card (Cmp G b a) := by
    rw [←Nat.card_congr (swapCut (G:=G) (a:=a) (b:=b))]
    exact big
  apply no_three_with_all_shores_high hc ab.symm even conn degree bign
  intro C
  have eq : aPorts C = bPorts (swapCut C) := by
    simp only [aPorts,bPorts,shore_swapCut]
  rw [eq]
  exact no _

#print axioms exists_shore_without_high_ports_at_six
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
