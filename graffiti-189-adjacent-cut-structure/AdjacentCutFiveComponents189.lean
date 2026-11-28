import AdjacentCutFiveActual189
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open scoped BigOperators
open private CutGraph Shore mem_shore shore_off shore_nonempty shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from AdjacentCutFiveActual189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp := (CutGraph (G := G) a b).ConnectedComponent

private theorem degree_le_shore_add_one (C : Cmp (G:=G) (a:=a) (b:=b))
    {x : V} (hx : x ∈ Shore C) :
    G.degree x ≤ (Shore C).card + 1 := by
  classical
  have sub : G.neighborFinset x ⊆ insert a (insert b ((Shore C).erase x)) := by
    intro y hy
    have e := (mem_neighborFinset G x y).mp hy
    rcases shore_closed C x hx y e with h | h | h
    · exact mem_insert.mpr (.inl h)
    · exact mem_insert.mpr (.inr (mem_insert.mpr (.inl h)))
    · exact mem_insert.mpr (.inr (mem_insert.mpr (.inr (mem_erase.mpr ⟨e.ne.symm,h⟩))))
  have cnt := card_le_card sub
  have ea := card_insert_le a (insert b ((Shore C).erase x))
  have eb := card_insert_le b ((Shore C).erase x)
  have ex := card_erase_add_one hx
  rw [card_neighborFinset_eq_degree] at cnt
  omega

private theorem degree_le_shore (C : Cmp (G:=G) (a:=a) (b:=b))
    {x : V} (hx : x ∈ Shore C) (e : ¬G.Adj a x ∨ ¬G.Adj b x) :
    G.degree x ≤ (Shore C).card := by
  classical
  have cover (s t : V) (no : ¬G.Adj s x)
      (neigh : ∀ y, G.Adj x y → y=s ∨ y=t ∨ y∈Shore C) :
      G.degree x ≤ (Shore C).card := by
    have sub : G.neighborFinset x ⊆ insert t ((Shore C).erase x) := by
      intro y hy
      have e := (mem_neighborFinset G x y).mp hy
      rcases neigh y e with rfl | rfl | ys
      · exact (no e.symm).elim
      · exact mem_insert_self _ _
      · exact mem_insert.mpr (.inr (mem_erase.mpr ⟨e.ne.symm,ys⟩))
    have cnt := card_le_card sub
    have et := card_insert_le t ((Shore C).erase x)
    have ex := card_erase_add_one hx
    rw [card_neighborFinset_eq_degree] at cnt
    omega
  rcases e with ea | eb
  · exact cover a b ea (shore_closed C x hx)
  · exact cover b a eb (fun y xy => by simpa only [or_left_comm] using shore_closed C x hx y xy)

private theorem adjacent_or_degree_le_shore_sub_one
    (C : Cmp (G:=G) (a:=a) (b:=b))
    {x : V} (hx : x ∈ Shore C) (high : 5 ≤ G.degree x)
    (sm : (Shore C).card ≤ 5) : G.Adj a x ∨ G.Adj b x := by
  classical
  by_contra! no
  have sub : G.neighborFinset x ⊆ (Shore C).erase x := by
    intro y hy
    have e := (mem_neighborFinset G x y).mp hy
    rcases shore_closed C x hx y e with rfl | rfl | ys
    · exact (no.1 e.symm).elim
    · exact (no.2 e.symm).elim
    · exact mem_erase.mpr ⟨e.ne.symm,ys⟩
  have cnt := card_le_card sub
  have ex := card_erase_add_one hx
  rw [card_neighborFinset_eq_degree] at cnt
  omega

private noncomputable def Vis (C : Cmp (G:=G) (a:=a) (b:=b)) : Finset V := by
  classical exact (Shore C).filter (fun x => G.Adj a x ∨ G.Adj b x)

private theorem vis_sub (C : Cmp (G:=G) (a:=a) (b:=b)) : Vis C ⊆ Shore C := by
  classical
  intro x hx
  exact (mem_filter.mp hx).1

private theorem vis_card_ge_two (ab : a≠b)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (C : Cmp (G:=G) (a:=a) (b:=b)) (big : 2 ≤ (Shore C).card) :
    2 ≤ (Vis C).card := by
  classical
  obtain ⟨u,uC,au⟩ := shore_hit_a ab conn C
  have uV : u ∈ Vis C := mem_filter.mpr ⟨uC,.inl au⟩
  by_contra! small
  have unique (v : V) (vv : v ∈ Vis C) : v = u :=
    (Finset.card_le_one.mp (by omega : (Vis C).card ≤ 1)) v vv u uV
  have ne : ((Shore C).erase u).Nonempty := by
    have c := card_erase_add_one uC
    exact card_pos.mp (by omega)
  obtain ⟨z,hz⟩ := ne
  have az : a ≠ u := fun h => (shore_off C).1 (h.symm ▸ uC)
  let W : Set V := (↑({u} : Finset V) : Set V)ᶜ
  let z' : W := ⟨z,by simpa only [W,Set.mem_compl_iff,mem_coe,mem_singleton] using (mem_erase.mp hz).1⟩
  let a' : W := ⟨a,by simpa only [W,Set.mem_compl_iff,mem_coe,mem_singleton] using az⟩
  have step {v w : W} (e : (G.induce W).Adj v w) (vc : v.val ∈ Shore C) :
      w.val ∈ Shore C := by
    have e' : G.Adj v.val w.val := e
    have vne : v.val ≠ u := by simpa only [W,Set.mem_compl_iff,mem_coe,mem_singleton] using v.property
    rcases shore_closed C v.val vc w.val e' with eq | eq | wc
    · exact (vne (unique _ (mem_filter.mpr ⟨vc,.inl (eq ▸ e'.symm)⟩))).elim
    · exact (vne (unique _ (mem_filter.mpr ⟨vc,.inr (eq ▸ e'.symm)⟩))).elim
    · exact wc
  have propagate {v w : W} (p : (G.induce W).Walk v w) :
      v.val ∈ Shore C → w.val ∈ Shore C := by
    induction p with
    | nil => exact id
    | cons e q ih => exact fun h => ih (step e h)
  obtain ⟨q⟩ := (conn {u} (by simp)).preconnected z' a'
  exact (shore_off C).1 (propagate q (mem_erase.mp hz).2)

private theorem foreign_pos_even (hc : G.Connected)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (ne : C≠D)
    {x z t : V} (hx : x∈Shore C) (hz : z∈Shore D) (tx : G.Adj t x) (tz : G.Adj t z) :
    z ∈ PositiveEven G x := by
  have n : x ≠ z := fun e => disjoint_left.mp (shore_disjoint ne) hx (e ▸ hz)
  have e : ¬G.Adj x z := by
    intro xz
    rcases shore_closed C x hx z xz with h | h | h
    · exact (shore_off D).1 (h ▸ hz)
    · exact (shore_off D).2 (h ▸ hz)
    · exact disjoint_left.mp (shore_disjoint ne) h hz
  have low := hc.one_lt_dist_of_ne_of_not_adj n e
  have up := G.dist_le (Walk.cons tx.symm (Walk.cons tz .nil))
  have eq : G.dist x z = 2 := by simp at up; omega
  simp [PositiveEven, EvenFrom, n.symm, eq]


private theorem sum_subset_card
    (U : Finset (Cmp (G:=G) (a:=a) (b:=b))) (F : Cmp (G:=G) (a:=a) (b:=b) → Finset V)
    (sub : ∀ C ∈ U, F C ⊆ Shore C) (A : Finset V)
    (all : ∀ C ∈ U, F C ⊆ A) :
    (∑ C ∈ U, (F C).card) ≤ A.card := by
  classical
  have dis : (↑U : Set (Cmp (G:=G) (a:=a) (b:=b))).PairwiseDisjoint F := by
    intro C h D k ne
    exact (shore_disjoint ne).mono (sub C h) (sub D k)
  rw [← card_biUnion dis]
  apply card_le_card
  intro z h
  obtain ⟨C,hm,hz⟩ := mem_biUnion.mp h
  exact all C hm hz

private theorem shore_sum_budget (ab : a≠b)
    (U : Finset (Cmp (G:=G) (a:=a) (b:=b))) :
    (∑ C ∈ U, (Shore C).card) + 2 ≤ Fintype.card V := by
  classical
  let A := ((univ : Finset V).erase a).erase b
  have sub := sum_subset_card U Shore (fun _ _ => subset_rfl) A (by
    intro C h x hx
    exact mem_erase.mpr ⟨fun e=>(shore_off C).2 (e ▸ hx),
      mem_erase.mpr ⟨fun e=>(shore_off C).1 (e ▸ hx), mem_univ _⟩⟩)
  have cb := card_erase_add_one (mem_erase.mpr ⟨ab.symm,mem_univ _⟩ : b∈(univ : Finset V).erase a)
  have ca := card_erase_add_one (mem_univ a)
  rw [card_univ] at ca
  dsimp only [A] at sub
  omega

private theorem count_sum (U : Finset (Cmp (G:=G) (a:=a) (b:=b)))
    (F : Cmp (G:=G) (a:=a) (b:=b) → Finset V) (k : ℕ)
    (h : ∀ C∈U, k ≤ (F C).card) : U.card * k ≤ ∑ C ∈ U, (F C).card := by
  classical
  rw [← Finset.sum_const_nat (f := fun _ => k) (fun _ _ => rfl)]
  exact Finset.sum_le_sum h

private theorem positive_cap (x : V) (even : ∀ x,(EvenFrom G x).card ≤ 6) :
    (PositiveEven G x).card ≤ 5 := by
  classical
  have h : x ∈ EvenFrom G x := by simp [EvenFrom, SimpleGraph.dist_self]
  have c := card_erase_add_one h
  have e := even x
  change ((EvenFrom G x).erase x).card ≤ 5
  omega

/-- An adjacent separating pair under the degree-five hypotheses
leaves at most three actual components. -/
theorem component_card_le_three_at_adjacent_cut (hc : G.Connected) (ab : G.Adj a b)
    (even : ∀ x,(EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ x y : V,x≠y → 5≤G.degree x ∨ 5≤G.degree y) :
    Nat.card (CutGraph (G:=G) a b).ConnectedComponent ≤ 3 := by
  classical
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent ≤ 3
  by_contra! too
  have big : 4 ≤ Fintype.card J.ConnectedComponent := by
    rw [Nat.card_eq_fintype_card] at too
    omega
  have n21 : Fintype.card V ≤ 21 :=
    order_le_twenty_one_of_actual_adjacent_cut hc ab even conn (by change 2 ≤ Nat.card J.ConnectedComponent; omega)
  obtain ⟨U,_,u4⟩ := exists_subset_card_eq (show 4 ≤ (univ : Finset J.ConnectedComponent).card by simpa)
  have usum : (∑ C∈U, (Shore C).card) ≤ 19 := by
    have h := shore_sum_budget ab.ne U
    exact Nat.le_of_add_le_add_right (h.trans (show Fintype.card V ≤ 19 + 2 from n21))
  have port (C : J.ConnectedComponent) (t : V) (h : t=a ∨ t=b) :
      ∃ x∈Shore C, G.Adj t x := by
    rcases h with rfl|rfl
    · exact shore_hit_a ab.ne conn C
    · exact shore_hit_b ab.ne conn C
  have highfive (D : J.ConnectedComponent) (du : D∈U)
      (high : ∀ x∈Shore D, 5 ≤ G.degree x) : 5 ≤ (Shore D).card := by
    by_cases D5 : 5 ≤ (Shore D).card
    · exact D5
    have small : (Shore D).card < 5 := Nat.lt_of_not_ge D5
    exfalso
    have common (x : V) (xd : x∈Shore D) : G.Adj a x := by
      by_cases hit : G.Adj a x
      · exact hit
      · have le := degree_le_shore D xd (.inl hit)
        have hi := high x xd
        omega
    have K3 : (U.erase D).card = 3 := by have q := card_erase_add_one du; omega
    obtain ⟨C,cm⟩ : (U.erase D).Nonempty := card_pos.mp (by omega)
    obtain ⟨x,xc,ax⟩ := shore_hit_a ab.ne conn C
    let H := (U.erase D).erase C
    have h2 : H.card = 2 := by have q := card_erase_add_one cm; dsimp [H]; omega
    let F (E : J.ConnectedComponent) := (Shore E).filter (G.Adj a)
    have hcount : 2 ≤ ∑ E∈H, (F E).card := by
      have q : H.card * 1 ≤ ∑ E∈H,(F E).card := count_sum H F 1 (by
        intro E _
        obtain ⟨z,ze,az⟩ := shore_hit_a ab.ne conn E
        exact card_pos.mpr ⟨z,mem_filter.mpr ⟨ze,az⟩⟩)
      exact (show 2 ≤ H.card * 1 by omega).trans q
    let B := H.biUnion F
    have Bcard : 2 ≤ B.card := by
      change 2 ≤ (H.biUnion F).card
      rw [card_biUnion (show (↑H : Set J.ConnectedComponent).PairwiseDisjoint F from by
        intro E _ E' _ ne
        exact (shore_disjoint ne).mono (filter_subset _ _) (filter_subset _ _))]
      exact hcount
    have BD : Disjoint (Shore D) B := by
      apply disjoint_left.mpr
      intro z zd zb
      obtain ⟨E,eh,ze⟩ := mem_biUnion.mp zb
      have eD := (mem_erase.mp ((mem_erase.mp eh).2)).1
      exact disjoint_left.mp (shore_disjoint eD.symm) zd (mem_filter.mp ze).1
    have D4 : 4 ≤ (Shore D).card := by
      obtain ⟨z,zd⟩ := shore_nonempty D
      have q := degree_le_shore_add_one D zd
      have hi := high z zd
      omega
    have sub : Shore D ∪ B ⊆ PositiveEven G x := by
      intro z zm
      rcases mem_union.mp zm with zd | zb
      · exact foreign_pos_even hc (mem_erase.mp cm).1 xc zd ax (common z zd)
      · obtain ⟨E,eh,ze⟩ := mem_biUnion.mp zb
        exact foreign_pos_even hc (mem_erase.mp eh).1.symm xc (mem_filter.mp ze).1 ax (mem_filter.mp ze).2
    have le := card_le_card sub
    rw [card_union_of_disjoint BD] at le
    have cap := positive_cap x even
    omega
  by_cases all : ∀ C∈U, ∀ x∈Shore C, 5≤G.degree x
  · have h := count_sum U Shore 5 (fun C cm => highfive C cm (all C cm))
    exact (Nat.not_le_of_gt (show 19 < U.card * 5 by omega)) (h.trans usum)
  push_neg at all
  obtain ⟨D,du,z,zd,lo⟩ := all
  let T := U.erase D
  have t3 : T.card = 3 := by have h := card_erase_add_one du; dsimp [T]; omega
  have tally : (∑ C∈T,(Shore C).card) + (Shore D).card ≤ 19 := by
    rw [sum_erase_add _ _ du]
    exact usum
  have high (C : J.ConnectedComponent) (ct : C∈T) (x : V) (xc : x∈Shore C) :
      5≤G.degree x := by
    have ne : z≠x := fun e=>disjoint_left.mp (shore_disjoint (mem_erase.mp ct).1) xc (e.symm ▸ zd)
    exact (degree z x ne).resolve_left (by omega)
  have t5 (C : J.ConnectedComponent) (ct : C∈T) : 5≤(Shore C).card :=
    highfive C (mem_erase.mp ct).2 (high C ct)
  have t15 : T.card * 5 ≤ ∑ C∈T,(Shore C).card := count_sum T Shore 5 t5
  have d4 : (Shore D).card ≤ 4 := by omega
  by_cases singleton : (Shore D).card = 1
  · obtain ⟨x,dx⟩ := card_eq_one.mp singleton
    obtain ⟨xa,ha,ax⟩ := shore_hit_a ab.ne conn D
    obtain ⟨xb,hb,bx⟩ := shore_hit_b ab.ne conn D
    rw [dx,mem_singleton] at ha hb
    subst xa
    subst xb
    have xc : x∈Shore D := by simp [dx]
    have lower := count_sum T Vis 2 (fun C ct => vis_card_ge_two ab.ne conn C (by have := t5 C ct; omega))
    have upper := sum_subset_card T Vis (fun C _ => vis_sub C) (PositiveEven G x) (by
      intro C ct y hy
      have ym := mem_filter.mp hy
      have dc := (mem_erase.mp ct).1.symm
      exact ym.2.elim (foreign_pos_even hc dc xc ym.1 ax) (foreign_pos_even hc dc xc ym.1 bx))
    have cap := positive_cap x even
    omega
  have dpos : 0 < (Shore D).card := card_pos.mpr (shore_nonempty D)
  have dz : 0 < ((Shore D).erase z).card := by
    have q := card_erase_add_one zd
    omega
  obtain ⟨w,wm⟩ := card_pos.mp dz
  have wh := (degree w z (mem_erase.mp wm).1).resolve_right (by omega)
  have q := degree_le_shore_add_one D (mem_erase.mp wm).2
  have d4' : (Shore D).card = 4 := by omega
  have tEq (C : J.ConnectedComponent) (ct : C∈T) : (Shore C).card = 5 := by
    have T₂ : (T.erase C).card = 2 := by have q := card_erase_add_one ct; omega
    have lo2 : (T.erase C).card * 5 ≤ ∑ E∈T.erase C,(Shore E).card :=
      count_sum (T.erase C) Shore 5 (fun E em => t5 E (mem_erase.mp em).2)
    have eq : (∑ E∈T.erase C,(Shore E).card) + (Shore C).card = ∑ E∈T,(Shore E).card :=
      sum_erase_add T (fun E => (Shore E).card) ct
    have c5 := t5 C ct
    omega
  obtain ⟨xa,ha,ax⟩ := shore_hit_a ab.ne conn D
  obtain ⟨xb,hb,bx⟩ := shore_hit_b ab.ne conn D
  let Fa (C : J.ConnectedComponent) := (Shore C).filter (G.Adj a)
  let Fb (C : J.ConnectedComponent) := (Shore C).filter (G.Adj b)
  have ua : (∑ C∈T,(Fa C).card) ≤ (PositiveEven G xa).card := sum_subset_card T Fa (fun _ _ => filter_subset _ _) (PositiveEven G xa) (by
    intro C ct y ym
    exact foreign_pos_even hc (mem_erase.mp ct).1.symm ha (mem_filter.mp ym).1 ax (mem_filter.mp ym).2)
  have ub : (∑ C∈T,(Fb C).card) ≤ (PositiveEven G xb).card := sum_subset_card T Fb (fun _ _ => filter_subset _ _) (PositiveEven G xb) (by
    intro C ct y ym
    exact foreign_pos_even hc (mem_erase.mp ct).1.symm hb (mem_filter.mp ym).1 bx (mem_filter.mp ym).2)
  have lt := Finset.sum_le_sum (s := T) (fun C ct => show (Shore C).card ≤ (Fa C).card + (Fb C).card from by
    have sub : Shore C ⊆ Fa C ∪ Fb C := by
      intro y ym
      exact mem_union.mpr ((adjacent_or_degree_le_shore_sub_one C ym (high C ct y ym)
        (tEq C ct).le).imp (fun e=>mem_filter.mpr ⟨ym,e⟩) (fun e=>mem_filter.mpr ⟨ym,e⟩))
    exact (card_le_card sub).trans (card_union_le _ _))
  rw [Finset.sum_add_distrib] at lt
  change (∑ C∈T,(Shore C).card) ≤ (∑ C∈T,(Fa C).card) + ∑ C∈T,(Fb C).card at lt
  have ca := positive_cap xa even
  have cb := positive_cap xb even
  omega

#print axioms component_card_le_three_at_adjacent_cut
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
