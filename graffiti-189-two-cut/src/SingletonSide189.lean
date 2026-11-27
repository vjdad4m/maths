import ThreeSide189
import Mathlib.Data.Finset.Sum
namespace Graffiti189LongestPath.FourCut.Three.Sides
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V} (S : Sides G a b)
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

lemma mem_ports_s {i : Fin 3} {x : V} :
    x∈S.Ports i ↔ x∈S.H i ∧ (G.Adj a x ∨ G.Adj b x) := by
  simp [Ports]

lemma mem_inner_s {i : Fin 3} {x : V} :
    x∈S.Inner i ↔ x∈S.H i ∧ ¬ G.Adj a x ∧ ¬ G.Adj b x := by
  by_cases h : x∈S.H i <;> simp [Inner, mem_ports_s, h]

lemma port_dis_s {i j : Fin 3} (ne : i≠j) : Disjoint (S.Ports i) (S.Ports j) :=
  (S.dis i j ne).mono (filter_subset _ _) (filter_subset _ _)

lemma sh_degree_s {i : Fin 3} {x : V} (xi : x∈S.H i) :
    G.degree x ≤ (S.H i).card+1 := by
  have sub : G.neighborFinset x ⊆ insert a (insert b ((S.H i).erase x)) := by
    intro y hy
    have xy := (mem_neighborFinset G x y).mp hy
    rcases S.closed i x xi y xy with rfl|rfl|yi
    · simp
    · simp
    · exact mem_insert.mpr (Or.inr (mem_insert.mpr (Or.inr (mem_erase.mpr ⟨xy.ne.symm,yi⟩))))
  have c := card_le_card sub
  rw [card_neighborFinset_eq_degree] at c
  have c1 := card_insert_le a (insert b ((S.H i).erase x))
  have c2 := card_insert_le b ((S.H i).erase x)
  rw [card_erase_of_mem xi] at c2
  have c3 := card_pos.mpr ⟨x,xi⟩
  omega

lemma inner_nb_s {i : Fin 3} {x : V} (xi : x∈S.Inner i) :
    G.neighborFinset x ⊆ (S.H i).erase x := by
  obtain ⟨hi,na,nb⟩ := (S.mem_inner_s).mp xi
  intro y hy
  have xy := (mem_neighborFinset G x y).mp hy
  rcases S.closed i x hi y xy with rfl|rfl|yi
  · exact (na xy.symm).elim
  · exact (nb xy.symm).elim
  · exact mem_erase.mpr ⟨xy.ne.symm,yi⟩

lemma inner_adj_if_five_s {i : Fin 3} {x y : V} (xi : x∈S.Inner i) (yi : y∈S.H i)
    (ne : x≠y) (high : 4≤G.degree x) (five : (S.H i).card=5) : G.Adj x y := by
  have sub := S.inner_nb_s xi
  have eq := eq_of_subset_of_card_le sub (by
    rw [card_erase_of_mem ((S.mem_inner_s).mp xi).1, card_neighborFinset_eq_degree, five]
    exact high)
  exact (mem_neighborFinset G x y).mp (eq.symm ▸ mem_erase.mpr ⟨ne.symm,yi⟩)

lemma r_neighbors_s {r : V} (zero : S.H 0 = {r}) :
    G.Adj r a ∧ G.Adj r b ∧ ∀ x, G.Adj r x → x=a ∨ x=b := by
  obtain ⟨u,hu,au⟩ := S.hita 0
  obtain ⟨v,hv,bv⟩ := S.hitb 0
  have eu : u=r := by simpa [zero] using hu
  have ev : v=r := by simpa [zero] using hv
  refine ⟨(eu ▸ au).symm,(ev ▸ bv).symm,?_⟩
  intro x rx
  rcases S.closed 0 r (by simp [zero]) x rx with h|h|h
  · exact Or.inl h
  · exact Or.inr h
  · have h' : x=r := by simpa [zero] using h
    exact (rx.ne h'.symm).elim

lemma other_high_s {r : V} (zero : S.H 0 = {r})
    {i : Fin 3} (i0 : i≠0) {x : V} (xi : x∈S.H i) : 4≤G.degree x := by
  have rd := S.sh_degree_s (i:=0) (x:=r) (by simp [zero])
  rw [zero,card_singleton] at rd
  have xr : x≠r := fun e => disjoint_left.mp (S.dis i 0 i0) xi (by simp [zero,e])
  exact (S.degree x r xr).resolve_right (by omega)

lemma other_side_three_s {r : V} (zero : S.H 0 = {r}) {i : Fin 3} (i0 : i≠0) :
    3≤(S.H i).card := by
  obtain ⟨x,xi,_⟩ := S.hita i
  have xd := S.other_high_s zero i0 xi
  have bd := S.sh_degree_s xi
  omega

lemma port_to_r_s {r : V} (zero : S.H 0 = {r}) {i : Fin 3} (i0 : i≠0)
    {x : V} (xi : x∈S.Ports i) : x∈DistanceTwo G r := by
  obtain ⟨hi,ha|hb⟩ := S.mem_ports_s.mp xi
  all_goals
    have ne : r≠x := fun e => disjoint_left.mp (S.dis i 0 i0) hi (by simp [zero,e])
    have no : ¬G.Adj r x := S.adj_forces_same i0.symm (by simp [zero]) hi
  · exact mem_d2.mpr (dist_two S.con ne no (S.r_neighbors_s zero).1 ha)
  · exact mem_d2.mpr (dist_two S.con ne no (S.r_neighbors_s zero).2.1 hb)

lemma saturated_r_s {r : V} (zero : S.H 0 = {r}) :
    (S.Ports 1).card=2 ∧ (S.Ports 2).card=2 ∧ (DistanceTwo G r).card=4 := by
  have c1 := S.plenty 1 (by have := S.other_side_three_s zero (i:=1) (by decide); omega)
  have c2 := S.plenty 2 (by have := S.other_side_three_s zero (i:=2) (by decide); omega)
  change 2≤(S.Ports 1).card at c1
  change 2≤(S.Ports 2).card at c2
  have sub : S.Ports 1 ∪ S.Ports 2 ⊆ DistanceTwo G r := union_subset
    (fun _ hx => S.port_to_r_s zero (by decide) hx)
    (fun _ hx => S.port_to_r_s zero (by decide) hx)
  have ca := card_le_card sub
  rw [card_union_of_disjoint (S.port_dis_s (by decide : (1 : Fin 3) ≠ 2))] at ca
  have b := S.d2 r
  omega

lemma all_r_dist_s {r : V} (zero : S.H 0 = {r}) (x : V) : G.dist r x≤3 := by
  by_contra! h
  have cap := S.even r
  have big := distanceTwo_add_two_le_even_of_far S.con (show 4≤G.dist r x by omega)
  have full := (S.saturated_r_s zero).2.2
  omega

lemma inner_ge_s {r : V} (zero : S.H 0 = {r}) {i : Fin 3} (i0 : i≠0)
    (two : (S.Ports i).card=2) :
    3≤(S.Inner i).card ∧ (S.H i).card=(S.Inner i).card+2 := by
  have tc := S.other_side_three_s zero i0
  have sub : S.Ports i⊆S.H i := filter_subset _ _
  have eq : (S.Inner i).card + 2 = (S.H i).card := by
    simpa only [Inner, two] using card_sdiff_add_card_eq_card sub
  obtain ⟨x,hx⟩ := card_pos.mp (show 0<(S.Inner i).card by omega)
  have high := S.other_high_s zero i0 (S.mem_inner_s.mp hx).1
  have le := card_le_card (S.inner_nb_s hx)
  rw [card_neighborFinset_eq_degree,card_erase_of_mem (S.mem_inner_s.mp hx).1] at le
  omega

lemma inner_makes_shell_s {i : Fin 3} {x y : V} (xi : x∈S.Inner i) (xy : G.Adj x y) :
    (G.Adj a y → x∈DistanceTwo G a) ∧ (G.Adj b y → x∈DistanceTwo G b) := by
  obtain ⟨hi,na,nb⟩ := S.mem_inner_s.mp xi
  exact ⟨fun ay => mem_d2.mpr (dist_two S.con (fun e => (S.off i).1 (e.symm ▸ hi)) na ay xy.symm),
    fun by' => mem_d2.mpr (dist_two S.con (fun e => (S.off i).2 (e.symm ▸ hi)) nb by' xy.symm)⟩

lemma inner_shell_cover_s {r : V} (zero : S.H 0 = {r}) {i : Fin 3} (i0 : i≠0)
    {x : V} (xi : x∈S.Inner i) : x∈DistanceTwo G a ∨ x∈DistanceTwo G b := by
  classical
  obtain ⟨hi,na,nb⟩ := S.mem_inner_s.mp xi
  have ne : r≠x := fun e => disjoint_left.mp (S.dis i 0 i0) hi (by simp [zero,e])
  have rx : ¬G.Adj r x := S.adj_forces_same i0.symm (by simp [zero]) hi
  have low := S.con.one_lt_dist_of_ne_of_not_adj ne rx
  obtain ⟨q,qe⟩ := S.con.exists_walk_length_eq_dist r x
  have upper : q.length≤3 := qe ▸ S.all_r_dist_s zero x
  have rn := S.r_neighbors_s zero
  cases q with
  | nil => exact (ne rfl).elim
  | @cons r t x rt q =>
    rcases rn.2.2 t rt with rfl|rfl
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
            | exact Or.inl ((S.inner_makes_shell_s xi yz.symm).1 uy)
            | exact Or.inr ((S.inner_makes_shell_s xi yz.symm).2 uy)
          | cons => simp [Walk.length_cons] at upper

lemma inner_both_of_high_five_s {r : V} (zero : S.H 0 = {r}) {i : Fin 3} (i0 : i≠0)
    (five : (S.H i).card=5) {x : V} (xi : x∈S.Inner i) :
    x∈DistanceTwo G a ∧ x∈DistanceTwo G b := by
  obtain ⟨hi,na,nb⟩ := S.mem_inner_s.mp xi
  obtain ⟨u,ui,au⟩ := S.hita i
  obtain ⟨v,vi,bv⟩ := S.hitb i
  have high := S.other_high_s zero i0 hi
  have xu := S.inner_adj_if_five_s xi ui (fun q => na (q.symm ▸ au)) high five
  have xv := S.inner_adj_if_five_s xi vi (fun q => nb (q.symm ▸ bv)) high five
  exact ⟨(S.inner_makes_shell_s xi xu).1 au, (S.inner_makes_shell_s xi xv).2 bv⟩

lemma inner_both_of_all_common_s {r : V} (zero : S.H 0 = {r}) {i : Fin 3} (i0 : i≠0)
    (common : ∀ y∈S.Ports i, G.Adj a y ∧ G.Adj b y) {x : V} (xi : x∈S.Inner i) :
    x∈DistanceTwo G a ∧ x∈DistanceTwo G b := by
  have hi := (S.mem_inner_s.mp xi).1
  have ⟨_,na,nb⟩ := S.mem_inner_s.mp xi
  have pos (t : V) (ht : G.dist t x = 2) (ta : t=a ∨ t=b) :
      x∈DistanceTwo G a ∧ x∈DistanceTwo G b := by
    obtain ⟨w,l⟩ := S.con.exists_walk_length_eq_dist t x
    have two : w.length=2 := l.trans ht
    cases w with
    | nil => simp at two
    | @cons t y x ty w =>
      cases w with
      | nil => simp [Walk.length_cons] at two
      | @cons y z x yz w =>
        cases w with
        | nil =>
          rcases S.closed i x hi y yz.symm with ha|hb|hy
          · exact (na (ha ▸ yz)).elim
          · exact (nb (hb ▸ yz)).elim
          have hy' : y∈S.Ports i := S.mem_ports_s.mpr ⟨hy,
            ta.elim (fun e=>Or.inl (e ▸ ty)) (fun e=>Or.inr (e ▸ ty))⟩
          have com := common y hy'
          exact ⟨(S.inner_makes_shell_s xi yz.symm).1 com.1,
            (S.inner_makes_shell_s xi yz.symm).2 com.2⟩
        | cons => simp [Walk.length_cons] at two
  rcases S.inner_shell_cover_s zero i0 xi with ha|hb
  · exact pos a (mem_d2.mp ha) (Or.inl rfl)
  · exact pos b (mem_d2.mp hb) (Or.inr rfl)

def insides_s : Finset V := S.Inner 1 ∪ S.Inner 2
noncomputable def both_shells_s (_ : Sides G a b) : Finset (V ⊕ V) :=
  (DistanceTwo G a).disjSum (DistanceTwo G b)
noncomputable def inner_tags_s : Finset (V ⊕ V) :=
  (S.insides_s.filter (· ∈ DistanceTwo G a)).disjSum
    (S.insides_s.filter (· ∈ DistanceTwo G b))

lemma inner_tags_sub_s : S.inner_tags_s ⊆ S.both_shells_s := by
  intro z hz
  cases z with
  | inl x => exact inl_mem_disjSum.mpr (mem_filter.mp (inl_mem_disjSum.mp hz)).2
  | inr x => exact inr_mem_disjSum.mpr (mem_filter.mp (inr_mem_disjSum.mp hz)).2

lemma inner_tags_count_s {r : V} (zero : S.H 0 = {r}) :
    S.inner_tags_s.card = S.insides_s.card +
      ((S.insides_s.filter (· ∈ DistanceTwo G a)) ∩
        (S.insides_s.filter (· ∈ DistanceTwo G b))).card := by
  have eq : S.insides_s.filter (· ∈ DistanceTwo G a) ∪
      S.insides_s.filter (· ∈ DistanceTwo G b) = S.insides_s := by
    ext x
    simp only [mem_union,mem_filter]
    refine ⟨fun hx => hx.elim And.left And.left,?_⟩
    intro hx
    have inI := mem_union.mp hx
    have either : x∈DistanceTwo G a ∨ x∈DistanceTwo G b := inI.elim
      (S.inner_shell_cover_s zero (by decide)) (S.inner_shell_cover_s zero (by decide))
    exact either.elim (fun e=>Or.inl ⟨hx,e⟩) (fun e=>Or.inr ⟨hx,e⟩)
  unfold inner_tags_s
  rw [card_disjSum,← card_union_add_card_inter,eq]

lemma inner_union_count_s :
    S.insides_s.card=(S.Inner 1).card+(S.Inner 2).card := by
  unfold insides_s
  apply card_union_of_disjoint
  exact (S.dis 1 2 (by decide)).mono sdiff_subset sdiff_subset

lemma common_obstruction_s {r : V} (zero : S.H 0 = {r}) {i : Fin 3} (ii : i=1 ∨ i=2)
    (common : ∀ y∈S.Ports i, G.Adj a y ∧ G.Adj b y) : False := by
  have two := S.saturated_r_s zero
  have L := (S.inner_ge_s zero (i:=1) (by decide) two.1).1
  have R := (S.inner_ge_s zero (i:=2) (by decide) two.2.1).1
  have C : 3≤(S.Inner i).card := ii.elim (fun e=>e.symm ▸ L) (fun e=>e.symm ▸ R)
  have ni : i≠0 := ii.elim (fun e=>e.symm ▸ (by decide : (1:Fin 3)≠0))
    (fun e=>e.symm ▸ (by decide : (2:Fin 3)≠0))
  have has : S.Inner i ⊆ ((S.insides_s.filter (· ∈ DistanceTwo G a)) ∩
      (S.insides_s.filter (· ∈ DistanceTwo G b))) := by
    intro x xi
    have both := S.inner_both_of_all_common_s zero ni common xi
    have xu : x∈S.insides_s := mem_union.mpr (ii.elim
      (fun e=>Or.inl (e ▸ xi)) (fun e=>Or.inr (e ▸ xi)))
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨xu,both.1⟩,mem_filter.mpr ⟨xu,both.2⟩⟩
  have hi := card_le_card has
  have cap := card_le_card S.inner_tags_sub_s
  have ca := S.d2 a
  have cb := S.d2 b
  rw [S.inner_tags_count_s zero,S.inner_union_count_s,both_shells_s,card_disjSum] at cap
  omega

lemma tags_exclusive_s {i : Fin 3} (edge : G.Adj a b)
    (no : ¬ ∀ y∈S.Ports i, G.Adj a y ∧ G.Adj b y) :
    ∃ z : V ⊕ V, z∈S.both_shells_s ∧ z∉S.inner_tags_s ∧
      ∃ v∈S.Ports i, z=Sum.inl v ∨ z=Sum.inr v := by
  push_neg at no
  obtain ⟨v,vp,bad⟩ := no
  obtain ⟨vh,hv⟩ := S.mem_ports_s.mp vp
  have outsideI : v∉S.insides_s := by
    intro hi
    have n (j : Fin 3) (vj : v∈S.Inner j) : False := by
      by_cases equal : i=j
      · subst j
        exact (mem_sdiff.mp vj).2 vp
      · exact disjoint_left.mp (S.dis i j equal) vh (S.mem_inner_s.mp vj).1
    exact (mem_union.mp hi).elim (n 1) (n 2)
  rcases hv with va|vb
  · have nv : ¬G.Adj b v := bad va
    have ne : b≠v := fun e=>(S.off i).2 (e.symm ▸ vh)
    refine ⟨Sum.inr v, inr_mem_disjSum.mpr (mem_d2.mpr (dist_two S.con ne nv edge.symm va)),?_,v,vp,Or.inr rfl⟩
    exact fun h=> outsideI ((mem_filter.mp (inr_mem_disjSum.mp h)).1)
  · have nv : ¬G.Adj a v := fun va=>bad va vb
    have ne : a≠v := fun e=>(S.off i).1 (e.symm ▸ vh)
    refine ⟨Sum.inl v, inl_mem_disjSum.mpr (mem_d2.mpr (dist_two S.con ne nv edge vb)),?_,v,vp,Or.inl rfl⟩
    exact fun h=> outsideI ((mem_filter.mp (inl_mem_disjSum.mp h)).1)

lemma reserves_s {r : V} (zero : S.H 0 = {r}) :
    ∃ x y : V ⊕ V, x≠y ∧ x∈S.both_shells_s ∧ y∈S.both_shells_s ∧
      x∉S.inner_tags_s ∧ y∉S.inner_tags_s := by
  by_cases e : G.Adj a b
  · obtain ⟨x,xs,xt,v,vp,xv⟩ := S.tags_exclusive_s (i:=1) e
      (fun c=>S.common_obstruction_s zero (Or.inl rfl) c)
    obtain ⟨y,ys,yt,w,wp,yw⟩ := S.tags_exclusive_s (i:=2) e
      (fun c=>S.common_obstruction_s zero (Or.inr rfl) c)
    have vw : v≠w := fun eq=>disjoint_left.mp (S.port_dis_s (by decide : (1:Fin 3)≠2)) vp (eq.symm ▸ wp)
    have ne : x≠y := by
      rcases xv with rfl|rfl <;> rcases yw with rfl|rfl <;> simp [vw]
    exact ⟨x,y,ne,xs,ys,xt,yt⟩
  · have rn := S.r_neighbors_s zero
    have dh : b∈DistanceTwo G a := mem_d2.mpr (dist_two S.con S.ab e rn.1.symm rn.2.1)
    have dt : a∈DistanceTwo G b := mem_d2.mpr (dist_two S.con S.ab.symm (fun h=>e h.symm) rn.2.1.symm rn.1)
    have na : a∉S.insides_s := fun h => (mem_union.mp h).elim
      (fun h1=>(S.off 1).1 (S.mem_inner_s.mp h1).1) (fun h2=>(S.off 2).1 (S.mem_inner_s.mp h2).1)
    have nb : b∉S.insides_s := fun h => (mem_union.mp h).elim
      (fun h1=>(S.off 1).2 (S.mem_inner_s.mp h1).1) (fun h2=>(S.off 2).2 (S.mem_inner_s.mp h2).1)
    exact ⟨Sum.inl b,Sum.inr a,by simp,inl_mem_disjSum.mpr dh,inr_mem_disjSum.mpr dt,
      fun h=>nb (mem_filter.mp (inl_mem_disjSum.mp h)).1,fun h=>na (mem_filter.mp (inr_mem_disjSum.mp h)).1⟩

/-- Three deletion components cannot include a singleton. -/
theorem no_singleton_at_zero_189 {r : V} (zero : S.H 0 = {r}) : False := by
  classical
  obtain ⟨x,y,ne,xs,ys,xt,yt⟩ := S.reserves_s zero
  have yr : x∉insert y S.inner_tags_s := by simp [ne,xt]
  have sub : insert x (insert y S.inner_tags_s) ⊆ S.both_shells_s :=
    insert_subset_iff.mpr ⟨xs,insert_subset_iff.mpr ⟨ys,S.inner_tags_sub_s⟩⟩
  have t := card_le_card sub
  rw [card_insert_of_not_mem yr,card_insert_of_not_mem yt,both_shells_s,card_disjSum] at t
  have cap1 := S.d2 a
  have cap2 := S.d2 b
  have two := S.saturated_r_s zero
  have L := S.inner_ge_s zero (i:=1) (by decide) two.1
  have R := S.inner_ge_s zero (i:=2) (by decide) two.2.1
  rw [S.inner_tags_count_s zero, S.inner_union_count_s] at t
  have f1 : (S.H 1).card=5 := by omega
  have f2 : (S.H 2).card=5 := by omega
  have inc : S.insides_s ⊆ DistanceTwo G a := by
    intro v hv
    rcases mem_union.mp hv with h | h
    · exact (S.inner_both_of_high_five_s zero (by decide) f1 h).1
    · exact (S.inner_both_of_high_five_s zero (by decide) f2 h).1
  have too := card_le_card inc
  rw [S.inner_union_count_s] at too
  omega

#print axioms no_singleton_at_zero_189
end Graffiti189LongestPath.FourCut.Three.Sides
