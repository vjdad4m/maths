import AdjacentCutFiveTwoOrderTwenty189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore mem_shore shore_off shore_disjoint shore_closed shore_hit_a
  shore_hit_b shore_connected from AdjacentCutFiveActual189
open private positive_cap foreign_pos_even from AdjacentCutFiveComponents189
open private mem_positive cross_dist_of_equal odd_equal d2
  odd_dist_to_even_next twins_dist_le cross_walk_length from AdjacentCutFiveBound189
open private complete_from_no_local_even from AdjacentCutFiveTwoTwinGeometry189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

private theorem order_nineteen_of_extra_overlap
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ x, (EvenFrom G x).card ≤ 6)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {v : V}, v≠a → v≠b → v∈Shore C ∨ v∈Shore D)
    {x y z : V} (xc : x∈Shore C) (yd : y∈Shore D)
    (ax : G.Adj a x) (ay : G.Adj a y)
    (zb : z ≠ b) (az : G.Adj a z) (bz : ¬ G.Adj b z)
    (extra :
      (∃ t, t∈PositiveEven G a ∧ t∈PositiveEven G b) ∨
      (∃ t, t≠z ∧ (t∈PositiveEven G a ∨ t∈PositiveEven G b) ∧
        ((t∈Shore C ∧ t∈PositiveEven G y) ∨ (t∈Shore D ∧ t∈PositiveEven G x)))) :
    Fintype.card V ≤ 19 := by
  classical
  have dis := shore_disjoint cd
  let L := (Shore C).filter (fun v => v∈PositiveEven G y)
  let R := (Shore D).filter (fun v => v∈PositiveEven G x)
  let A := PositiveEven G a
  let B := PositiveEven G b
  let U := A ∪ B
  let W := L ∪ R
  have sub : (univ.erase a |>.erase b : Finset V) ⊆ U ∪ W := by
    intro v hv
    have vb := (mem_erase.mp hv).1
    have va := (mem_erase.mp (mem_erase.mp hv).2).1
    by_cases ea : Even (G.dist a v)
    · exact mem_union.mpr (.inl (mem_union.mpr (.inl (mem_positive.mpr ⟨va,ea⟩))))
    by_cases eb : Even (G.dist b v)
    · exact mem_union.mpr (.inl (mem_union.mpr (.inr (mem_positive.mpr ⟨vb,eb⟩))))
    have same := odd_equal hc ab ea eb
    rcases cover va vb with vc|vd
    · have no : v∉Shore D := fun h=>disjoint_left.mp dis vc h
      have dk := cross_dist_of_equal (Shore D) hc yd no (shore_closed D) (.inl ay) same
      have e := mem_positive.mpr ⟨(show v≠y from fun h=>no (by simpa only [h] using yd)),odd_dist_to_even_next dk ea⟩
      exact mem_union.mpr (.inr (mem_union.mpr (.inl (mem_filter.mpr ⟨vc,e⟩))))
    · have no : v∉Shore C := fun h=>disjoint_left.mp dis h vd
      have dk := cross_dist_of_equal (Shore C) hc xc no (shore_closed C) (.inl ax) same
      have e := mem_positive.mpr ⟨(show v≠x from fun h=>no (by simpa only [h] using xc)),odd_dist_to_even_next dk ea⟩
      exact mem_union.mpr (.inr (mem_union.mpr (.inr (mem_filter.mpr ⟨vd,e⟩))))
  have za : z≠a := az.ne.symm
  have zB : z∈B := by
    have hh := d2 hc zb.symm bz ab.symm az
    exact mem_positive.mpr ⟨zb,by simp [(mem_filter.mp hh).2]⟩
  have zW : z∈W := by
    rcases cover za zb with zc|zd
    · exact mem_union.mpr (.inl (mem_filter.mpr ⟨zc,foreign_pos_even hc cd.symm yd zc ay az⟩))
    · exact mem_union.mpr (.inr (mem_filter.mpr ⟨zd,foreign_pos_even hc cd xc zd ax az⟩))
  have zU : z∈U := mem_union.mpr (.inr zB)
  have eraseEq {K P : Finset V} {w : V} (wk : w∈K) :
      K∪P = K∪(P.erase w) := by
    ext u
    by_cases h : u=w
    · subst u; simp [wk]
    · simp [h]
  have wcard : W.card ≤ L.card + R.card := card_union_le L R
  have excess : (U∪W).card + 2 ≤ A.card + B.card + L.card + R.card := by
    rcases extra with ⟨t,ta,tb⟩|⟨t,tz,tu,tw⟩
    · have tu : U.card + 1 ≤ A.card + B.card := by
        have q := card_union_le A (B.erase t)
        rw [←eraseEq ta,card_erase_of_mem tb] at q
        change U.card ≤ A.card + (B.card - 1) at q
        have pos := card_pos.mpr (show B.Nonempty from ⟨t,tb⟩)
        omega
      have uv := card_union_le U (W.erase z)
      rw [←eraseEq zU,card_erase_of_mem zW] at uv
      have pos := card_pos.mpr (show W.Nonempty from ⟨z,zW⟩)
      omega
    · have tu' : t∈U := mem_union.mpr tu
      have tw' : t∈W := mem_union.mpr (tw.imp (fun j=>mem_filter.mpr j) (fun j=>mem_filter.mpr j))
      have wt : t∈W.erase z := mem_erase.mpr ⟨tz,tw'⟩
      have uv := card_union_le U ((W.erase z).erase t)
      rw [←eraseEq tu',←eraseEq zU,card_erase_of_mem wt,card_erase_of_mem zW] at uv
      have pos := card_pos.mpr (show (W.erase z).Nonempty from ⟨t,wt⟩)
      rw [card_erase_of_mem zW] at pos
      have ucard : U.card ≤ A.card + B.card := card_union_le A B
      omega
  have rem_size := card_le_card sub
  rw [card_erase_of_mem (by simp [ab.ne.symm]),card_erase_of_mem (mem_univ _),card_univ] at rem_size
  have acard := positive_cap a even
  have bcard := positive_cap b even
  have lcard : L.card ≤ 5 :=
    (card_le_card (show L ⊆ PositiveEven G y from fun _ h=>(mem_filter.mp h).2)).trans
      (positive_cap y even)
  have rcard : R.card ≤ 5 :=
    (card_le_card (show R ⊆ PositiveEven G x from fun _ h=>(mem_filter.mp h).2)).trans
      (positive_cap x even)
  by_cases small : Fintype.card V ≤ 19
  · exact small
  have big : 20 ≤ Fintype.card V := Nat.lt_of_not_ge small
  exfalso
  have l5 : L.card = 5 := by
    change A.card ≤ 5 at acard
    change B.card ≤ 5 at bcard
    omega
  have r5 : R.card = 5 := by
    change A.card ≤ 5 at acard
    change B.card ≤ 5 at bcard
    omega
  have ban {K P : Cmp G a b} (kp : K≠P)
      {v : V} (vc : v∈Shore K) (quota : ((Shore P).filter (fun u=>u∈PositiveEven G v)).card = 5) :
      ∀ u∈Shore K,u∉PositiveEven G v := by
    intro u uc ue
    let X := (Shore P).filter (fun w=>w∈PositiveEven G v)
    have un : u∉X := fun m => disjoint_left.mp (shore_disjoint kp) uc (mem_filter.mp m).1
    have s : insert u X ⊆ PositiveEven G v := by
      intro t tm
      rcases mem_insert.mp tm with rfl|tm
      · exact ue
      · exact (mem_filter.mp tm).2
    have c := card_le_card s
    rw [card_insert_of_not_mem un] at c
    change X.card = 5 at quota
    have q := positive_cap v even
    omega
  have ux := complete_from_no_local_even hc xc (ban cd xc r5)
  have uy := complete_from_no_local_even hc yd (ban cd.symm yd l5)
  let Cport := (Shore C).filter (G.Adj a)
  let Dport := (Shore D).filter (G.Adj a)
  have cp := card_le_card (show Cport ⊆ PositiveEven G y from
    fun _ q=>foreign_pos_even hc cd.symm yd (mem_filter.mp q).1 ay (mem_filter.mp q).2)
  have dp := card_le_card (show Dport ⊆ PositiveEven G x from
    fun _ q=>foreign_pos_even hc cd xc (mem_filter.mp q).1 ax (mem_filter.mp q).2)
  have rest : (univ.erase a |>.erase b : Finset V) ⊆ A ∪ (Cport∪Dport) := by
    intro v hv
    have vb := (mem_erase.mp hv).1
    have va := (mem_erase.mp (mem_erase.mp hv).2).1
    by_cases av : G.Adj a v
    · rcases cover va vb with vc|vd
      · exact mem_union.mpr (.inr (mem_union.mpr (.inl (mem_filter.mpr ⟨vc,av⟩))))
      · exact mem_union.mpr (.inr (mem_union.mpr (.inr (mem_filter.mpr ⟨vd,av⟩))))
    have w : ∃ c, G.Adj a c ∧ G.Adj c v := by
      rcases cover va vb with vc|vd
      · exact ⟨x,ax,(ux v vc).resolve_left (fun h=>av (h.symm ▸ ax))⟩
      · exact ⟨y,ay,(uy v vd).resolve_left (fun h=>av (h.symm ▸ ay))⟩
    obtain ⟨c,ac,cv⟩ := w
    have dd := d2 hc va.symm av ac cv
    exact mem_union.mpr (.inl (mem_positive.mpr ⟨va,by simp [(mem_filter.mp dd).2]⟩))
  have rem := card_le_card rest
  rw [card_erase_of_mem (by simp [ab.ne.symm]),card_erase_of_mem (mem_univ _),card_univ] at rem
  have p12 := card_union_le Cport Dport
  have p123 := card_union_le A (Cport ∪ Dport)
  have e1 := positive_cap x even
  have e2 := positive_cap y even
  change A.card ≤ 5 at acard
  omega


#print axioms order_nineteen_of_extra_overlap

private theorem positive_overlap_or_all_ports
    (hc : G.Connected) {D : Cmp G a b}
    (common : ∀ u∈Shore D, G.Adj a u ↔ G.Adj b u)
    {y : V} (yd : y∈Shore D) (ay : G.Adj a y) :
    (∃ t, t∈PositiveEven G a ∧ t∈PositiveEven G b) ∨
      (∀ u∈Shore D, G.Adj a u) := by
  by_cases hit : ∃ u∈Shore D, ∃ v∈Shore D, G.Adj a u ∧ ¬G.Adj a v ∧ G.Adj u v
  · obtain ⟨u,ud,v,vd,au,av,uv⟩ := hit
    have bv : ¬ G.Adj b v := fun e=>av ((common v vd).mpr e)
    have bu := (common u ud).mp au
    have va : v≠a := fun e=>(shore_off D).1 (e ▸ vd)
    have vb : v≠b := fun e=>(shore_off D).2 (e ▸ vd)
    have ad := (mem_filter.mp (d2 hc va.symm av au uv)).2
    have bd := (mem_filter.mp (d2 hc vb.symm bv bu uv)).2
    exact .inl ⟨v,mem_positive.mpr ⟨va,by simp [ad]⟩,mem_positive.mpr ⟨vb,by simp [bd]⟩⟩
  · right
    let H := G.induce (↑(Shore D) : Set V)
    have trans {u v : (↑(Shore D) : Set V)} (p : H.Walk u v)
        (uport : G.Adj a u.val) : G.Adj a v.val := by
      induction p with
      | nil => exact uport
      | @cons u w v e p ih =>
        apply ih
        by_contra h
        exact hit ⟨_,u.property,_,w.property,uport,h,e⟩
    intro v vd
    obtain ⟨p⟩ := (shore_connected D).preconnected ⟨y,yd⟩ ⟨v,vd⟩
    exact trans p ay

private theorem order_small_of_all_port_shore_and_nested
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ x, (EvenFrom G x).card ≤ 6)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {v : V}, v≠a → v≠b → v∈Shore C ∨ v∈Shore D)
    {x y : V} (xc : x∈Shore C) (yd : y∈Shore D)
    (ax : G.Adj a x) (ay : G.Adj a y)
    (all : ∀ v∈Shore D, G.Adj a v)
    (nested : ∀ v, v≠a → G.Adj b v → G.Adj a v) :
    Fintype.card V ≤ 17 := by
  classical
  have nd (v : V) (vc : v∈Shore C) :
      G.dist y v = G.dist a v + 1 := by
    have no : v∉Shore D := fun h=>disjoint_left.mp (shore_disjoint cd) vc h
    have vb : v≠b := fun h=>(shore_off C).2 (h ▸ vc)
    have near := twins_dist_le hc vb.symm (a:=b) (b:=a) nested
    obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist y v
    have lo := cross_walk_length (Shore D) no (shore_closed D) p yd
    rw [min_eq_left near,pl] at lo
    have hi := hc.dist_triangle (u:=y) (v:=a) (w:=v)
    rw [dist_eq_one_iff_adj.mpr ay.symm] at hi
    omega
  let O := (Shore C).filter (fun v => ¬ Even (G.dist a v))
  let E := (Shore C).filter (fun v => Even (G.dist a v))
  have oe : Shore C = O∪E := by
    ext v
    simp only [O,E,mem_union,mem_filter]
    constructor
    · intro vc
      by_cases p : Even (G.dist a v)
      · exact .inr ⟨vc,p⟩
      · exact .inl ⟨vc,p⟩
    · exact fun h=>h.elim And.left And.left
  have oc : O.card ≤ 5 := by
    have s : O ⊆ PositiveEven G y := by
      intro v vv
      obtain ⟨vc,odd⟩ := mem_filter.mp vv
      have vy : v≠y := fun e=>disjoint_left.mp (shore_disjoint cd) vc (e.symm ▸ yd)
      exact mem_positive.mpr ⟨vy,odd_dist_to_even_next (nd v vc) odd⟩
    exact (card_le_card s).trans (positive_cap y even)
  have ec : E.card ≤ 5 := by
    have s : E ⊆ PositiveEven G a := by
      intro v vv
      obtain ⟨vc,ee⟩ := mem_filter.mp vv
      exact mem_positive.mpr ⟨fun h=>(shore_off C).1 (h ▸ vc),ee⟩
    exact (card_le_card s).trans (positive_cap a even)
  have dc : (Shore D).card ≤ 5 := by
    have s : Shore D ⊆ PositiveEven G x := by
      intro v vd
      exact foreign_pos_even hc cd xc vd ax (all v vd)
    exact (card_le_card s).trans (positive_cap x even)
  have g := card_union_le O E
  rw [←oe] at g
  have s : (univ.erase a |>.erase b : Finset V) ⊆ Shore C ∪ Shore D := by
    intro v vv
    exact mem_union.mpr (cover (mem_erase.mp (mem_erase.mp vv).2).1 (mem_erase.mp vv).1)
  have n := card_le_card s
  rw [card_erase_of_mem (by simp [ab.ne.symm]),card_erase_of_mem (mem_univ _),card_univ] at n
  have u := card_union_le (Shore C) (Shore D)
  omega


private theorem order_nineteen_from_an_exclusive
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (two : Nat.card (Cmp G a b) = 2)
    {z : V} (zb : z≠b) (az : G.Adj a z) (bz : ¬G.Adj b z) :
    Fintype.card V ≤ 19 := by
  classical
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores two
  by_cases aa : ∃ t, t≠z ∧ t≠b ∧ G.Adj a t ∧ ¬G.Adj b t
  · obtain ⟨t,tz,tb,at',bt⟩ := aa
    obtain ⟨x,xc,ax⟩ := shore_hit_a ab.ne conn C
    obtain ⟨y,yd,ay⟩ := shore_hit_a ab.ne conn D
    apply order_nineteen_of_extra_overlap hc ab even cd cover xc yd ax ay zb az bz
    right
    have d := (mem_filter.mp (d2 hc tb.symm bt ab.symm at')).2
    refine ⟨t,tz,.inr (mem_positive.mpr ⟨tb,by simp [d]⟩),?_⟩
    rcases cover at'.ne.symm tb with tc|td
    · exact .inl ⟨tc,foreign_pos_even hc cd.symm yd tc ay at'⟩
    · exact .inr ⟨td,foreign_pos_even hc cd xc td ax at'⟩
  by_cases bb : ∃ t, t≠a ∧ G.Adj b t ∧ ¬G.Adj a t
  · obtain ⟨t,ta,bt,at'⟩ := bb
    by_cases bb' : ∃ u, u≠t ∧ u≠a ∧ G.Adj b u ∧ ¬G.Adj a u
    · obtain ⟨u,ut,ua,bu,au⟩ := bb'
      have sw : {v : V | v≠a ∧ v≠b} = {v : V | v≠b ∧ v≠a} := Set.ext (fun _=>and_comm)
      have tt : Nat.card (Cmp G b a) = 2 := by
        change Nat.card (G.induce {v : V | v≠b ∧ v≠a}).ConnectedComponent = 2
        rw [←sw]
        exact two
      obtain ⟨K,P,kp,cov⟩ := actual_two_shores tt
      obtain ⟨r,rk,br⟩ := shore_hit_a ab.ne.symm conn K
      obtain ⟨s,sp,bs⟩ := shore_hit_a ab.ne.symm conn P
      apply order_nineteen_of_extra_overlap hc ab.symm even kp cov rk sp br bs ta bt at'
      right
      have d := (mem_filter.mp (d2 hc ua.symm au ab bu)).2
      refine ⟨u,ut,.inr (mem_positive.mpr ⟨ua,by simp [d]⟩),?_⟩
      rcases cov bu.ne.symm ua with uk|up
      · exact .inl ⟨uk,foreign_pos_even hc kp.symm sp uk bs bu⟩
      · exact .inr ⟨up,foreign_pos_even hc kp rk up br bu⟩
    have tpos : t∈PositiveEven G a := by
      have d := (mem_filter.mp (d2 hc ta.symm at' ab bt)).2
      exact mem_positive.mpr ⟨ta,by simp [d]⟩
    have tz : t≠z := fun eq=>at' (eq.symm ▸ az)
    rcases cover ta bt.ne.symm with tc|td
    · obtain ⟨x,xc,ax⟩ := shore_hit_a ab.ne conn C
      obtain ⟨y,yd,by'⟩ := shore_hit_b ab.ne conn D
      have ay : G.Adj a y := by
        by_contra no
        have yt : y≠t := fun eq=>disjoint_left.mp (shore_disjoint cd) tc (eq ▸ yd)
        have ya : y≠a := fun eq=>(shore_off D).1 (eq ▸ yd)
        exact bb' ⟨y,yt,ya,by',no⟩
      exact order_nineteen_of_extra_overlap hc ab even cd cover xc yd ax ay zb az bz
        (.inr ⟨t,tz,.inl tpos,.inl ⟨tc,foreign_pos_even hc cd.symm yd tc by' bt⟩⟩)
    · obtain ⟨x,xc,bx⟩ := shore_hit_b ab.ne conn C
      obtain ⟨y,yd,ay⟩ := shore_hit_a ab.ne conn D
      have ax : G.Adj a x := by
        by_contra no
        have xt : x≠t := fun eq=>disjoint_left.mp (shore_disjoint cd) (eq ▸ xc) td
        have xa : x≠a := fun eq=>(shore_off C).1 (eq ▸ xc)
        exact bb' ⟨x,xt,xa,bx,no⟩
      exact order_nineteen_of_extra_overlap hc ab even cd cover xc yd ax ay zb az bz
        (.inr ⟨t,tz,.inl tpos,.inr ⟨td,foreign_pos_even hc cd xc td bx bt⟩⟩)
  have nested (v : V) (va : v≠a) (bv : G.Adj b v) : G.Adj a v := by
    by_contra no
    exact bb ⟨v,va,bv,no⟩
  have single {K P : Cmp G a b} (kp : K≠P)
      (cov : ∀ {v : V}, v≠a → v≠b → v∈Shore K ∨ v∈Shore P)
      (zk : z∈Shore K) : Fintype.card V ≤ 19 := by
    obtain ⟨x,xk,ax⟩ := shore_hit_a ab.ne conn K
    obtain ⟨y,yp,ay⟩ := shore_hit_a ab.ne conn P
    have cm (v : V) (vp : v∈Shore P) : G.Adj a v ↔ G.Adj b v := by
      have va : v≠a := fun e=>(shore_off P).1 (e ▸ vp)
      have vb : v≠b := fun e=>(shore_off P).2 (e ▸ vp)
      have vz : v≠z := fun e=>disjoint_left.mp (shore_disjoint kp) zk (e ▸ vp)
      refine ⟨?_,nested v va⟩
      intro av
      by_contra nv
      exact aa ⟨v,vz,vb,av,nv⟩
    rcases positive_overlap_or_all_ports hc cm yp ay with ov|all
    · exact order_nineteen_of_extra_overlap hc ab even kp cov xk yp ax ay zb az bz (.inl ov)
    · exact (order_small_of_all_port_shore_and_nested hc ab even kp cov xk yp ax ay all nested).trans (by decide)
  rcases cover az.ne.symm zb with zc|zd
  · exact single cd cover zc
  · exact single cd.symm (fun va vb=>(cover va vb).symm) zd

theorem order_le_nineteen_of_actual_adjacent_two_shores
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ x, (EvenFrom G x).card ≤ 6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (two : Nat.card (Cmp G a b) = 2) :
    Fintype.card V ≤ 19 := by
  classical
  by_cases twin : ∀ z, z ≠ a → z ≠ b → (G.Adj a z ↔ G.Adj b z)
  · exact (order_le_seventeen_of_actual_adjacent_twin_cut hc ab even conn (two.symm ▸ Nat.le_refl 2) twin).trans (by decide)
  push_neg at twin
  obtain ⟨z,za,zb,h⟩ := twin
  by_cases az : G.Adj a z
  · exact order_nineteen_from_an_exclusive hc ab even conn two zb az ((h.resolve_right (fun q=>q.1 az)).2)
  have bz : G.Adj b z := (h.resolve_left (fun q=>az q.1)).2
  have sw : {z : V | z≠a ∧ z≠b} = {z : V | z≠b ∧ z≠a} := Set.ext (fun _=>and_comm)
  have twos : Nat.card (Cmp G b a) = 2 := by
    change Nat.card (G.induce {z : V | z≠b ∧ z≠a}).ConnectedComponent = 2
    rw [←sw]
    exact two
  exact order_nineteen_from_an_exclusive hc ab.symm even conn twos za bz az

#print axioms order_le_nineteen_of_actual_adjacent_two_shores
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
