import AdjacentCutFiveFourteenEC1Frame189
import AdjacentCutFiveFourteenSingletonThree189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_closed shore_disjoint shore_hit_a shore_hit_b from AdjacentCutFiveActual189
open private prof classSet key key_facts from AdjacentCutFiveTopProfiles189
open private key_a_port key_b_port from AdjacentCutFiveTopFlatten189
open private even_two_three_info even_three_two_info restrict_unique_profile disjoint_profile_sets shore_port_cases
  from AdjacentCutFiveSixteenSingletonGeometry189
open private left_even_adjoins_exclusive right_even_adjoins_exclusive from AdjacentCutFiveSixteenSingletonDepth189
open private mem_positive d2 from AdjacentCutFiveBound189
open private foreign_pos_even positive_cap from AdjacentCutFiveComponents189
open private inside_lower_of_boundary from AdjacentCutFiveMixedRouteSmall189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent

set_option maxHeartbeats 4000000 in
/-- A singleton and order-eleven shore with one equal-even vertex and one
exclusive port of each color are traceable when the strict even classes
contain at least two vertices each and at least five in total. -/
theorem traceable_of_adjacent_singleton_eleven_equal_one_unique
    (hc : G.Connected) (ab : G.Adj a b) (even : ∀ z,(EvenFrom G z).card≤6)
    (conn : ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp G a b} (cd : C≠D)
    (cover : ∀ {z : V}, z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
    (one : (Shore C).card=1) (big : (Shore D).card=11)
    (a2 : 2≤(prof D).ea) (b2 : 2≤(prof D).eb) (ab5 : 5≤(prof D).ea+(prof D).eb)
    (ec : (prof D).ec=1) (oa : (prof D).oa=1) (ob : (prof D).ob=1)
    (oc3 : (prof D).oc≤3) :
    ∃ s t,∃ p : G.Walk s t,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  obtain ⟨s,sC⟩ := card_eq_one.mp one
  have sc : s∈Shore C := by simp [sC]
  obtain ⟨c,cm,ac⟩ := shore_hit_a ab.ne conn C
  obtain ⟨d,dm,bd⟩ := shore_hit_b ab.ne conn C
  have as' : G.Adj a s := (show c=s by simpa [sC] using cm) ▸ ac
  have bs' : G.Adj b s := (show d=s by simpa [sC] using dm) ▸ bd
  have sD : s∉Shore D := fun h=>disjoint_left.mp (shore_disjoint cd) sc h
  have Dside {u : V} (um : u∈Shore D) : u≠a ∧ u≠b ∧ u≠s :=
    ⟨fun h=>(shore_off D).1 (h ▸ um),fun h=>(shore_off D).2 (h ▸ um),fun h=>sD (h ▸ um)⟩
  obtain ⟨numA,_,high⟩ := adjacent_singleton_terminal_count ab degree cd cover one
  let A := classSet D 0
  let B := classSet D 1
  let E := classSet D 2
  let O := classSet D 5
  let K := O.filter (fun v=>G.Adj a v ∧ G.Adj b v)
  let W := A ∪ B ∪ (O \ K)
  have a2' : 2≤A.card := a2
  have b2' : 2≤B.card := b2
  have ab5' : 5≤A.card+B.card := ab5
  have er : E.card=1 := ec
  obtain ⟨e,eE⟩ := card_eq_one.mp er
  have em : e∈E := by simp [eE]
  have ed := (mem_filter.mp em).1
  have ek := (mem_filter.mp em).2
  obtain ⟨u,um⟩ := card_pos.mp (show 0<A.card by omega)
  obtain ⟨v,vm⟩ := card_pos.mp (show 0<B.card by omega)
  obtain ⟨x,xd,ax,bx⟩ := exclusive_left_port_of_strictly_nearer hc
    (mem_filter.mp um).1 (by have h:=even_two_three_info hc ab oa um; omega)
  obtain ⟨y,yd,by',ay⟩ := exclusive_right_port_of_strictly_nearer hc
    (mem_filter.mp vm).1 (by have h:=even_three_two_info hc ab ob vm; omega)
  have dx := (mem_filter.mp (d2 hc (Dside xd).2.1.symm bx ab.symm ax)).2
  have dy := (mem_filter.mp (d2 hc (Dside yd).1.symm ay ab by')).2
  have xk : key G a b x=3 := by simp [key,dist_eq_one_iff_adj.mpr ax,dx]
  have yk : key G a b y=4 := by simp [key,dist_eq_one_iff_adj.mpr by',dy]
  have L := restrict_unique_profile oa xd xk
  have R := restrict_unique_profile ob yd yk
  have xy : x≠y := fun f=>ay (f ▸ ax)
  have xe : x≠e := by intro h; rw [h,ek] at xk; contradiction
  have ye : y≠e := by intro h; rw [h,ek] at yk; contradiction
  have disAB : Disjoint A B := disjoint_profile_sets D (by decide : (0:Fin 6)≠1)
  have ak (z : V) (zm : z∈K) : G.Adj a z := (mem_filter.mp zm).2.1
  have bk (z : V) (zm : z∈K) : G.Adj b z := (mem_filter.mp zm).2.2
  have kD : K⊆Shore D := fun z h=>(mem_filter.mp (mem_filter.mp h).1).1
  have k3 : K.card≤3 := (card_le_card (filter_subset _ _)).trans (show O.card≤3 from oc3)
  have k2 : 2≤K.card := by
    have sub : (Shore D).filter (G.Adj a)⊆insert x K := by
      intro z zm
      obtain ⟨zd,az⟩ := mem_filter.mp zm
      rcases shore_port_cases hc ab zd L R (.inl az) with h|h|⟨az,bz,oz⟩
      · exact mem_insert.mpr (.inl h)
      · exact (ay (h ▸ az)).elim
      exact mem_insert_of_mem (mem_filter.mpr ⟨oz,az,bz⟩)
    have q := (card_le_card sub).trans (card_insert_le _ _)
    omega
  have xA (u : V) (um : u∈A) : G.Adj x u := by
    have h := even_two_three_info hc ab oa um
    exact left_even_adjoins_exclusive hc ab L (mem_filter.mp um).1 h.1 h.2
  have yB (u : V) (um : u∈B) : G.Adj y u := by
    have h := even_three_two_info hc ab ob um
    exact right_even_adjoins_exclusive hc ab R (mem_filter.mp um).1 h.1 h.2
  have eqW (z : V) : z∈W ↔ z∈A ∨ z∈B ∨ z∈O ∧ z∉K := by
    simp [W,or_assoc]
  have wD : W⊆Shore D := by
    intro z zm
    rcases (eqW z).mp zm with h|h|⟨h,_⟩
    · exact (mem_filter.mp h).1
    · exact (mem_filter.mp h).1
    exact (mem_filter.mp h).1
  have disWK : Disjoint W K := by
    apply disjoint_left.mpr
    intro z zm zk
    have oc := (mem_filter.mp zk).1
    rcases (eqW z).mp zm with h|h|⟨_,h⟩
    · exact disjoint_left.mp (disjoint_profile_sets D (by decide : (0:Fin 6)≠5)) h oc
    · exact disjoint_left.mp (disjoint_profile_sets D (by decide : (1:Fin 6)≠5)) h oc
    exact h zk
  have keynotW {z : V} (h : key G a b z=2 ∨ key G a b z=3 ∨ key G a b z=4) : z∉W := by
    intro zm
    rcases (eqW z).mp zm with j|j|⟨j,_⟩ <;>
      have k := (mem_filter.mp j).2 <;> rw [k] at h <;> omega
  have xW : x∉W := keynotW (.inr (.inl xk))
  have yW : y∉W := keynotW (.inr (.inr yk))
  have eW : e∉W := keynotW (.inl ek)
  have xK : x∉K := fun h=>bx (bk x h)
  have yK : y∉K := fun h=>ay (ak y h)
  have eK : e∉K := by
    intro h
    have k := (mem_filter.mp (mem_filter.mp h).1).2
    rw [ek] at k
    contradiction
  have eNo (u : V) (um : u∈E) : ¬G.Adj a u ∧ ¬G.Adj b u := by
    obtain ⟨ud,uk⟩ := mem_filter.mp um
    constructor
    · intro h
      rcases key_a_port hc ab (Dside ud).2.1 h with t|t <;> rw [uk] at t <;> contradiction
    · intro h
      rcases key_b_port hc ab (Dside ud).1 h with t|t <;> rw [uk] at t <;> contradiction
  have split (z : V) (zd : z∈Shore D) : z∈W ∨ z∈K ∨ z=x ∨ z=y ∨ z=e := by
    have poss : key G a b z=0 ∨ key G a b z=1 ∨ key G a b z=2 ∨
       key G a b z=3 ∨ key G a b z=4 ∨ key G a b z=5 := by omega
    rcases poss with h|h|h|h|h|h
    · exact .inl ((eqW z).mpr (.inl (mem_filter.mpr ⟨zd,h⟩)))
    · exact .inl ((eqW z).mpr (.inr (.inl (mem_filter.mpr ⟨zd,h⟩))))
    · exact .inr (.inr (.inr (.inr (mem_singleton.mp (eE ▸ (mem_filter.mpr ⟨zd,h⟩ : z∈E))))))
    · exact .inr (.inr (.inl (mem_singleton.mp (L ▸ (mem_filter.mpr ⟨zd,h⟩ : z∈classSet D 3)))))
    · exact .inr (.inr (.inr (.inl (mem_singleton.mp (R ▸ (mem_filter.mpr ⟨zd,h⟩ : z∈classSet D 4))))))
    by_cases t : z∈K
    · exact .inr (.inl t)
    exact .inl ((eqW z).mpr (.inr (.inr ⟨mem_filter.mpr ⟨zd,h⟩,t⟩)))
  have noW (z : V) (zm : z∈W) : ¬G.Adj a z ∧ ¬G.Adj b z := by
    have no (h : G.Adj a z ∨ G.Adj b z) : False := by
      rcases shore_port_cases hc ab (wD zm) L R h with p|p|⟨u,v,r⟩
      · exact xW (p ▸ zm)
      · exact yW (p ▸ zm)
      exact disjoint_left.mp disWK zm (mem_filter.mpr ⟨r,u,v⟩)
    exact ⟨fun h=>no (.inl h),fun h=>no (.inr h)⟩
  have noWK {u z : V} (um : u∈W) (zk : z∈K) (uz : G.Adj u z) : False := by
    have ⟨nA,nB⟩ := noW u um
    have oa := (Dside (wD um)).1
    have ob := (Dside (wD um)).2.1
    have f := (mem_filter.mp (d2 hc oa.symm nA (ak z zk) uz.symm)).2
    have h := (mem_filter.mp (d2 hc ob.symm nB (bk z zk) uz.symm)).2
    have k : key G a b u=2 := by simp [key,f,h]
    exact keynotW (.inl k) um
  have yAf (u : V) (um : u∈A) : ¬G.Adj y u := by
    intro H
    have o := even_two_three_info hc ab oa um
    have h := hc.dist_triangle (u:=b) (v:=y) (w:=u)
    rw [o.2,dist_eq_one_iff_adj.mpr by',dist_eq_one_iff_adj.mpr H] at h
    omega
  have xBf (u : V) (um : u∈B) : ¬G.Adj x u := by
    intro H
    have o := even_three_two_info hc ab ob um
    have h := hc.dist_triangle (u:=a) (v:=x) (w:=u)
    rw [o.1,dist_eq_one_iff_adj.mpr ax,dist_eq_one_iff_adj.mpr H] at h
    omega
  have neutral_no {u : V} (um : u∈O) (uw : u∈W) :
      ¬G.Adj x u ∧ ¬G.Adj y u := by
    obtain ⟨az,bz,odd⟩ := key_facts hc ab u
    rw [(mem_filter.mp um).2] at az bz odd
    change G.dist a u=depth G a b u+0 at az
    change G.dist b u=depth G a b u+0 at bz
    change depth G a b u%2=1 at odd
    have lo : 3≤depth G a b u := by
      by_cases h : depth G a b u=1
      · exact ((noW u uw).1 (dist_eq_one_iff_adj.mp (by omega))).elim
      omega
    constructor
    · intro xu
      have h := hc.dist_triangle (u:=a) (v:=x) (w:=u)
      rw [dist_eq_one_iff_adj.mpr ax,dist_eq_one_iff_adj.mpr xu] at h
      omega
    · intro yu
      have h := hc.dist_triangle (u:=b) (v:=y) (w:=u)
      rw [dist_eq_one_iff_adj.mpr by',dist_eq_one_iff_adj.mpr yu] at h
      omega
  have highW (u : V) (um : u∈W) : 4≤(inside G (insert e W) u).card := by
    have hu := high u (wD um)
    have near {t : V} (deny : ∀ z,G.Adj u z → z=x → t=x)
        (deny' : ∀ z,G.Adj u z → z=y → t=y) :
        G.degree u≤(inside G (insert e W) u).card+1 := by
      have f := inside_lower_of_boundary (G:=G) (insert e W) {t} (u:=u)
        (fun z uz=>by
          rcases shore_closed D u (wD um) z uz with h|h|h
          · exact ((noW u um).1 (h ▸ uz.symm)).elim
          · exact ((noW u um).2 (h ▸ uz.symm)).elim
          rcases split z h with p|p|p|p|p
          · exact .inl (mem_insert_of_mem p)
          · exact (noWK um p uz).elim
          · exact .inr (mem_singleton.mpr (p.trans (deny z uz p).symm))
          · exact .inr (mem_singleton.mpr (p.trans (deny' z uz p).symm))
          · exact .inl (mem_insert.mpr (.inl p)))
      simpa using f
    rcases (eqW u).mp um with h|h|⟨h,_⟩
    · have b := near (t:=x) (fun _ _ _=>rfl) (fun _ e f=>(yAf u h (f ▸ e.symm)).elim)
      omega
    · have b := near (t:=y) (fun _ e f=>(xBf u h (f ▸ e.symm)).elim) (fun _ _ _=>rfl)
      omega
    have b := near (t:=x) (fun _ _ _=>rfl) (fun _ e f=>((neutral_no h um).2 (f ▸ e.symm)).elim)
    omega
  have triple : ({x,y,e}:Finset V).card=3 := by
    have xoff : x∉({y,e}:Finset V) := by simp [xy,xe]
    rw [card_insert_of_not_mem xoff,show ({y,e}:Finset V).card=2 by simp [ye]]
  have sepD : Disjoint (W∪K) ({x,y,e}:Finset V) := by
    apply disjoint_left.mpr
    intro z zm zt
    simp only [mem_insert,mem_singleton] at zt
    rcases zt with rfl|rfl|rfl <;> rcases mem_union.mp zm with h|h
    · exact xW h
    · exact xK h
    · exact yW h
    · exact yK h
    · exact eW h
    · exact eK h
  have Dcov : W∪K∪({x,y,e}:Finset V)=Shore D := by
    ext z
    constructor
    · intro zm
      rcases mem_union.mp zm with h|h
      · exact (mem_union.mp h).elim (fun hw=>wD hw) (fun hk=>kD hk)
      simp only [mem_insert,mem_singleton] at h
      rcases h with rfl|rfl|rfl <;> assumption
    · intro zD
      have h := split z zD
      simp only [mem_union,mem_insert,mem_singleton]
      tauto
  have w6 : W.card≤6 := by
    have f := card_union_of_disjoint sepD
    rw [Dcov,big,card_union_of_disjoint disWK,triple] at f
    omega
  have common_not_both (z : V) (zm : z∈K) : ¬(G.Adj z x ∧ G.Adj z y) := by
    intro h
    have As : A⊆PositiveEven G z := by
      intro u um
      have p := even_two_three_info hc ab oa um
      have bz := dist_eq_one_iff_adj.mpr (bk z zm)
      have ne : z≠u := fun q=>by rw [q,p.2] at bz; omega
      have no : ¬G.Adj z u := by
        intro g
        have t := hc.dist_triangle (u:=b) (v:=z) (w:=u)
        rw [p.2,bz,dist_eq_one_iff_adj.mpr g] at t
        omega
      exact mem_positive.mpr ⟨ne.symm,by
        rw [(mem_filter.mp (d2 hc ne no h.1 (xA u um))).2]; decide⟩
    have Bs : B⊆PositiveEven G z := by
      intro u um
      have p := even_three_two_info hc ab ob um
      have az := dist_eq_one_iff_adj.mpr (ak z zm)
      have ne : z≠u := fun q=>by rw [q,p.1] at az; omega
      have no : ¬G.Adj z u := by
        intro g
        have t := hc.dist_triangle (u:=a) (v:=z) (w:=u)
        rw [p.1,az,dist_eq_one_iff_adj.mpr g] at t
        omega
      exact mem_positive.mpr ⟨ne.symm,by
        rw [(mem_filter.mp (d2 hc ne no h.2 (yB u um))).2]; decide⟩
    have ss := foreign_pos_even hc cd.symm (kD zm) sc (ak z zm) as'
    have not_s : s∉A∪B := by
      intro h
      exact sD ((mem_union.mp h).elim (fun h=>(mem_filter.mp h).1) (fun h=>(mem_filter.mp h).1))
    have q := (card_le_card (insert_subset_iff.mpr ⟨ss,union_subset As Bs⟩ :
      insert s (A∪B)⊆PositiveEven G z)).trans (positive_cap z even)
    rw [card_insert_of_not_mem not_s,card_union_of_disjoint disAB] at q
    omega
  have exclusiveChoice (z : V) (zm : z∈K) :
      ∃ t,∀ u,G.Adj z u → u=x ∨ u=y → u=t := by
    by_cases h : G.Adj z x
    · exact ⟨x,fun u uz q=>q.elim id (fun f=>(common_not_both z zm ⟨h,f ▸ uz⟩).elim)⟩
    exact ⟨y,fun u uz q=>q.elim (fun f=>(h (f ▸ uz)).elim) id⟩
  have nearK (z : V) (zm : z∈K) (t : V)
      (chosen : ∀ u,G.Adj z u → u=x ∨ u=y → u=t) :
      ∀ u,G.Adj z u → u=a ∨ u=b ∨ u∈K.erase z ∨ u=t ∨ u=e := by
    intro u zu
    rcases shore_closed D z (kD zm) u zu with h|h|h
    · exact .inl h
    · exact .inr (.inl h)
    rcases split u h with w|k|uX|uY|uE
    · exact (noWK w zm zu.symm).elim
    · exact .inr (.inr (.inl (mem_erase.mpr ⟨zu.ne.symm,k⟩)))
    · exact .inr (.inr (.inr (.inl (chosen u zu (.inl uX)))))
    · exact .inr (.inr (.inr (.inl (chosen u zu (.inr uY)))))
    exact .inr (.inr (.inr (.inr uE)))
  have linkK (z : V) (zm : z∈K) : ∃ v∈K,G.Adj z v := by
    apply Classical.byContradiction
    intro no
    obtain ⟨t,chosen⟩ := exclusiveChoice z zm
    let P : Finset V := {a,b,t,e}
    have sub : G.neighborFinset z⊆P := by
      intro u um
      have zu := (mem_neighborFinset G z u).mp um
      have f := nearK z zm t chosen u zu
      have nh : u∉K.erase z := fun h=>no ⟨u,(mem_erase.mp h).2,zu⟩
      simp only [P,mem_insert,mem_singleton]
      tauto
    have c := card_le_card sub
    have n : P.card≤4 := le_trans (card_insert_le _ _) <|
      Nat.add_le_add_right (le_trans (card_insert_le _ _) <|
        Nat.add_le_add_right ((card_insert_le t ({e}:Finset V)).trans (by simp)) 1) 1
    rw [card_neighborFinset_eq_degree] at c
    have h := high z (kD zm)
    omega
  have lowEk (small : (inside G W e).card≤1) : 2≤(K.filter (G.Adj e)).card := by
    have ns : G.neighborFinset e⊆inside G W e∪((inside G K e)∪({x,y}:Finset V)) := by
      intro u um
      have eu := (mem_neighborFinset G e u).mp um
      rcases shore_closed D e ed u eu with p|p|p
      · exact ((eNo e em).1 (p ▸ eu.symm)).elim
      · exact ((eNo e em).2 (p ▸ eu.symm)).elim
      rcases split u p with h|h|h|h|h
      · exact mem_union_left _ (mem_filter.mpr ⟨h,eu⟩)
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨h,eu⟩))
      · exact mem_union_right _ (mem_union_right _ (mem_insert.mpr (.inl h)))
      · exact mem_union_right _ (mem_union_right _ (mem_insert_of_mem (mem_singleton.mpr h)))
      exact (eu.ne.symm h).elim
    have c := (card_le_card ns).trans (card_union_le _ _)
    have t := card_union_le (inside G K e) ({x,y}:Finset V)
    have f : ({x,y}:Finset V).card=2 := by simp [xy]
    rw [card_neighborFinset_eq_degree] at c
    have high_e := high e ed
    change 2≤(inside G K e).card
    omega
  let F : SingletonEC1Frame G := {
    a:=a,b:=b,s:=s,x:=x,y:=y,e:=e,W:=W,K:=K,A:=A,B:=B
    xOff:=by
      obtain ⟨p,q,r⟩ := Dside xd
      simp [p,q,r,xy]
    eOff:=by
      obtain ⟨p,q,r⟩ := Dside ed
      simp [p,q,r,xe.symm,ye.symm]
    wk:=disWK
    wOff:=by
      apply disjoint_left.mpr
      intro z zw zf
      obtain ⟨ha,hb,hs⟩ := Dside (wD zw)
      simp only [mem_insert,mem_singleton] at zf
      rcases zf with h|h|h|h|h|h
      · exact ha h
      · exact hb h
      · exact hs h
      · exact xW (h ▸ zw)
      · exact yW (h ▸ zw)
      · exact eW (h ▸ zw)
    kOff:=by
      apply disjoint_left.mpr
      intro z zk zf
      obtain ⟨ha,hb,hs⟩ := Dside (kD zk)
      simp only [mem_insert,mem_singleton] at zf
      rcases zf with h|h|h|h|h|h
      · exact ha h
      · exact hb h
      · exact hs h
      · exact xK (h ▸ zk)
      · exact yK (h ▸ zk)
      · exact eK (h ▸ zk)
    cover:=by
      apply eq_univ_iff_forall.mpr
      intro z
      by_cases ha : z=a
      · simp [ha]
      by_cases hb : z=b
      · simp [hb]
      rcases cover ha hb with h|h
      · have zs : z=s := by simpa [sC] using h
        simp [zs]
      have h := split z h
      simp only [mem_insert,mem_singleton,mem_union]
      tauto
    stem:=by
      have h := RouteOn.three by'.symm bs' (Dside yd).2.2
      have aoff : a∉({y,b,s}:Finset V) :=
        by simp [ab.ne,(Dside yd).1.symm,as'.ne]
      have p := h.suffix as'.symm aoff
      have f : insert a ({y,b,s}:Finset V)={y,b,s,a} := by ext z; simp [or_left_comm,or_comm,or_assoc]
      exact f ▸ p
    ak:=ak,xA:=xA,yB:=yB,aW:=fun u h=>(eqW u).mpr (.inl h),
    bW:=fun u h=>(eqW u).mpr (.inr (.inl h)),apart:=disAB,a2:=a2',b2:=b2',
    small:=w6,k2:=k2,k3:=k3,linkK:=linkK,lowEk:=lowEk,highW:=highW }
  exact F.traceable

#print axioms traceable_of_adjacent_singleton_eleven_equal_one_unique
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
