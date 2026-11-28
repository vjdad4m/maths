import AdjacentCutFiveTwoOrderTwenty189
import AdjacentCutFiveMixedNineGeom189
import DegreeFiveFarCut189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset
open private CutGraph Shore mem_shore shore_off shore_closed shore_disjoint shore_connected shore_hit_a shore_hit_b
  from AdjacentCutFiveActual189
open private actual_two_shores from AdjacentCutFiveTwoOrderTwenty189
open private d2 foreign_subset from CrossSaturation189
open private saturation_impossible from DegreeFiveFarCut189
open private swapCut from AdjacentCutFiveMixedNineGeom189
open FiveAdjacent (shore_swapCut)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
private abbrev Cmp (G : SimpleGraph V) (a b : V) := (CutGraph (G:=G) a b).ConnectedComponent
private abbrev DeletionConnected (G : SimpleGraph V) :=
  ∀ T : Finset V,T.card<2 → (G.induce ((↑T : Set V)ᶜ)).Connected

private theorem own_far {x y : V} (hc : G.Connected) (far : 4≤G.dist a b)
    (C : Cmp G a b) (xc : x∈Shore C) (yn : y∉Shore C) (ax : G.Adj a x) (by' : G.Adj b y) :
    4≤G.dist x y := by
  have r := cross_metric (Shore C) hc xc yn (shore_closed C)
  have hi := hc.dist_triangle (u:=a) (v:=x) (w:=b)
  have hj := hc.dist_triangle (u:=a) (v:=y) (w:=b)
  have xa := dist_eq_one_iff_adj.mpr ax.symm
  have ax' := dist_eq_one_iff_adj.mpr ax
  have yb := dist_eq_one_iff_adj.mpr by'.symm
  have by'' := dist_eq_one_iff_adj.mpr by'
  omega

private theorem split_at_shore (ab : a≠b) (conn : DeletionConnected G) (C : Cmp G a b) :
    ∃ S : CrossSaturation.Split G a b,S.L=Shore C ∧ S.R=(univ : Finset V).filter (fun x=>x≠a ∧ x≠b ∧ x∉Shore C) := by
  classical
  let R := (univ : Finset V).filter fun z => z≠a ∧ z≠b ∧ z∉Shore C
  have test {z : V} : z∈R ↔ z≠a ∧ z≠b ∧ z∉Shore C := by simp [R]
  refine ⟨⟨Shore C,R,disjoint_left.mpr (fun _ hz hr=>(test.mp hr).2.2 hz),
    shore_off C,⟨fun h=>(test.mp h).1 rfl,fun h=>(test.mp h).2.1 rfl⟩,
    shore_connected C,?_,shore_hit_a ab conn C,shore_hit_b ab conn C,?_⟩,rfl,rfl⟩
  · intro u um v vm uv
    rcases shore_closed C u um v uv with h|h|h
    · exact (test.mp vm).1 h
    · exact (test.mp vm).2.1 h
    · exact (test.mp vm).2.2 h
  · intro z
    by_cases za : z=a
    · exact .inl za
    by_cases zb : z=b
    · exact .inr (.inl zb)
    by_cases zl : z∈Shore C
    · exact .inr (.inr (.inl zl))
    exact .inr (.inr (.inr (test.mpr ⟨za,zb,zl⟩)))

private noncomputable def aPorts (C : Cmp G a b) : Finset V := (Shore C).filter (G.Adj a)
private noncomputable def bPorts (C : Cmp G a b) : Finset V := (Shore C).filter (G.Adj b)
private noncomputable def aTwos (C : Cmp G a b) : Finset V := Shore C ∩ DistanceTwo G a
private noncomputable def bTwos (C : Cmp G a b) : Finset V := Shore C ∩ DistanceTwo G b

private theorem source_foreign (hc : G.Connected) (far : 4≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (C : Cmp G a b) {x : V} (xc : x∈Shore C) (ax : G.Adj a x) :
    ((G.neighborFinset a) \ aPorts C) ⊂ DistanceTwo G x := by
  classical
  obtain ⟨S,L,R⟩ := split_at_shore ab conn C
  have E : S.foreignA=(G.neighborFinset a) \ aPorts C := by
    ext z
    simp only [CrossSaturation.Split.foreignA,R,aPorts,mem_sdiff,mem_filter,mem_univ,true_and,mem_neighborFinset]
    constructor
    · rintro ⟨⟨_,_,n⟩,az⟩
      exact ⟨az,fun j=>n j.1⟩
    · rintro ⟨az,n⟩
      have zb : z≠b := by
        intro ez
        have k := dist_eq_one_iff_adj.mpr (ez ▸ az : G.Adj a b)
        omega
      exact ⟨⟨az.ne.symm,zb,fun m=>n ⟨m,az⟩⟩,az⟩
  have sx : x∈S.L := L.symm ▸ xc
  rw [←E,ssubset_iff_subset_ne]
  exact ⟨foreign_subset S hc sx ax,
    fun e=>saturation_impossible S hc far sx ax e.symm⟩

private theorem foreign_cap (hc : G.Connected) (far : 4≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤7) (ab : a≠b) (conn : DeletionConnected G)
    {C D : Cmp G a b} (cd : C≠D) :
    ((G.neighborFinset a) \ aPorts C).card≤4 := by
  obtain ⟨x,xc,ax⟩ := shore_hit_a ab conn C
  obtain ⟨y,yd,by'⟩ := shore_hit_b ab conn D
  have xy := own_far hc far C xc (fun h=>disjoint_left.mp (shore_disjoint cd) h yd) ax by'
  have bound := distanceTwo_add_two_le_even_of_far hc xy
  have small := card_lt_card (source_foreign hc far ab conn C xc ax)
  have ex := even x
  omega

private theorem local_cap (hc : G.Connected) (far : 4≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤7) (ab : a≠b) (conn : DeletionConnected G)
    {C D : Cmp G a b} (cd : C≠D) : (aPorts C).card≤4 := by
  apply le_trans _ (foreign_cap hc far even ab conn cd.symm)
  apply card_le_card
  intro z zp
  have ⟨zc,az⟩ := mem_filter.mp zp
  exact mem_sdiff.mpr ⟨(mem_neighborFinset _ _ _).mpr az,
    fun q=>disjoint_left.mp (shore_disjoint cd) zc (mem_filter.mp q).1⟩

private theorem caps_terminal (hc : G.Connected) (far : 4≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤7) (ab : a≠b) (conn : DeletionConnected G)
    {C D : Cmp G a b} (cd : C≠D) :
    G.degree a≤8 ∧ (DistanceTwo G a).card≤5 := by
  classical
  have f := foreign_cap hc far even ab conn cd
  have p := local_cap hc far even ab conn cd
  have s : aPorts C⊆G.neighborFinset a := fun _ h=>(mem_neighborFinset _ _ _).mpr (mem_filter.mp h).2
  have t := card_sdiff_add_card_eq_card s
  rw [card_neighborFinset_eq_degree] at t
  have e := distanceTwo_add_two_le_even_of_far hc far
  have q := even a
  omega

private theorem shore_degree_bound (hc : G.Connected) (far : 4≤G.dist a b)
    (C : Cmp G a b) {x : V} (xc : x∈Shore C) (ax : G.Adj a x) :
    G.degree x≤(aPorts C).card+(aTwos C).card := by
  classical
  have xp : x∈aPorts C := mem_filter.mpr ⟨xc,ax⟩
  have sub : G.neighborFinset x⊆insert a (((aPorts C).erase x) ∪ aTwos C) := by
    intro z hz
    have xz := (mem_neighborFinset _ _ _).mp hz
    rcases shore_closed C x xc z xz with rfl|rfl|zc
    · exact mem_insert_self _ _
    · have h := G.dist_le (Walk.cons ax (Walk.cons xz .nil))
      simp at h
      omega
    by_cases az : G.Adj a z
    · exact mem_insert_of_mem (mem_union_left _ (mem_erase.mpr ⟨xz.ne.symm,mem_filter.mpr ⟨zc,az⟩⟩))
    have az' : a≠z := fun e=>(shore_off C).1 (e.symm ▸ zc)
    exact mem_insert_of_mem (mem_union_right _ (mem_inter.mpr ⟨zc,d2 hc az' az ax xz⟩))
  have c := card_le_card sub
  rw [card_neighborFinset_eq_degree] at c
  have w := card_insert_le a (((aPorts C).erase x) ∪ aTwos C)
  have k := card_union_le ((aPorts C).erase x) (aTwos C)
  have p := card_erase_add_one xp
  omega

private theorem two_local_counts (A B : Finset V) (d : Disjoint A B) (W : Finset V)
    (al : A⊆W) (bl : B⊆W) : A.card+B.card≤W.card := by
  have h := card_le_card (union_subset al bl)
  rwa [card_union_of_disjoint d] at h

private theorem three_local_counts (A B C : Finset V)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C) (W : Finset V)
    (al : A⊆W) (bl : B⊆W) (cl : C⊆W) : A.card+B.card+C.card≤W.card := by
  have h := two_local_counts (A∪B) C (disjoint_union_left.mpr ⟨ac,bc⟩) W (union_subset al bl) cl
  rwa [card_union_of_disjoint ab] at h

private theorem no_far_with_all_ports_high (hc : G.Connected) (far : 4≤G.dist a b)
    (even : ∀ x,(EvenFrom G x).card≤7) (ab : a≠b) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cut : 2≤Nat.card (Cmp G a b)) (high : ∀ x,G.Adj a x → 6≤G.degree x) :
    False := by
  classical
  have lower (C : Cmp G a b) : 6≤(aPorts C).card+(aTwos C).card := by
    obtain ⟨x,xc,ax⟩ := shore_hit_a ab conn C
    exact (high x ax).trans (shore_degree_bound hc far C xc ax)
  have pD {C D : Cmp G a b} (h : C≠D) : Disjoint (aPorts C) (aPorts D) :=
    (shore_disjoint h).mono (filter_subset _ _) (filter_subset _ _)
  have qD {C D : Cmp G a b} (h : C≠D) : Disjoint (aTwos C) (aTwos D) :=
    (shore_disjoint h).mono inter_subset_left inter_subset_left
  have pSub (C : Cmp G a b) : aPorts C⊆G.neighborFinset a :=
    fun _ h=>(mem_neighborFinset _ _ _).mpr (mem_filter.mp h).2
  have qSub (C : Cmp G a b) : aTwos C⊆DistanceTwo G a := inter_subset_right
  have two : Nat.card (Cmp G a b)=2 := by
    by_contra h
    have big : 3≤Nat.card (Cmp G a b) := by omega
    haveI : Finite (Cmp G a b) := Finite.of_surjective (CutGraph (G:=G) a b).connectedComponentMk (fun c=>c.exists_rep)
    letI : Fintype (Cmp G a b) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at big
    let e := Fintype.equivFin (Cmp G a b)
    let C := e.symm ⟨0,by omega⟩
    let D := e.symm ⟨1,by omega⟩
    let E := e.symm ⟨2,by omega⟩
    have cd : C≠D := fun z=>Nat.zero_ne_one (congrArg Fin.val (e.symm.injective z))
    have ce : C≠E := fun z=>(by decide : (0:Nat)≠2) (congrArg Fin.val (e.symm.injective z))
    have de : D≠E := fun z=>(by decide : (1:Nat)≠2) (congrArg Fin.val (e.symm.injective z))
    have p := three_local_counts _ _ _ (pD cd) (pD ce) (pD de) _ (pSub C) (pSub D) (pSub E)
    have q := three_local_counts _ _ _ (qD cd) (qD ce) (qD de) _ (qSub C) (qSub D) (qSub E)
    rw [card_neighborFinset_eq_degree] at p
    obtain ⟨capA,capQ⟩ := caps_terminal hc far even ab conn cd
    have lc := lower C
    have ld := lower D
    have le := lower E
    omega
  obtain ⟨C,D,cd,cover⟩ := actual_two_shores two
  have p_C := local_cap hc far even ab conn cd
  have p_D := local_cap hc far even ab conn cd.symm
  have q := two_local_counts _ _ (qD cd) _ (qSub C) (qSub D)
  obtain ⟨_,capQ⟩ := caps_terminal hc far even ab conn cd
  have lc := lower C
  have ld := lower D
  have finish (C D : Cmp G a b) (cd : C≠D)
      (cover : ∀ {z : V},z≠a → z≠b → z∈Shore C ∨ z∈Shore D)
      (four : (aPorts D).card=4) : False := by
    obtain ⟨x,xc,ax⟩ := shore_hit_a ab conn C
    have sub : aPorts D⊆(G.neighborFinset a)\aPorts C := by
      intro z h
      exact mem_sdiff.mpr ⟨pSub D h,fun g=>disjoint_left.mp (pD cd) g h⟩
    have lt := card_lt_card (source_foreign hc far ab conn C xc ax)
    have five : 5≤(DistanceTwo G x).card := by
      have l := card_le_card sub
      omega
    have nr (z : V) : G.dist x z≤4 := by
      by_contra bad
      have l := twoEvenLayers_of_radius_five hc 2 conn (x:=x) (y:=z) (by omega)
      have k := even x
      omega
    have dose : (bPorts D).card≤1 := by
      have sub' : bPorts D⊆Shell G x 4 := by
        intro y hy
        have ⟨yd,by'⟩ := mem_filter.mp hy
        have ge := own_far hc far C xc (fun h=>disjoint_left.mp (shore_disjoint cd) h yd) ax by'
        exact mem_shell.mpr (by have l := nr y; omega)
      have k := card_le_card sub'
      have dos := shell_two_four_le_of_even (d:=6) (even x)
      rw [shell_two] at dos
      omega
    obtain ⟨y,yd,by'⟩ := shore_hit_b ab conn D
    have ypos : y∈bPorts D := mem_filter.mpr ⟨yd,by'⟩
    have sing : bPorts D={y} :=
      (eq_of_subset_of_card_le (singleton_subset_iff.mpr ypos) (by simpa using dose)).symm
    have far' : 4≤G.dist b a := by rwa [dist_comm]
    -- Count b-neighbors in the other shore by using an a-port there as a far witness.
    have bcap : (bPorts C).card≤4 := by
      -- Terminal exchange carries the same two shores to the reflected cut.
      have t := local_cap (a:=b) (b:=a) hc far' even ab.symm conn
        (C:=swapCut C) (D:=swapCut D) (fun h=>cd (swapCut.injective h))
      simpa only [aPorts,bPorts,shore_swapCut] using t
    have bdeg : G.degree b≤5 := by
      have sub' : G.neighborFinset b⊆bPorts C∪bPorts D := by
        intro z hz
        have bz := (mem_neighborFinset _ _ _).mp hz
        have za : z≠a := by
          intro eq
          have f := dist_eq_one_iff_adj.mpr (eq ▸ bz : G.Adj b a)
          omega
        rcases cover za bz.ne.symm with h|h
        · exact mem_union_left _ (mem_filter.mpr ⟨h,bz⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨h,bz⟩)
      have p := card_le_card sub'
      rw [card_neighborFinset_eq_degree] at p
      have k := card_union_le (bPorts C) (bPorts D)
      omega
    have yhigh := (degree y b by'.ne.symm).resolve_right (by omega)
    have ytwos : 5≤(bTwos D).card := by
      have t := shore_degree_bound (a:=b) (b:=a) hc far' (swapCut D) (by simpa only [shore_swapCut] using yd) by'
      have t' : G.degree y≤(bPorts D).card+(bTwos D).card := by
        simpa only [aPorts,bPorts,aTwos,bTwos,shore_swapCut] using t
      omega
    have c2 : 1≤(bTwos C).card := by
      obtain ⟨w,wc,bw⟩ := shore_hit_b ab conn C
      obtain ⟨v,vc,av⟩ := shore_hit_a ab conn C
      let U : Set V := ↑(Shore C)
      obtain ⟨p⟩ := (shore_connected C).preconnected (⟨w,wc⟩ : U) (⟨v,vc⟩ : U)
      by_contra zero
      have step {s t : U} (q : (G.induce U).Walk s t) : G.Adj b s.val → G.Adj b t.val := by
        induction q with
        | nil => exact id
        | @cons i j k ij q ih =>
          intro a0
          apply ih
          by_contra bad
          have jc : j.val∈Shore C := Finset.mem_coe.mp j.property
          have jb : b≠j.val := fun e=>(shore_off C).2 ((congrArg (fun v=>v∈Shore C) e.symm).mp jc)
          have m : j.val∈bTwos C := mem_inter.mpr ⟨jc,d2 hc jb bad a0 (show G.Adj i.val j.val from ij)⟩
          have q := card_pos.mpr ⟨_,m⟩
          omega
      have bv := step p bw
      have g := G.dist_le (Walk.cons av (Walk.cons bv.symm .nil))
      simp at g
      omega
    have dT : Disjoint (bTwos C) (bTwos D) := (shore_disjoint cd).mono inter_subset_left inter_subset_left
    have qT := two_local_counts _ _ dT (DistanceTwo G b) inter_subset_right inter_subset_right
    have e3 := distanceTwo_add_two_le_even_of_far hc far'
    have b7 := even b
    omega
  by_cases h : (aPorts D).card=4
  · exact finish C D cd cover h
  exact finish D C cd.symm (fun za zb=>(cover za zb).symm) (by omega)

/-- For the exact order-six threshold, every actual two-vertex separator has
terminal distance at most three (no restriction on the number of shores). -/
theorem separating_pair_distance_le_three_at_six (hc : G.Connected) (ab : a≠b)
    (even : ∀ x,(EvenFrom G x).card≤7) (conn : DeletionConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cut : 2≤Nat.card (Cmp G a b)) :
    G.dist a b≤3 := by
  classical
  by_contra h
  have far : 4≤G.dist a b := by omega
  by_cases high : ∀ x,G.Adj a x → 6≤G.degree x
  · exact no_far_with_all_ports_high hc far even ab conn degree cut high
  push_neg at high
  obtain ⟨x,ax,low⟩ := high
  have highB (y : V) (by' : G.Adj b y) : 6≤G.degree y := by
    have ne : y≠x := by
      intro eq
      have hi := G.dist_le (Walk.cons ax (Walk.cons (eq ▸ by').symm .nil))
      simp at hi
      omega
    exact (degree y x ne).resolve_right (by omega)
  have cut' : 2≤Nat.card (Cmp G b a) := by
    rw [←Nat.card_congr (swapCut (G:=G) (a:=a) (b:=b))]
    exact cut
  exact no_far_with_all_ports_high hc (by rwa [dist_comm]) even ab.symm conn degree cut' highB

#print axioms separating_pair_distance_le_three_at_six
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
