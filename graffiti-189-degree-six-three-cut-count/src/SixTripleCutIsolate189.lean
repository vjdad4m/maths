import SixTripleCutFourShore189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
open scoped BigOperators
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.sum_cards_le from SixTripleCutFourShore189
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem isolated_port_precise {S A : Finset V} (sh : Shore G S A)
    (hc : G.Connected) {a x : V} (isolated : ∀ y∈S,y≠a → ¬ G.Adj a y)
    (xp : x∈ports G A a) :
    G.degree x≤(ports G A a).card+(localTwo G A a).card+(S∩DistanceTwo G a).card := by
  classical
  let P := ports G A a
  let Q := localTwo G A a
  let R := S∩DistanceTwo G a
  let M := P∪Q
  have px : x∈M := mem_union_left _ xp
  have sub : G.neighborFinset x⊆insert a (M.erase x ∪ R) := by
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
    · exact mem_union_right _ (mem_inter.mpr
        ⟨yS,two_of_common hc (Ne.symm ya) (isolated y yS ya) (mem_filter.mp xp).2 xy⟩)
  have c := card_le_card sub
  rw [card_neighborFinset_eq_degree] at c
  have dep := card_insert_le a (M.erase x ∪ R)
  have hu := card_union_le (M.erase x) R
  have hm := card_union_le P Q
  change M.card≤P.card+Q.card at hm
  rw [card_erase_of_mem px] at hu
  have pos := card_pos.mpr ⟨x,px⟩
  change G.degree x≤P.card+Q.card+R.card
  omega

private theorem all_adj_of_no_internal_two (hc : G.Connected) {A : Finset V}
    (ac : (G.induce (↑A : Set V)).Connected) {x : V} (xa : x∈A)
    (no : ∀ z∈A,z∉DistanceTwo G x) : ∀ z∈A,z=x ∨ G.Adj x z := by
  intro z za
  let X : Set V := ↑A
  obtain ⟨p⟩ := ac.preconnected (⟨x,xa⟩ : X) (⟨z,za⟩ : X)
  have walk {u v : X} (q : (G.induce X).Walk u v) :
      (u.val=x ∨ G.Adj x u.val) → (v.val=x ∨ G.Adj x v.val) := by
    induction q with
    | nil => exact id
    | @cons u w v uw q ih =>
      intro h
      apply ih
      by_cases wx : w.val=x
      · exact Or.inl wx
      right
      change G.Adj u.val w.val at uw
      rcases h with xu|adj
      · exact xu ▸ uw
      by_contra bad
      exact no w.val w.property (two_of_common hc (Ne.symm wx) bad adj uw)
  exact walk p (Or.inl rfl)

private theorem low_of_small_nonport {S A : Finset V} (sh : Shore G S A)
    (ss : S.card=3) (aa : A.card=4) {a z : V} (as' : a∈S) (za : z∈A)
    (miss : z∉ports G A a) : G.degree z<6 := by
  have notadj : ¬G.Adj z a := fun e => miss (mem_filter.mpr ⟨za,e.symm⟩)
  have inc : G.neighborFinset z⊆A.erase z∪S.erase a := by
    intro w wm
    have zw := (G.mem_neighborFinset ..).mp wm
    rcases sh.closed z za w zw with wa|ws
    · exact mem_union_left _ (mem_erase.mpr ⟨zw.ne.symm,wa⟩)
    · exact mem_union_right _ (mem_erase.mpr ⟨fun e=>notadj (e ▸ zw),ws⟩)
  have cnt := (card_le_card inc).trans (card_union_le _ _)
  rw [card_neighborFinset_eq_degree,card_erase_of_mem za,card_erase_of_mem as',aa,ss] at cnt
  omega

/-- When one terminal is isolated inside a three-cut, three connected
shores cannot each offer that terminal a vertex of degree at least six.
The even cap leaves both extra terminal slots used and at most four
local distance-two slots; one small saturated shore then has two low
vertices, or two such shores each have one. -/
theorem not_three_high_port_shores_at_isolated_terminal
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S : Finset V} (ss : S.card=3) (A : Fin 3→Finset V)
    (sh : ∀ i,Shore G S (A i)) (conn : ∀ i,(G.induce (↑(A i) : Set V)).Connected)
    (dis : Pairwise fun i j => Disjoint (A i) (A j))
    {a : V} (as' : a∈S) (isolated : ∀ y∈S,y≠a → ¬ G.Adj a y)
    (hi : ∀ i, ∃ x∈ports G (A i) a,6≤G.degree x) : False := by
  classical
  let p (i : Fin 3) := (ports G (A i) a).card
  let q (i : Fin 3) := (localTwo G (A i) a).card
  let P := ∑ i,p i
  let Q := ∑ i,q i
  let R := S∩DistanceTwo G a
  have rc : R.card≤2 := by
    have sub : R⊆S.erase a := by
      intro x xm
      have d := (mem_inter.mp xm).2
      refine mem_erase.mpr ⟨?_,(mem_inter.mp xm).1⟩
      rintro rfl
      simp [DistanceTwo,SimpleGraph.dist_self] at d
    have b := card_le_card sub
    rwa [card_erase_of_mem as',ss] at b
  let U := univ.biUnion (fun i : Fin 3 => localTwo G (A i) a)
  have qU : U.card=Q := card_biUnion (fun i _ j _ ne => (dis ne).mono inter_subset_left inter_subset_left)
  have ud : Disjoint R U := by
    apply disjoint_left.mpr
    intro z zr zu
    obtain ⟨i,_,zi⟩ := mem_biUnion.mp zu
    exact disjoint_left.mp (sh i).disjoint (mem_inter.mp zi).1 (mem_inter.mp zr).1
  have ucap := (card_le_card (show R∪U⊆DistanceTwo G a from by
    apply union_subset inter_subset_right
    intro z zu
    obtain ⟨i,_,zi⟩ := mem_biUnion.mp zu
    exact (mem_inter.mp zi).2)).trans (distanceTwo_le_of_even 6 a (cap a))
  rw [card_union_of_disjoint ud,qU] at ucap
  have ch (i : Fin 3) : 6≤p i+q i+R.card := by
    obtain ⟨x,xm,h⟩ := hi i
    exact h.trans (isolated_port_precise (sh i) hc isolated xm)
  have weak (i : Fin 3) : 4≤p i+q i := by have c := ch i; omega
  have ext (i : Fin 3) : (∑ j∈univ.erase i,p j)≤6 := by
    obtain ⟨x,xp,_⟩ := hi i
    exact (Graffiti189LongestPath.ThresholdSix.ThreeCut.sum_cards_le (univ.erase i)
      (fun j=>ports G (A j) a)
      (fun _ _ h=>(dis h).mono (filter_subset _ _) (filter_subset _ _))
      (fun j jm _ yj=>(sh i).foreign_distance_two (sh j) (dis (mem_erase.mp jm).1.symm) hc xp yj))
      |>.trans (distanceTwo_le_of_even 6 x (cap x))
  have sc (i : Fin 3) : (∑ j∈univ.erase i,p j)+p i=P := sum_erase_add univ p (mem_univ i)
  have pc (i : Fin 3) : P≤6+p i := by have c:=ext i; have s:=sc i; omega
  have pe : P=p 0+p 1+p 2 := sum_fin_three p
  have qe : Q=q 0+q 1+q 2 := sum_fin_three q
  have pcap : P≤9 := by have x:=pc 0; have y:=pc 1; have z:=pc 2; omega
  have rb : R.card=2 := by have x:=ch 0; have y:=ch 1; have z:=ch 2; omega
  have pbase : 8≤P := by have x:=ch 0; have y:=ch 1; have z:=ch 2; omega
  have qc : Q≤4 := by omega
  have sat (i : Fin 3) (full : (∑ j∈univ.erase i,p j)=6) : (A i).card=p i+q i := by
    obtain ⟨x,xp,_⟩ := hi i
    let L := (univ.erase i).biUnion (fun j => ports G (A j) a)
    have size : L.card=6 := by
      have h := card_biUnion (s:=univ.erase i) (t:=fun j=>ports G (A j) a)
        (fun u _ v _ ne=>(dis ne).mono (filter_subset _ _) (filter_subset _ _))
      exact h.trans full
    have lsub : L⊆DistanceTwo G x := by
      intro u um
      obtain ⟨j,jm,up⟩ := mem_biUnion.mp um
      exact (sh i).foreign_distance_two (sh j) (dis (mem_erase.mp jm).1.symm) hc xp up
    have eq : L=DistanceTwo G x := eq_of_subset_of_card_le lsub (by
      rw [size]; exact distanceTwo_le_of_even 6 x (cap x))
    have no (z : V) (zi : z∈A i) : z∉DistanceTwo G x := by
      rw [←eq]
      intro zm
      obtain ⟨j,jm,zj⟩ := mem_biUnion.mp zm
      exact disjoint_left.mp (dis (mem_erase.mp jm).1.symm) zi (mem_filter.mp zj).1
    have adj := all_adj_of_no_internal_two hc (conn i) (mem_filter.mp xp).1 no
    have cover : ports G (A i) a ∪ localTwo G (A i) a=A i := by
      ext z
      constructor
      · intro zz
        exact (mem_union.mp zz).elim (fun t=>(mem_filter.mp t).1) (fun t=>(mem_inter.mp t).1)
      · intro zi
        by_cases az : G.Adj a z
        · exact mem_union_left _ (mem_filter.mpr ⟨zi,az⟩)
        have zx : z≠x := fun e=>az (e ▸ (mem_filter.mp xp).2)
        have na : a≠z := fun e=>disjoint_left.mp (sh i).disjoint zi (e ▸ as')
        exact mem_union_right _ (mem_inter.mpr ⟨zi,two_of_common hc na az (mem_filter.mp xp).2
          ((adj z zi).resolve_left zx)⟩)
    have pd : Disjoint (ports G (A i) a) (localTwo G (A i) a) := by
      apply disjoint_left.mpr
      intro z zp zq
      have m : G.dist a z=1 := dist_eq_one_iff_adj.mpr (mem_filter.mp zp).2
      have n : G.dist a z=2 := by simpa [DistanceTwo] using (mem_inter.mp zq).2
      omega
    exact (congrArg Finset.card cover).symm.trans (card_union_of_disjoint pd)
  have sat_four (i : Fin 3) (pi : p i+q i=4) (fi : P=p i+6) :
      (A i).card=4 := by
    have u := sc i
    have f : (∑ j∈univ.erase i,p j)=6 := by omega
    exact (sat i f).trans pi
  have sum_rem (i : Fin 3) : (∑ j∈univ.erase i,q j)+q i=Q := sum_erase_add univ q (mem_univ i)
  by_cases p9 : P=9
  · have peq (i : Fin 3) : p i=3 := by
      have b0:=pc 0; have b1:=pc 1; have b2:=pc 2
      rcases (show i=0 ∨ i=1 ∨ i=2 from (by decide : ∀ j : Fin 3,j=0 ∨ j=1 ∨ j=2) i) with rfl|rfl|rfl <;> omega
    have qpos (i : Fin 3) : 1≤q i := by have h:=weak i; rw [peq i] at h; omega
    have two : (q 0=1 ∧ q 1=1) ∨ (q 0=1 ∧ q 2=1) ∨ (q 1=1 ∧ q 2=1) := by
      have k0:=qpos 0; have k1:=qpos 1; have k2:=qpos 2
      omega
    have low (i : Fin 3) (qi : q i=1) : ∃ z∈A i,G.degree z<6 := by
      have s := sat_four i (by rw [peq i,qi]) (by rw [peq i,p9])
      let D := A i \ ports G (A i) a
      have d : 0<D.card := by
        dsimp [D]
        have incl : ports G (A i) a⊆A i := filter_subset _ _
        rw [card_sdiff incl,s]
        change 0<4-p i
        rw [peq i]
        decide
      obtain ⟨z,zm⟩ := card_pos.mp d
      exact ⟨z,(mem_sdiff.mp zm).1,low_of_small_nonport (sh i) ss s as'
        (mem_sdiff.mp zm).1 (mem_sdiff.mp zm).2⟩
    have clash {i j : Fin 3} (ij : i≠j) (qi : q i=1) (qj : q j=1) : False := by
      obtain ⟨x,xm,xl⟩ := low i qi
      obtain ⟨y,ym,yl⟩ := low j qj
      have xy : x≠y := fun e=>disjoint_left.mp (dis ij) xm (e ▸ ym)
      rcases degree x y xy with h|h <;> omega
    rcases two with ⟨b,c⟩|⟨b,c⟩|⟨b,c⟩
    · exact clash (show (0:Fin 3)≠1 by decide) b c
    · exact clash (show (0:Fin 3)≠2 by decide) b c
    · exact clash (show (1:Fin 3)≠2 by decide) b c
  · have p8 : P=8 := by omega
    have small : ∃ i,p i≤2 := by
      by_cases ex : ∃ i : Fin 3,p i≤2
      · exact ex
      exfalso
      have h0 : ¬p 0≤2 := fun h=>ex ⟨0,h⟩
      have h1 : ¬p 1≤2 := fun h=>ex ⟨1,h⟩
      have h2 : ¬p 2≤2 := fun h=>ex ⟨2,h⟩
      omega
    obtain ⟨i,pi⟩ := small
    have p2 : p i=2 := by have e:=pc i; omega
    have r : (∑ j∈univ.erase i,p j)=6 := by have h:=sc i; omega
    have cost := sum_le_sum (s:=univ.erase i) (f:=fun _=>(4:Nat)) (g:=fun j=>p j+q j)
      (fun j _=>weak j)
    have count : ((univ:Finset (Fin 3)).erase i).card=2 := by
      rw [card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin]
    simp only [sum_const,count,nsmul_eq_mul,sum_add_distrib] at cost
    change 8≤(∑ j∈univ.erase i,p j)+(∑ j∈univ.erase i,q j) at cost
    rw [r] at cost
    have q2 : q i=2 := by have s:=sum_rem i; have w:=weak i; omega
    have s := sat_four i (by rw [p2,q2]) (by rw [p8,p2])
    let D := A i \ ports G (A i) a
    have d : D.card=2 := by
      have incl : ports G (A i) a⊆A i := filter_subset _ _
      dsimp [D]
      rw [card_sdiff incl,s]
      change 4-p i=2
      rw [p2]
    obtain ⟨x,y,xy,eq⟩ := card_eq_two.mp d
    have xm : x∈D := eq ▸ mem_insert_self _ _
    have ym : y∈D := eq ▸ mem_insert_of_mem (mem_singleton_self _)
    have xl := low_of_small_nonport (sh i) ss s as' (mem_sdiff.mp xm).1 (mem_sdiff.mp xm).2
    have yl := low_of_small_nonport (sh i) ss s as' (mem_sdiff.mp ym).1 (mem_sdiff.mp ym).2
    rcases degree x y xy with h|h <;> omega

#print axioms not_three_high_port_shores_at_isolated_terminal
end Graffiti189LongestPath.ThresholdSix.ThreeCut
