import SixOrder24BThreeExcluded189
import SixLayer25Cover189
import Mathlib.Tactic.NormNum

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private distance_on_geodesic mem_distanceTwo dist_two from SmallSeparator189

variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

structure Layer24Cover (G : SimpleGraph V) (x : V) [DecidableRel G.Adj] where
  T : Finset V
  rep : V → V
  selected : T ⊆ Shell G x 1
  tSize : T.card = 3 ∨ T.card = 4
  firstSize : (Shell G x 1).card = 6
  thirdSize : (Shell G x 3).card = 11 ∨ (Shell G x 3).card = 12
  secondMin : 4 ≤ (Shell G x 2).card
  evenMax : (Shell G x 2).card+(Shell G x 4).card ≤ 6
  shellTotal : (Shell G x 2).card+(Shell G x 3).card+(Shell G x 4).card=17
  radius : ∀ y, G.dist x y ≤ 4
  groupBound : ∀ a ∈ T, (Layer25Group G x a).card ≤ 7 - T.card
  groupCover : Shell G x 3 ⊆ T.biUnion (Layer25Group G x)
  repDepth : ∀ a ∈ T, G.dist x (rep a) = 2
  repAdj : ∀ a ∈ T, G.Adj a (rep a)
  repPrivate : ∀ a ∈ T, ∀ b ∈ T, b ≠ a → ¬ G.Adj b (rep a)
  repWitness : ∀ a ∈ T, ∃ c ∈ Layer25Group G x a, G.Adj (rep a) c ∧
      ∀ b∈T,b≠a → c∉Layer25Group G x b
  d2Exact : ∀ a ∈ T, (Layer25Group G x a).card=7-T.card → DistanceTwo G a =
    Layer25Group G x a ∪ (T.erase a).image (fun b => if G.Adj a b then rep b else b)
  joinRest : ∀ a ∈ T, (Layer25Group G x a).card=7-T.card →
    ∀ b ∈ Shell G x 1, b ∉ T → G.Adj a b

theorem layer_cover_at_order_twenty_four_with_radius_frame
    (hc : G.Connected) (cap : ∀ v, (EvenFrom G v).card ≤ 7)
    (x : V) (dx : G.degree x = 6) (n : Fintype.card V = 24)
    (diam : ∀ y, G.dist x y ≤ 4) (p2lower : 4 ≤ (Shell G x 2).card) :
    Nonempty (Layer24Cover G x) := by
  classical
  let A := Shell G x 1
  let C := Shell G x 3
  let f := Layer25Group G x
  have eqA : A = G.neighborFinset x := by
    ext a
    rw [mem_shell,G.mem_neighborFinset,dist_eq_one_iff_adj]
  have cA : A.card ≤ 6 := by
    rw [eqA,G.card_neighborFinset_eq_degree]
    exact dx.le
  have bd (u : V) : (DistanceTwo G u).card ≤ 6 :=
    distanceTwo_le_of_even 6 u (cap u)
  have aDepth {a : V} (am : a ∈ A) : G.dist x a = 1 := mem_shell.mp am
  have cDepth {c : V} (cm : c ∈ C) : G.dist x c = 3 := mem_shell.mp cm
  have d2_of_middle {a b c : V} (da : G.dist x a = 1) (dc : G.dist x c = 3)
      (ab : G.Adj a b) (bc : G.Adj b c) : G.dist a c = 2 := by
    have ne : a ≠ c := by intro e; rw [e] at da; omega
    have na : ¬ G.Adj a c := by
      intro ac
      have e := dist_eq_one_iff_adj.mpr ac
      have t := hc.dist_triangle (u:=x) (v:=a) (w:=c)
      omega
    exact dist_two hc ne na ab bc
  have coverA : C ⊆ A.biUnion f := by
    intro c cm
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x c
    have len : p.length = 3 := hp.trans (cDepth cm)
    let a := p.getVert 1
    let b := p.getVert 2
    have ap : G.dist x a = 1 := distance_on_geodesic hc p hp 1 (by omega)
    have ab : G.Adj a b := p.adj_getVert_succ (i:=1) (by omega)
    have bc : G.Adj b c := by
      have e := p.adj_getVert_succ (i:=2) (by omega)
      have e3 : p.getVert 3 = c := by rw [← len,getVert_length]
      simpa only [e3] using e
    exact mem_biUnion.mpr ⟨a,mem_shell.mpr ap,mem_inter.mpr
      ⟨cm,mem_distanceTwo.mpr (d2_of_middle ap (cDepth cm) ab bc)⟩⟩
  let fam := A.powerset.filter (fun T : Finset V => C ⊆ T.biUnion f)
  have fn : fam.Nonempty := ⟨A,mem_filter.mpr ⟨mem_powerset.mpr (Subset.rfl),coverA⟩⟩
  obtain ⟨T, Tfam, minT⟩ := exists_min_image fam (fun S : Finset V => S.card) fn
  have TA : T ⊆ A := mem_powerset.mp (mem_filter.mp Tfam).1
  have cover : C ⊆ T.biUnion f := (mem_filter.mp Tfam).2
  have ts : T.card ≤ 6 := (card_le_card TA).trans cA
  have uniqueMiddle (a : V) (ha : a ∈ T) :
      ∃ b : V, G.dist x b = 2 ∧ G.Adj a b ∧
      (∀ z ∈ T, z ≠ a → ¬ G.Adj z b) ∧ ∃ c ∈ f a, G.Adj b c ∧
        ∀ z∈T,z≠a → c∉f z := by
    have lost : ¬ C ⊆ (T.erase a).biUnion f := by
      intro hs
      have m : T.erase a ∈ fam := mem_filter.mpr ⟨mem_powerset.mpr
        ((erase_subset a T).trans TA),hs⟩
      have e := minT (T.erase a) m
      have cd := card_erase_add_one ha
      omega
    obtain ⟨c, cm, miss⟩ := not_subset.mp lost
    have ac : c ∈ f a := by
      obtain ⟨z,zm,zc⟩ := mem_biUnion.mp (cover cm)
      by_cases za : z = a
      · exact za ▸ zc
      · exact (miss (mem_biUnion.mpr ⟨z,mem_erase.mpr ⟨za,zm⟩,zc⟩)).elim
    have d2 := mem_distanceTwo.mp (mem_inter.mp ac).2
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist a c
    have len : p.length = 2 := hp.trans d2
    let b := p.getVert 1
    have ab : G.Adj a b := by simpa [b] using p.adj_getVert_succ (i:=0) (by omega)
    have bc : G.Adj b c := by
      have e := p.adj_getVert_succ (i:=1) (by omega)
      have e2 : p.getVert 2 = c := by rw [← len,getVert_length]
      simpa only [e2] using e
    have da := aDepth (TA ha)
    have dc := cDepth cm
    have d_ab := dist_eq_one_iff_adj.mpr ab
    have d_bc := dist_eq_one_iff_adj.mpr bc
    have t1 := hc.dist_triangle (u:=x) (v:=a) (w:=b)
    have t2 := hc.dist_triangle (u:=x) (v:=b) (w:=c)
    have db : G.dist x b = 2 := by omega
    have privateC (z : V) (zT : z∈T) (ne : z≠a) : c∉f z := fun zc=>
      miss (mem_biUnion.mpr ⟨z,mem_erase.mpr ⟨ne,zT⟩,zc⟩)
    refine ⟨b, db, ab, ?_, ⟨c,ac,bc,privateC⟩⟩
    intro z zT ne zb
    have zc : c ∈ f z := mem_inter.mpr ⟨cm,mem_distanceTwo.mpr
      (d2_of_middle (aDepth (TA zT)) dc zb bc)⟩
    exact privateC z zT ne zc
  let rep (a : V) := if h : a ∈ T then Classical.choose (uniqueMiddle a h) else x
  have prop {a : V} (ha : a ∈ T) :
      G.dist x (rep a) = 2 ∧ G.Adj a (rep a) ∧
      (∀ z ∈ T, z ≠ a → ¬ G.Adj z (rep a)) ∧ ∃ c ∈ f a, G.Adj (rep a) c ∧
        ∀ z∈T,z≠a → c∉f z := by
    simpa [rep, dif_pos ha] using Classical.choose_spec (uniqueMiddle a ha)
  have fData (a : V) (ha : a ∈ T) :
      (f a).card ≤ 7 - T.card ∧
      ∃ R : Finset V, R = (T.erase a).image (fun b => if G.Adj a b then rep b else b) ∧
        R.card + 1 = T.card ∧ Disjoint (f a) R ∧ f a ∪ R ⊆ DistanceTwo G a := by
    let U := T.erase a
    let ch (b : V) := if G.Adj a b then rep b else b
    have good (b : V) (hb : b ∈ U) : ch b ∈ DistanceTwo G a ∧ G.dist x (ch b) ≤ 2 := by
      obtain ⟨ba,bm⟩ := mem_erase.mp hb
      have pr := prop bm
      have bd := aDepth (TA bm)
      by_cases ab : G.Adj a b
      · have ne : a ≠ rep b := by
          intro h
          have d := aDepth (TA ha)
          rw [h] at d
          have e := pr.1
          omega
        simp only [ch,if_pos ab,mem_distanceTwo]
        exact ⟨dist_two hc ne (pr.2.2.1 a ha ba.symm) ab pr.2.1,pr.1.le⟩
      · have ax : G.Adj a x := (dist_eq_one_iff_adj.mp (aDepth (TA ha))).symm
        have xb : G.Adj x b := dist_eq_one_iff_adj.mp bd
        simp only [ch,if_neg ab,mem_distanceTwo]
        exact ⟨dist_two hc ba.symm ab ax xb,bd.le.trans (by decide)⟩
    have inj : ∀ b ∈ U, ∀ c ∈ U, ch b = ch c → b = c := by
      intro b hb c hc' eq
      have bm := (mem_erase.mp hb).2
      have cm := (mem_erase.mp hc').2
      have bp := prop bm
      have cp := prop cm
      have b1 := aDepth (TA bm)
      have c1 := aDepth (TA cm)
      by_cases ab : G.Adj a b <;> by_cases ac : G.Adj a c
      · simp only [ch,if_pos ab,if_pos ac] at eq
        apply Classical.byContradiction
        intro ne
        exact cp.2.2.1 b bm ne (eq ▸ bp.2.1)
      · simp only [ch,if_pos ab,if_neg ac] at eq
        have d := bp.1
        rw [eq] at d
        omega
      · simp only [ch,if_neg ab,if_pos ac] at eq
        have d := cp.1
        rw [← eq] at d
        omega
      · simpa [ch,ab,ac] using eq
    have dis : Disjoint (f a) (U.image ch) := by
      apply disjoint_left.mpr
      intro z zf zi
      obtain ⟨b,hb,rfl⟩ := mem_image.mp zi
      have d := cDepth (mem_inter.mp zf).1
      have e := (good b hb).2
      omega
    have sub : f a ∪ U.image ch ⊆ DistanceTwo G a := by
      apply union_subset (fun z hz => (mem_inter.mp hz).2)
      intro z zz
      obtain ⟨b,hb,rfl⟩ := mem_image.mp zz
      exact (good b hb).1
    have n := (card_le_card sub).trans (bd a)
    rw [card_union_of_disjoint dis,card_image_of_injOn inj] at n
    have er := card_erase_add_one ha
    dsimp [U] at n
    refine ⟨by omega,U.image ch,rfl,?_,dis,sub⟩
    rw [card_image_of_injOn inj]
    exact er
  have fbound (a : V) (ha : a ∈ T) := (fData a ha).1
  have w := (card_le_card cover).trans (card_biUnion_le_card_mul T f (7-T.card) fbound)
  have ar (t : ℕ) (h : t ≤ 6) : t*(7-t) ≤ 12 := by
    have e : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
    rcases e with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have cC : C.card ≤ 12 := w.trans (ar T.card ts)
  have cov : (Finset.univ : Finset V) ⊆ (EvenFrom G x ∪ A) ∪ C := by
    intro y _
    have d : G.dist x y ≤ 4 := diam y
    by_cases e : Even (G.dist x y)
    · exact mem_union.mpr (.inl (mem_union.mpr (.inl (mem_filter.mpr ⟨mem_univ _,e⟩))))
    by_cases o : G.dist x y = 1
    · exact mem_union.mpr (.inl (mem_union.mpr (.inr (mem_shell.mpr o))))
    exact mem_union.mpr (.inr (mem_shell.mpr (by simp only [Nat.even_iff] at e; omega)))
  have h := card_le_card cov
  rw [card_univ] at h
  have u := card_union_le (EvenFrom G x ∪ A) C
  have v := card_union_le (EvenFrom G x) A
  have xc := cap x
  have c11 : 11≤C.card := by omega
  have a6 : A.card=6 := by rw [eqA,G.card_neighborFinset_eq_degree,dx]
  have tCases : T.card = 3 ∨ T.card = 4 := by
    have e : T.card=0 ∨ T.card=1 ∨ T.card=2 ∨ T.card=3 ∨
        T.card=4 ∨ T.card=5 ∨ T.card=6 := by omega
    have w' : 11 ≤ T.card * (7 - T.card) := c11.trans w
    rcases e with e|e|e|e|e|e|e
    · rw [e] at w'; norm_num at w'
    · rw [e] at w'; norm_num at w'
    · rw [e] at w'; norm_num at w'
    · exact .inl e
    · exact .inr e
    · rw [e] at w'; norm_num at w'
    · rw [e] at w'; norm_num at w'

  let B := Shell G x 2
  let D := Shell G x 4
  have layerDiff {i j : ℕ} (hne : i≠j) : Disjoint (Shell G x i) (Shell G x j) := by
    apply disjoint_left.mpr
    intro z zi zj
    exact hne ((mem_shell.mp zi).symm.trans (mem_shell.mp zj))
  have ab : Disjoint A B := layerDiff (by decide : (1:ℕ)≠2)
  have ac : Disjoint A C := layerDiff (by decide : (1:ℕ)≠3)
  have ad : Disjoint A D := layerDiff (by decide : (1:ℕ)≠4)
  have bc : Disjoint B C := layerDiff (by decide : (2:ℕ)≠3)
  have bDisD : Disjoint B D := layerDiff (by decide : (2:ℕ)≠4)
  have cd : Disjoint C D := layerDiff (by decide : (3:ℕ)≠4)
  have rootNot : x∉A∪B∪C∪D := by
    intro m
    have dep : G.dist x x=1 ∨ G.dist x x=2 ∨ G.dist x x=3 ∨ G.dist x x=4 := by
      rcases mem_union.mp m with m|m
      · rcases mem_union.mp m with m|m
        · rcases mem_union.mp m with m|m
          · exact .inl (mem_shell.mp m)
          · exact .inr (.inl (mem_shell.mp m))
        · exact .inr (.inr (.inl (mem_shell.mp m)))
      · exact .inr (.inr (.inr (mem_shell.mp m)))
    rw [dist_self] at dep
    omega
  have all : insert x (A∪B∪C∪D)=(univ:Finset V) := by
    apply eq_univ_iff_forall.mpr
    intro z
    have h := diam z
    have dep : G.dist x z=0 ∨ G.dist x z=1 ∨ G.dist x z=2 ∨ G.dist x z=3 ∨ G.dist x z=4 := by omega
    rcases dep with e|e|e|e|e
    · exact mem_insert.mpr (.inl ((hc.dist_eq_zero_iff.mp e).symm))
    · exact mem_insert.mpr (.inr (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_shell.mpr e)))))
    · exact mem_insert.mpr (.inr (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_shell.mpr e)))))
    · exact mem_insert.mpr (.inr (mem_union_left _ (mem_union_right _ (mem_shell.mpr e))))
    · exact mem_insert.mpr (.inr (mem_union_right _ (mem_shell.mpr e)))
  have len := congrArg Finset.card all
  rw [card_insert_of_not_mem rootNot,
    card_union_of_disjoint (disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨ad,bDisD⟩,cd⟩),
    card_union_of_disjoint (disjoint_union_left.mpr ⟨ac,bc⟩),card_union_of_disjoint ab,a6,card_univ,n] at len
  have shells : B.card+C.card+D.card=17 := by omega
  have cCase : C.card=11 ∨ C.card=12 := by omega
  have exactD (a : V) (ha : a∈T) (full : (f a).card=7-T.card) :
      DistanceTwo G a = f a ∪ (T.erase a).image (fun b => if G.Adj a b then rep b else b) := by
    obtain ⟨_,R,rfl,cs,ds,sub⟩ := fData a ha
    apply (eq_of_subset_of_card_le sub ?_).symm
    have h := bd a
    rw [card_union_of_disjoint ds,full]
    omega
  have joinR (a : V) (ha : a∈T) (full : (f a).card=7-T.card) (b : V) (hb : b∈A) (bt : b∉T) : G.Adj a b := by
    apply Classical.byContradiction
    intro e
    have n : a≠b := fun q=>bt (q ▸ ha)
    have ax := (dist_eq_one_iff_adj.mp (aDepth (TA ha))).symm
    have xb := dist_eq_one_iff_adj.mp (aDepth hb)
    have bb : b ∈ DistanceTwo G a := mem_distanceTwo.mpr (dist_two hc n e ax xb)
    rw [exactD a ha full] at bb
    rcases mem_union.mp bb with c|m
    · have q := cDepth (mem_inter.mp c).1
      have r := aDepth hb
      omega
    obtain ⟨i,im,ie⟩ := mem_image.mp m
    have it := (mem_erase.mp im).2
    by_cases ai : G.Adj a i
    · simp only [if_pos ai] at ie
      have z := (prop it).1
      rw [ie] at z
      have w := aDepth hb
      omega
    · simp only [if_neg ai] at ie
      exact bt (ie ▸ it)

  exact ⟨⟨T,rep,TA,tCases,a6,cCase,p2lower,shell_two_four_le_of_even (cap x),
    shells,diam,fbound,cover,fun a ha => (prop ha).1,fun a ha => (prop ha).2.1,
    fun a ha => (prop ha).2.2.1,fun a ha => (prop ha).2.2.2,exactD,joinR⟩⟩
theorem layer_cover_at_order_twenty_four
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (conn : ∀ S : Finset V,S.card<3→(G.induce ((↑S:Set V)ᶜ)).Connected)
    (high : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (x : V) (dx : G.degree x=6) (n : Fintype.card V=24) :
    Nonempty (Layer24Cover G x) :=
  layer_cover_at_order_twenty_four_with_radius_frame hc cap x dx n
    (eccentricity_le_four_of_order_ge_twenty_four_at_degree_six hc cap conn high dx.le n.ge)
    (four_le_second_shell_of_order_ge_twenty_four_at_degree_six hc cap conn high dx.le n.ge)
#print axioms layer_cover_at_order_twenty_four
end Graffiti189LongestPath
