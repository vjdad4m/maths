import SixJointEqualityBase189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset
open private distance_on_geodesic mem_distanceTwo dist_two from SmallSeparator189

variable {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

noncomputable def JointFarGroup (G : SimpleGraph V) (x a : V) :=
  (Shell G x 3 ∩ DistanceTwo G a) ∪ (Shell G x 5 ∩ Shell G a 4)

structure RadiusFiveEquality (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) where
  T : Finset V
  rep : V→V
  near : T ⊆ Shell G x 1
  t3 : T.card=3
  middle : ∀ a∈T,rep a∈Shell G x 2
  adj : ∀ a∈T,G.Adj a (rep a)
  private_rep : ∀ a∈T,∀ b∈T,b≠a → ¬G.Adj b (rep a)
  rep_cover : ∀ b∈Shell G x 2,∃ a∈T,rep a=b
  far_cover : Shell G x 3 ∪ Shell G x 5 ⊆ T.biUnion (JointFarGroup G x)
  far_card : ∀ a∈T,(JointFarGroup G x a).card=4
  far_dis : ∀ a∈T,∀ b∈T,a≠b → Disjoint (JointFarGroup G x a) (JointFarGroup G x b)
  saturated : ∀ a∈T, ∀ z∈(EvenFrom G a).erase a, z∈JointFarGroup G x a ∨
    ∃ b∈T.erase a, z=(if G.Adj a b then rep b else b)

theorem radius_five_equality
    (hc : G.Connected) (cap : ∀ v, (EvenFrom G v).card ≤ 7)
    (x : V) (dx : G.degree x ≤ 6)
    (b3 : (Shell G x 2).card=3)
    (eq : (Shell G x 3).card+(Shell G x 5).card=12) :
    Nonempty (RadiusFiveEquality G x) := by
  classical
  let A := Shell G x 1
  let C := Shell G x 3
  let E := Shell G x 5
  let f (a : V) := C ∩ DistanceTwo G a
  let h := JointFarGroup G x
  have cA : A.card ≤ 6 := by
    have eq : A = G.neighborFinset x := by
      ext a
      rw [mem_shell,G.mem_neighborFinset,dist_eq_one_iff_adj]
    rw [eq,G.card_neighborFinset_eq_degree]
    exact dx
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
  have coverE : E ⊆ T.biUnion h := by
    intro e em
    have e5 := mem_shell.mp em
    obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist x e
    have len : p.length=5 := hp.trans e5
    let c := p.getVert 3
    let d := p.getVert 4
    have c3 : G.dist x c=3 := distance_on_geodesic hc p hp 3 (by omega)
    have cd : G.Adj c d := p.adj_getVert_succ (i:=3) (by omega)
    have de : G.Adj d e := by
      have adj4 := p.adj_getVert_succ (i:=4) (by omega)
      have len5 : p.getVert 5 = e := by rw [←len,getVert_length]
      simpa only [len5] using adj4
    obtain ⟨a,am,ac⟩ := mem_biUnion.mp (cover (mem_shell.mpr c3))
    have a1 := aDepth (TA am)
    have ac2 := mem_distanceTwo.mp (mem_inter.mp ac).2
    have ae4 : G.dist a e=4 := by
      have one := dist_eq_one_iff_adj.mpr cd
      have two := dist_eq_one_iff_adj.mpr de
      have ce := hc.dist_triangle (u:=c) (v:=d) (w:=e)
      have ae := hc.dist_triangle (u:=a) (v:=c) (w:=e)
      have xx := hc.dist_triangle (u:=x) (v:=a) (w:=e)
      omega
    exact mem_biUnion.mpr ⟨a,am,mem_union_right _ (mem_inter.mpr ⟨em,mem_shell.mpr ae4⟩)⟩
  have coverAll : C ∪ E ⊆ T.biUnion h := by
    intro z zm
    rcases mem_union.mp zm with cm|em
    · obtain ⟨a,am,hf⟩ := mem_biUnion.mp (cover cm)
      exact mem_biUnion.mpr ⟨a,am,mem_union_left _ hf⟩
    · exact coverE em
  have ceDis : Disjoint C E := by
    apply disjoint_left.mpr
    intro z cz ez
    have a := mem_shell.mp cz
    have b := mem_shell.mp ez
    omega
  have ts : T.card ≤ 6 := (card_le_card TA).trans cA
  have uniqueMiddle (a : V) (ha : a ∈ T) :
      ∃ b : V, G.dist x b = 2 ∧ G.Adj a b ∧ ∀ z ∈ T, z ≠ a → ¬ G.Adj z b := by
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
    refine ⟨b, db, ab, ?_⟩
    intro z zT ne zb
    have zc : c ∈ f z := mem_inter.mpr ⟨cm,mem_distanceTwo.mpr
      (d2_of_middle (aDepth (TA zT)) dc zb bc)⟩
    exact miss (mem_biUnion.mpr ⟨z,mem_erase.mpr ⟨ne,zT⟩,zc⟩)
  let rep (a : V) := if h : a ∈ T then Classical.choose (uniqueMiddle a h) else x
  have prop {a : V} (ha : a ∈ T) :
      G.dist x (rep a) = 2 ∧ G.Adj a (rep a) ∧ ∀ z ∈ T, z ≠ a → ¬ G.Adj z (rep a) := by
    simpa [rep, dif_pos ha] using Classical.choose_spec (uniqueMiddle a ha)
  let ch (a b : V) := if G.Adj a b then rep b else b
  have repIncl : T.image rep⊆Shell G x 2 := by
    intro z zm
    obtain ⟨a,am,rfl⟩ := mem_image.mp zm
    exact mem_shell.mpr (prop am).1
  have rInj : ∀ a∈T,∀ b∈T,rep a=rep b → a=b := by
    intro a am b bm same
    by_contra ne
    exact (prop bm).2.2 a am ne (same ▸ (prop am).2.1)
  have t3le := card_le_card repIncl
  rw [card_image_of_injOn rInj,b3] at t3le
  have arithmetic (a : V) (ha : a ∈ T) :
      h a ∪ (T.erase a).image (ch a) ⊆ (EvenFrom G a).erase a ∧
      (h a).card + (T.erase a).card ≤ 6 := by
    let U := T.erase a
    have good (b : V) (hb : b ∈ U) : ch a b ∈ DistanceTwo G a ∧ G.dist x (ch a b) ≤ 2 := by
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
        exact ⟨dist_two hc ne (pr.2.2 a ha ba.symm) ab pr.2.1,pr.1.le⟩
      · have ax : G.Adj a x := (dist_eq_one_iff_adj.mp (aDepth (TA ha))).symm
        have xb : G.Adj x b := dist_eq_one_iff_adj.mp bd
        simp only [ch,if_neg ab,mem_distanceTwo]
        exact ⟨dist_two hc ba.symm ab ax xb,bd.le.trans (by decide)⟩
    have inj : ∀ b ∈ U, ∀ c ∈ U, ch a b = ch a c → b = c := by
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
        exact cp.2.2 b bm ne (eq ▸ bp.2.1)
      · simp only [ch,if_pos ab,if_neg ac] at eq
        have d := bp.1
        rw [eq] at d
        omega
      · simp only [ch,if_neg ab,if_pos ac] at eq
        have d := cp.1
        rw [← eq] at d
        omega
      · simpa [ch,ab,ac] using eq
    have dis : Disjoint (h a) (U.image (ch a)) := by
      apply disjoint_left.mpr
      intro z zf zi
      obtain ⟨b,hb,rfl⟩ := mem_image.mp zi
      have e := (good b hb).2
      rcases mem_union.mp zf with hf|hg
      · have d := cDepth (mem_inter.mp hf).1
        omega
      · have d := mem_shell.mp (mem_inter.mp hg).1
        omega
    have here (z : V) (p : G.dist a z=2 ∨ G.dist a z=4) :
        z∈(EvenFrom G a).erase a := by
      have ne : z≠a := fun k=>by rw [k,dist_self] at p; omega
      have even : Even (G.dist a z) := by rcases p with e|e <;> rw [e] <;> decide
      exact mem_erase.mpr ⟨ne,mem_filter.mpr ⟨mem_univ _,even⟩⟩
    have sub : h a ∪ U.image (ch a) ⊆ (EvenFrom G a).erase a := by
      apply union_subset
      · intro z zh
        rcases mem_union.mp zh with hf|hg
        · exact here z (Or.inl (mem_distanceTwo.mp (mem_inter.mp hf).2))
        · exact here z (Or.inr (mem_shell.mp (mem_inter.mp hg).2))
      · intro z zz
        obtain ⟨b,hb,rfl⟩ := mem_image.mp zz
        exact here _ (Or.inl (mem_distanceTwo.mp (good b hb).1))
    have n := card_le_card sub
    rw [card_union_of_disjoint dis,card_image_of_injOn inj] at n
    have sea : a∈EvenFrom G a := by simp [EvenFrom,dist_self]
    have num := card_erase_add_one sea
    have bound := cap a
    have er := card_erase_add_one ha
    dsimp [U] at n
    exact ⟨sub,by omega⟩
  have fbound (a : V) (ha : a∈T) : (h a).card≤7-T.card := by
    have e := (arithmetic a ha).2
    have er := card_erase_add_one ha
    omega
  have w := (card_le_card coverAll).trans (card_biUnion_le_card_mul T h (7-T.card) fbound)
  rw [card_union_of_disjoint ceDis] at w
  change C.card+E.card=12 at eq
  rw [eq] at w
  have teq : T.card=3 := by
    have v : T.card=0 ∨ T.card=1 ∨ T.card=2 ∨ T.card=3 := by omega
    rcases v with f|f|f|f <;> rw [f] at w <;> omega
  have p : (C∪E).card=T.card*4 := by rw [card_union_of_disjoint ceDis,eq,teq]
  have ⟨hc4,hd⟩ := exact_cover_members T h (C∪E) 4 coverAll p
    (fun a am=>by have e := fbound a am; omega)
  have repEq : T.image rep=Shell G x 2 := eq_of_subset_of_card_le repIncl
    (by rw [card_image_of_injOn rInj,b3,teq])
  have sat (a : V) (am : a∈T) : h a ∪ (T.erase a).image (ch a) = (EvenFrom G a).erase a := by
    have inj : ∀ b∈T.erase a,∀ c∈T.erase a,ch a b=ch a c → b=c := by
      intro b bm c cm eq
      have bt := (mem_erase.mp bm).2
      have ct := (mem_erase.mp cm).2
      have b1 := aDepth (TA bt)
      have c1 := aDepth (TA ct)
      have bp := (prop bt).1
      have cp := (prop ct).1
      by_cases ab : G.Adj a b <;> by_cases ac : G.Adj a c
      · exact rInj b bt c ct (by simpa [ch,ab,ac] using eq)
      · simp only [ch,ab,ac,if_true,if_false] at eq
        rw [eq] at bp
        omega
      · simp only [ch,ab,ac,if_true,if_false] at eq
        rw [←eq] at cp
        omega
      · simpa [ch,ab,ac] using eq
    have dis : Disjoint (h a) ((T.erase a).image (ch a)) := by
      apply disjoint_left.mpr
      intro z zm zi
      obtain ⟨b,bm,rfl⟩ := mem_image.mp zi
      have bt := (mem_erase.mp bm).2
      have np := aDepth (TA bt)
      have mp := (prop bt).1
      have l : G.dist x (ch a b)≤2 := by by_cases e : G.Adj a b <;> simp [ch,e,np,mp]
      rcases mem_union.mp zm with f|g
      · have k := mem_shell.mp (mem_inter.mp f).1
        omega
      · have k := mem_shell.mp (mem_inter.mp g).1
        omega
    apply eq_of_subset_of_card_le (arithmetic a am).1
    rw [card_union_of_disjoint dis,hc4 a am,card_image_of_injOn inj,card_erase_of_mem am,teq]
    have ea : a∈EvenFrom G a := by simp [EvenFrom,dist_self]
    have e := card_erase_add_one ea
    have q := cap a
    omega
  refine ⟨⟨T,rep,TA,teq,fun a am=>mem_shell.mpr (prop am).1,fun a am=>(prop am).2.1,
    fun a am b bm ne=>(prop am).2.2 b bm ne,?_,coverAll,hc4,hd,?_⟩⟩
  · intro b bm
    have m : b∈T.image rep := repEq.symm ▸ bm
    exact mem_image.mp m
  · intro a am z zm
    have s : z∈h a ∪ (T.erase a).image (ch a) := (sat a am).symm ▸ zm
    rcases mem_union.mp s with zf|zn
    · exact Or.inl zf
    · obtain ⟨b,bm,e⟩ := mem_image.mp zn
      exact Or.inr ⟨b,bm,e.symm⟩

#print axioms radius_five_equality
end Graffiti189LongestPath
