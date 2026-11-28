import SixSingletonCommon189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private two_local_counts from SixCutFar189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

private theorem cannot_miss_two_on_seven (D : Finset V) (seven : D.card=7) {z p q : V}
    (zd : z∈D) (pd : p∈D) (qd : q∈D) (zp : z≠p) (zq : z≠q) (pq : p≠q)
    (hi : 5≤(inside G D z).card) : G.Adj z p ∨ G.Adj z q := by
  classical
  by_cases xp : G.Adj z p
  · exact .inl xp
  by_cases xq : G.Adj z q
  · exact .inr xq
  exfalso
  have sub : inside G D z⊆D.erase z :=
    fun u h=>mem_erase.mpr ⟨(mem_filter.mp h).2.ne.symm,(mem_filter.mp h).1⟩
  have pair : ({p,q}:Finset V)⊆D.erase z :=
    insert_subset (mem_erase.mpr ⟨zp.symm,pd⟩) (singleton_subset_iff.mpr (mem_erase.mpr ⟨zq.symm,qd⟩))
  have apart : Disjoint (inside G D z) ({p,q}:Finset V) := by
    apply disjoint_left.mpr
    intro u um up
    rcases (by simpa using up : u=p ∨ u=q) with rfl|rfl
    · exact xp (mem_filter.mp um).2
    exact xq (mem_filter.mp um).2
  have h := two_local_counts _ _ apart _ sub pair
  rw [card_erase_of_mem zd,seven,card_insert_of_not_mem (by simp [pq]),card_singleton] at h
  omega

private abbrev GoodComplement (S : Finset V) (i z : V) : Prop :=
  ∀ p∈(S.erase i).erase z,∀ q∈(S.erase i).erase z,p≠q→G.Adj p q

private theorem good_complement_two_choices (S : Finset V) (four : S.card=4)
    (miss : ∀ z∈S,∀ p∈S,∀ q∈S,z≠p → z≠q → p≠q → G.Adj z p ∨ G.Adj z q)
    {i j k : V} (im : i∈S) (jm : j∈S) (km : k∈S)
    (ij : i≠j) (ik : i≠k) (jk : j≠k) :
    GoodComplement (G:=G) S i j ∨ GoodComplement (G:=G) S i k := by
  classical
  let T := ((S.erase i).erase j).erase k
  have t1 : T.card=1 := by
    change (((S.erase i).erase j).erase k).card=1
    rw [card_erase_of_mem (mem_erase.mpr ⟨jk.symm,mem_erase.mpr ⟨ik.symm,km⟩⟩),
      card_erase_of_mem (mem_erase.mpr ⟨ij.symm,jm⟩),card_erase_of_mem im,four]
  obtain ⟨u,ut⟩ := card_eq_one.mp t1
  have hu : u∈T := by rw [ut]; simp
  have ⟨uk,hu⟩ := mem_erase.mp hu
  have ⟨uj,hu⟩ := mem_erase.mp hu
  have ⟨ui,hu⟩ := mem_erase.mp hu
  have ju := miss u hu j jm k km uj uk jk
  have ek : (S.erase i).erase k={u,j} := by
    have m : ({u,j}:Finset V)⊆(S.erase i).erase k :=
      insert_subset (mem_erase.mpr ⟨uk,mem_erase.mpr ⟨ui,hu⟩⟩)
        (singleton_subset_iff.mpr (mem_erase.mpr ⟨jk,mem_erase.mpr ⟨ij.symm,jm⟩⟩))
    have c : ((S.erase i).erase k).card=2 := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨ik.symm,km⟩),card_erase_of_mem im,four]
    exact (eq_of_subset_of_card_le m (by rw [c,card_insert_of_not_mem (by simp [uj]),card_singleton])).symm
  have ej : (S.erase i).erase j={u,k} := by
    have m : ({u,k}:Finset V)⊆(S.erase i).erase j :=
      insert_subset (mem_erase.mpr ⟨uj,mem_erase.mpr ⟨ui,hu⟩⟩)
        (singleton_subset_iff.mpr (mem_erase.mpr ⟨jk.symm,mem_erase.mpr ⟨ik.symm,km⟩⟩))
    have c : ((S.erase i).erase j).card=2 := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨ij.symm,jm⟩),card_erase_of_mem im,four]
    exact (eq_of_subset_of_card_le m (by rw [c,card_insert_of_not_mem (by simp [uk]),card_singleton])).symm
  have done {x y : V} (h : G.Adj u y) (e : (S.erase i).erase x={u,y}) :
      GoodComplement (G:=G) S i x := by
    intro p pm q qm pq
    rw [e] at pm qm
    have fp : p=u ∨ p=y := by simpa using pm
    have fq : q=u ∨ q=y := by simpa using qm
    rcases fp with g|g <;> rcases fq with f|f
    · exact (pq (g.trans f.symm)).elim
    · rw [g,f]
      exact h
    · rw [g,f]
      exact h.symm
    exact (pq (g.trans f.symm)).elim
  exact ju.elim (fun h=>.inr (done h ek)) (fun h=>.inl (done h ej))

private theorem choose_good_complement (S A B : Finset V) (four : S.card=4)
    (cover : A∪B=S) (aPos : A.Nonempty) (bPos : B.Nonempty)
    (miss : ∀ z∈S,∀ p∈S,∀ q∈S,z≠p → z≠q → p≠q → G.Adj z p ∨ G.Adj z q) :
    ∃ i∈A,∃ z∈B,i≠z ∧ GoodComplement (G:=G) S i z := by
  classical
  have aS : A⊆S := fun _ h=>cover ▸ (mem_union_left _ h : _∈A∪B)
  have bS : B⊆S := fun _ h=>cover ▸ (mem_union_right _ h : _∈A∪B)
  have choose {i : V} (im : i∈S) (T : Finset V) (ts : T⊆S)
      (t2 : 2≤(T.erase i).card) : ∃ z∈T,i≠z ∧ GoodComplement (G:=G) S i z := by
    have more : 1<(T.erase i).card := by omega
    obtain ⟨j,jt,k,kt,jk⟩ := one_lt_card.mp more
    have ⟨ji,jt⟩ := mem_erase.mp jt
    have ⟨ki,kt⟩ := mem_erase.mp kt
    rcases good_complement_two_choices S four miss im (ts jt) (ts kt) ji.symm ki.symm jk with h|h
    · exact ⟨j,jt,ji.symm,h⟩
    exact ⟨k,kt,ki.symm,h⟩
  by_cases three : 3≤B.card
  · obtain ⟨i,ia⟩ := aPos
    have m := card_erase_le (s:=B) (a:=i)
    have e : 2≤(B.erase i).card := by
      by_cases h : i∈B
      · have q := card_erase_add_one h
        omega
      rw [erase_eq_of_not_mem h]
      omega
    obtain ⟨z,zb,iz,g⟩ := choose (aS ia) B bS e
    exact ⟨i,ia,z,zb,iz,g⟩
  by_cases two : B.card=2
  · have gap : ¬S⊆B := by
      intro h
      have q := card_le_card h
      omega
    obtain ⟨i,is,ib⟩ := not_subset.mp gap
    have iu : i∈A∪B := cover.symm ▸ is
    have ia := (mem_union.mp iu).resolve_right ib
    obtain ⟨z,zb,iz,g⟩ := choose is B bS (by simp [erase_eq_of_not_mem ib,two])
    exact ⟨i,ia,z,zb,iz,g⟩
  obtain ⟨z,zb⟩ := bPos
  have c := card_union_le A B
  rw [cover,four] at c
  have m : 2≤(A.erase z).card := by
    by_cases q : z∈A
    · have e := card_erase_add_one q
      omega
    rw [erase_eq_of_not_mem q]
    omega
  obtain ⟨i,ia,zi,g⟩ := choose (bS zb) A aS m
  refine ⟨i,ia,z,zb,zi.symm,?_⟩
  have eq : (S.erase i).erase z=(S.erase z).erase i := by
    ext t
    simp only [mem_erase]
    tauto
  intro t tm v vm tv
  rw [eq] at tm vm
  exact g t tm v vm tv

/-- With four strict dark vertices and three balanced dark vertices, a marked
balance with between one and three strict neighbors can be the last vertex
of a dark spanning path whose first vertex is another balanced vertex. -/
theorem dark_three_balanced_route_to_mark (D S B : Finset V)
    (seven : D.card=7) (four : S.card=4) (three : B.card=3)
    (cover : S∪B=D) (dis : Disjoint S B)
    (hi : ∀ z∈S,5≤(inside G D z).card)
    {w : V} (wb : w∈B) (some : ∃ z∈S,G.Adj w z)
    (atmost : (S.filter (G.Adj w)).card≤3) :
    ∃ p∈B,p≠w ∧ RouteOn G D p w := by
  classical
  have sD : S⊆D := fun _ h=>cover ▸ (mem_union_left _ h : _∈S∪B)
  have bD : B⊆D := fun _ h=>cover ▸ (mem_union_right _ h : _∈S∪B)
  have miss {z : V} (zs : z∈S) {p q : V} (pd : p∈D) (qd : q∈D) (zp : z≠p) (zq : z≠q) (pq : p≠q) :=
    cannot_miss_two_on_seven D seven (sD zs) pd qd zp zq pq (hi z zs)
  have bsz : (B.erase w).card=2 := by rw [card_erase_of_mem wb,three]
  obtain ⟨p,v,pv,pack⟩ := card_eq_two.mp bsz
  have wp' : p∈B.erase w := by rw [pack]; simp
  have wv' : v∈B.erase w := by rw [pack]; simp
  have ⟨pw,pb⟩ := mem_erase.mp wp'
  have ⟨vw,vb⟩ := mem_erase.mp wv'
  have wc : B=insert w {p,v} := by rw [←pack,insert_erase wb]
  let Sx (x : V) := S.filter (G.Adj x)
  have hit {p q : V} (pb : p∈B) (qb : q∈B) (pq : p≠q) : Sx p∪Sx q=S := by
    apply Subset.antisymm (union_subset (filter_subset _ _) (filter_subset _ _))
    intro z zs
    have zp : z≠p := fun e=>disjoint_left.mp dis zs (e.symm ▸ pb)
    have zq : z≠q := fun e=>disjoint_left.mp dis zs (e.symm ▸ qb)
    rcases miss zs (bD pb) (bD qb) zp zq pq with u|u
    · exact mem_union_left _ (mem_filter.mpr ⟨zs,u.symm⟩)
    exact mem_union_right _ (mem_filter.mpr ⟨zs,u.symm⟩)
  have exists3 : 3≤(Sx p).card ∨ 3≤(Sx v).card := by
    have ws : Sx w⊆S := filter_subset _ _
    obtain ⟨z,zs,zwn⟩ := not_subset.mp (show ¬S⊆Sx w from fun t=>by
      have k := card_le_card t
      change (Sx w).card≤3 at atmost
      omega)
    have zm1 : z∈Sx p := (mem_union.mp (show z∈Sx p∪Sx w from (hit pb wb pw).symm ▸ zs)).resolve_right zwn
    have zm2 : z∈Sx v := (mem_union.mp (show z∈Sx v∪Sx w from (hit vb wb vw).symm ▸ zs)).resolve_right zwn
    have q := card_union_add_card_inter (Sx p) (Sx v)
    rw [hit pb vb pv,four] at q
    have c := card_pos.mpr ⟨z,mem_inter.mpr ⟨zm1,zm2⟩⟩
    omega
  have go {p v : V} (pb : p∈B) (vb : v∈B) (pw : p≠w) (vw : v≠w) (pv : p≠v)
      (desc : B=insert w {p,v}) (h3 : 3≤(Sx v).card) :
      ∃ p∈B,p≠w ∧ RouteOn G D p w := by
    have U := hit pb wb pw
    have np : (Sx p).Nonempty := by
      have q := card_union_le (Sx p) (Sx w)
      rw [U,four] at q
      change (Sx w).card≤3 at atmost
      exact card_pos.mp (by omega)
    have nw : (Sx w).Nonempty := by
      obtain ⟨z,zs,wz⟩ := some
      exact ⟨z,mem_filter.mpr ⟨zs,wz⟩⟩
    obtain ⟨i,ip,z,zw,iz,g⟩ := choose_good_complement S (Sx p) (Sx w) four U np nw
      (fun z zs p ps q qs=>miss zs (sD ps) (sD qs))
    have ⟨is,pi⟩ := mem_filter.mp ip
    have ⟨zs,wz⟩ := mem_filter.mp zw
    have rest : ((S.erase i).erase z).card=2 := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨iz.symm,zs⟩),card_erase_of_mem is,four]
    obtain ⟨u,t,ut,restEq⟩ := card_eq_two.mp rest
    have ur : u∈(S.erase i).erase z := by rw [restEq]; simp
    have tr : t∈(S.erase i).erase z := by rw [restEq]; simp
    have ⟨uz,u'⟩ := mem_erase.mp ur
    have ⟨ui,us⟩ := mem_erase.mp u'
    have ⟨tz,t'⟩ := mem_erase.mp tr
    have ⟨ti,ts⟩ := mem_erase.mp t'
    have eUT := g u ur t tr ut
    have seq : (G.Adj i u ∧ G.Adj t z) ∨ (G.Adj i t ∧ G.Adj u z) := by
      by_cases iu : G.Adj i u
      · by_cases tz' : G.Adj t z
        · exact .inl ⟨iu,tz'⟩
        have it := (miss ts (sD zs) (sD is) tz ti iz.symm).resolve_left tz'
        have zu := (miss zs (sD ts) (sD us) tz.symm uz.symm ut.symm).resolve_left (fun h=>tz' h.symm)
        exact .inr ⟨it.symm,zu.symm⟩
      have it := (miss is (sD us) (sD ts) ui.symm ti.symm ut).resolve_left iu
      have uz' := (miss us (sD is) (sD zs) ui uz iz).resolve_left (fun h=>iu h.symm)
      exact .inr ⟨it,uz'⟩
    have forms : S={i,u,t,z} := by
      have sub : S⊆({i,u,t,z}:Finset V) := by
        intro k km
        by_cases ki : k=i
        · simp [ki]
        by_cases kz : k=z
        · simp [kz]
        have g : k∈(S.erase i).erase z := mem_erase.mpr ⟨kz,mem_erase.mpr ⟨ki,km⟩⟩
        rw [restEq] at g
        rcases (by simpa using g : k=u ∨ k=t) with rfl|rfl <;> simp
      have sub' : ({i,u,t,z}:Finset V)⊆S :=
        insert_subset is (insert_subset us (insert_subset ts (singleton_subset_iff.mpr zs)))
      exact Subset.antisymm sub sub'
    have vOff : ∀ i∈S,i≠v := fun i im e=>disjoint_left.mp dis im (e.symm ▸ vb)
    have make {f l : V} (fs : f∈S) (ls : l∈S) (fl : f≠l)
        (fi : f≠i) (fz : f≠z) (li : l≠i) (lz : l≠z)
        (Sform : S={i,f,l,z}) (ef : G.Adj i f) (el : G.Adj f l) (ez : G.Adj l z) :
        RouteOn G (insert v S) i z := by
      have pair : (G.Adj v i ∧ G.Adj v f) ∨ (G.Adj v l ∧ G.Adj v z) := by
        by_contra h
        have bad : ∃ m∈({i,f}:Finset V),¬G.Adj v m := by
          by_cases hI : G.Adj v i
          · exact ⟨f,by simp,fun hv=>h (.inl ⟨hI,hv⟩)⟩
          exact ⟨i,by simp,hI⟩
        have bad' : ∃ m∈({l,z}:Finset V),¬G.Adj v m := by
          by_cases hL : G.Adj v l
          · exact ⟨z,by simp,fun hv=>h (.inr ⟨hL,hv⟩)⟩
          exact ⟨l,by simp,hL⟩
        obtain ⟨m,mm,mn⟩ := bad
        obtain ⟨n,nn,nb⟩ := bad'
        have e : m≠n := by
          rcases (by simpa using mm : m=i ∨ m=f) with rfl|rfl <;>
            rcases (by simpa using nn : n=l ∨ n=z) with rfl|rfl
          · exact li.symm
          · exact iz
          · exact fl
          exact fz
        have ss : ({m,n}:Finset V)⊆S := by
          apply insert_subset
          · exact (by simpa using mm : m=i ∨ m=f).elim (fun e=>e.symm ▸ is) (fun e=>e.symm ▸ fs)
          apply singleton_subset_iff.mpr
          exact (by simpa using nn : n=l ∨ n=z).elim (fun e=>e.symm ▸ ls) (fun e=>e.symm ▸ zs)
        have dd : Disjoint ({m,n}:Finset V) (Sx v) := by
          apply disjoint_left.mpr
          intro u up uv
          rcases (by simpa using up : u=m ∨ u=n) with rfl|rfl
          · exact mn (mem_filter.mp uv).2
          exact nb (mem_filter.mp uv).2
        have c := two_local_counts _ _ dd _ ss (filter_subset _ _)
        rw [card_insert_of_not_mem (by simp [e]),card_singleton,four] at c
        omega
      rw [Sform]
      rcases pair with ⟨vi,vf⟩|⟨vl,vz⟩
      · have tail := RouteOn.three el ez fz
        have t := tail.prefix vf (by simp [(vOff f fs).symm,(vOff l ls).symm,(vOff z zs).symm])
        have r := t.prefix vi.symm (by simp [vOff i is,fi.symm,li.symm,iz])
        have eq : insert i (insert v ({f,l,z}:Finset V)) = ({v,i,f,l,z}:Finset V) := by
          ext k
          simp [or_comm,or_assoc,or_left_comm]
        exact eq ▸ r
      have arm := RouteOn.three ef el li.symm
      have t := arm.suffix vl.symm (by simp [(vOff i is).symm,(vOff f fs).symm,(vOff l ls).symm])
      have r := t.suffix vz (by simp [vOff z zs,iz.symm,fz.symm,lz.symm])
      have eq : insert z (insert v ({i,f,l}:Finset V)) = ({v,i,f,l,z}:Finset V) := by
        ext k
        simp [or_comm,or_assoc,or_left_comm]
      exact eq ▸ r
    have arm : RouteOn G (insert v S) i z := by
      rcases seq with ⟨iu,tz'⟩|⟨it,uz'⟩
      · exact make us ts ut ui uz ti tz forms iu eUT tz'
      exact make ts us ut.symm ti tz ui uz (by simpa only [insert_comm] using forms) it eUT.symm uz'
    have pOff : p∉insert v S := by
      simp only [mem_insert,not_or]
      exact ⟨pv,fun h=>disjoint_left.mp dis h pb⟩
    have wOff : w∉insert p (insert v S) := by
      simp only [mem_insert,not_or]
      exact ⟨pw.symm,vw.symm,fun h=>disjoint_left.mp dis h wb⟩
    have run := (arm.prefix pi pOff).suffix wz.symm wOff
    have de : insert w (insert p (insert v S))=D := by
      rw [←cover,desc]
      ext k
      simp [or_assoc,or_comm,or_left_comm]
    rw [de] at run
    exact ⟨p,pb,pw,run⟩
  rcases exists3 with hp|hv
  · have e : B=insert w {v,p} := by
      rw [wc]
      ext z
      simp [or_comm,or_assoc,or_left_comm]
    exact go vb pb vw pw pv.symm e hp
  exact go pb vb pw vw pv wc hv

#print axioms dark_three_balanced_route_to_mark
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
