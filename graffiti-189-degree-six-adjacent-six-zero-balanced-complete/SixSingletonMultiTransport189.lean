import SixSingletonMultiZeroGeom189
import SixSingletonPortScore189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_off from AdjacentCutFiveActual189
open private Cmp DeletionConnected aPorts bPorts from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark Common strictA strictB from SixSingletonGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
open private nearBal from SixSingletonFiveGeometry189
open private class_strict_dis from SixSingletonShape189
open private shore_sum_with_cover from AdjacentCutFiveMixedFourteenSixteen189
open private inside_label from SixSingletonLabel189
open private positive_even_cap from TwoCutOrderCenters189
open private in_positive_even_of_dist_two from TwoCutDistanceCaps189
open FiveAdjacent (depth traceable_label)
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

private theorem common_size {D : Cmp G a b} {s : V} (F : ZeroBalanceData G D s) :
    (EA D).card+(EB D).card+(Common D).card=(Vis D).card := by
  have eab : Disjoint (EA D) (EB D) := disjoint_left.mpr (fun _ h j=>(mem_sdiff.mp h).2 (mem_sdiff.mp j).1)
  have ck : Disjoint (EA D∪EB D) (Common D) := by
    apply disjoint_left.mpr
    intro z hz zk
    rcases mem_union.mp hz with u|v
    · exact (mem_sdiff.mp u).2 (mem_inter.mp zk).2
    exact (mem_sdiff.mp v).2 (mem_inter.mp zk).1
  rw [←F.visiblePart,card_union_of_disjoint ck,card_union_of_disjoint eab]

private theorem both_strict_nonempty (even : ∀ z,(EvenFrom G z).card≤7)
    {D : Cmp G a b} {s : V} (F : ZeroBalanceData G D s)
    (near : ∀ z∈Dark D,depth G a b z=2) :
    (strictA D).Nonempty ∧ (strictB D).Nonempty := by
  classical
  have l {z : V} (m : z∈strictA D) : G.dist a z=2 := by
    have h := near z (mem_filter.mp m).1
    change min (G.dist a z) (G.dist b z)=2 at h
    have q := (mem_filter.mp m).2
    rw [min_eq_left (le_of_lt q)] at h
    exact h
  have r {z : V} (m : z∈strictB D) : G.dist b z=2 := by
    have h := near z (mem_filter.mp m).1
    change min (G.dist a z) (G.dist b z)=2 at h
    have q := (mem_filter.mp m).2
    rw [min_eq_right (le_of_lt q)] at h
    exact h
  constructor
  · by_contra no
    have B : Dark D ⊆ PositiveEven G b := by
      intro z m
      have h := mem_union.mp (F.darkPart.symm ▸ m)
      exact in_positive_even_of_dist_two (r (h.resolve_left (fun zl=>no ⟨z,zl⟩)))
    have h := card_le_card B
    rw [F.dark7] at h
    have j := positive_even_cap (d:=6) (even b)
    omega
  · by_contra no
    have A : Dark D ⊆ PositiveEven G a := by
      intro z m
      have h := mem_union.mp (F.darkPart.symm ▸ m)
      exact in_positive_even_of_dist_two (l (h.resolve_right (fun zr=>no ⟨z,zr⟩)))
    have h := card_le_card A
    rw [F.dark7] at h
    have j := positive_even_cap (d:=6) (even a)
    omega

private theorem transfer_dark {D : Cmp G a b} {s : V} (F : ZeroBalanceData G D s)
    (e : Fin 16≃V)
    (dark : ∀ i,i∈PortCertificates.D ↔ e i∈Dark D) :
    let L := univ.filter (fun i=>e i∈strictA D)
    let R := univ.filter (fun i=>e i∈strictB D)
    L⊆PortCertificates.D ∧ R⊆PortCertificates.D ∧ Disjoint L R ∧
      ∀ t∈PortCertificates.D,4≤(inside (G.comap e) PortCertificates.D t).card := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · intro i im
    exact (dark i).mpr (mem_filter.mp (mem_filter.mp im).2).1
  · intro i im
    exact (dark i).mpr (mem_filter.mp (mem_filter.mp im).2).1
  · exact disjoint_left.mpr (fun _ im jm=>disjoint_left.mp (class_strict_dis D) (mem_filter.mp im).2 (mem_filter.mp jm).2)
  · intro i im
    rw [inside_label e _ _ dark i]
    exact F.darkFour _ ((dark i).mp im)

private theorem board22_of_data {D : Cmp G a b} {s : V} (F : ZeroBalanceData G D s)
    (n : Fintype.card V=16) (v6 : (Vis D).card=6)
    (ea : (EA D).card=2) (eb : (EB D).card=2)
    (nl : (strictA D).Nonempty) (nr : (strictB D).Nonempty) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have kc : (Common D).card=2 := by
    have h := common_size F
    omega
  obtain ⟨x,x',_,xs⟩ := card_eq_two.mp ea
  obtain ⟨y,y',_,ys⟩ := card_eq_two.mp eb
  obtain ⟨c,c',_,cs⟩ := card_eq_two.mp kc
  let q : Fin 9→V := ![a,b,s,x,x',y,y',c,c']
  have cover (z : V) : (∃ j,q j=z) ∨ z∈Dark D := by
    rcases F.cover z with e|e|e|v|d
    · exact .inl ⟨0,e.symm⟩
    · exact .inl ⟨1,e.symm⟩
    · exact .inl ⟨2,e.symm⟩
    · rw [←F.visiblePart,xs,ys,cs] at v
      simp only [mem_union,mem_insert,mem_singleton] at v
      rcases v with ((e|e)|(e|e))|(e|e)
      · exact .inl ⟨3,e.symm⟩
      · exact .inl ⟨4,e.symm⟩
      · exact .inl ⟨5,e.symm⟩
      · exact .inl ⟨6,e.symm⟩
      · exact .inl ⟨7,e.symm⟩
      · exact .inl ⟨8,e.symm⟩
    · exact .inr d
  obtain ⟨e,tab,ed⟩ := label_nine_and_seven n q _ F.dark7 cover
  have hA (i : Fin 4) (h : PortCertificates.left i=true) : e (PortCertificates.e22 i)∈EA D := by
    fin_cases i
    · change e (PortCertificates.e22 0) ∈ EA D
      rw [show PortCertificates.e22 0=widenPort 3 by rfl,tab,xs]
      simp [q]
    · change e (PortCertificates.e22 1) ∈ EA D
      rw [show PortCertificates.e22 1=widenPort 4 by rfl,tab,xs]
      simp [q]
    · cases (show false=true from h)
    · cases (show false=true from h)
  have hB (i : Fin 4) (h : PortCertificates.left i=false) : e (PortCertificates.e22 i)∈EB D := by
    fin_cases i
    · cases (show true=false from h)
    · cases (show true=false from h)
    · change e (PortCertificates.e22 2) ∈ EB D
      rw [show PortCertificates.e22 2=widenPort 5 by rfl,tab,ys]
      simp [q]
    · change e (PortCertificates.e22 3) ∈ EB D
      rw [show PortCertificates.e22 3=widenPort 6 by rfl,tab,ys]
      simp [q]
  have hC (i : Fin 2) : e (PortCertificates.c22 i)∈Common D := by
    fin_cases i
    · change e (PortCertificates.c22 0) ∈ Common D
      rw [show PortCertificates.c22 0=widenPort 7 by rfl,tab,cs]
      simp [q]
    · change e (PortCertificates.c22 1) ∈ Common D
      rw [show PortCertificates.c22 1=widenPort 8 by rfl,tab,cs]
      simp [q]
  have ta : e PortCertificates.a=a := tab 0
  have tb : e PortCertificates.b=b := tab 1
  have ts : e PortCertificates.s=s := tab 2
  let J := G.comap e
  let L := univ.filter (fun i=>e i∈strictA D)
  let R := univ.filter (fun i=>e i∈strictB D)
  let act (i : Fin 4) : Prop :=
    ∃ z∈(if PortCertificates.left i then strictA D else strictB D),G.Adj (e (PortCertificates.e22 i)) z
  let A : Fin 4→Bool := fun i=>decide (act i)
  obtain ⟨lD,rD,lr,dg⟩ := transfer_dark F e ed
  have actL : A 0=true ∨ A 1=true := by
    obtain ⟨z,zl⟩ := nl
    obtain ⟨d,dl,dz⟩ := F.rootsA z zl
    rw [xs] at dl
    rcases mem_insert.mp dl with p|p
    · subst d
      exact .inl (decide_eq_true ⟨z,zl,(tab 3).symm ▸ dz⟩)
    · have p : d=x' := mem_singleton.mp p
      subst d
      exact .inr (decide_eq_true ⟨z,zl,(tab 4).symm ▸ dz⟩)
  have actR : A 2=true ∨ A 3=true := by
    obtain ⟨z,zr⟩ := nr
    obtain ⟨d,dr,dz⟩ := F.rootsB z zr
    rw [ys] at dr
    rcases mem_insert.mp dr with p|p
    · subst d
      exact .inl (decide_eq_true ⟨z,zr,(tab 5).symm ▸ dz⟩)
    · have p : d=y' := mem_singleton.mp p
      subst d
      exact .inr (decide_eq_true ⟨z,zr,(tab 6).symm ▸ dz⟩)
  apply traceable_label (SimpleGraph.Iso.comap e G)
  apply PortCertificates.traceable_of_double_exclusive_zero_balanced (A:=A) (L:=L) (R:=R)
  refine ⟨?_,?_,?_,?_,?_,?_,lD,rD,lr,dg,?_,?_,actL,actR⟩
  · change G.Adj (e PortCertificates.s) (e PortCertificates.a)
    rw [ts,ta]
    exact F.sa
  · change G.Adj (e PortCertificates.s) (e PortCertificates.b)
    rw [ts,tb]
    exact F.sb
  · intro i
    change G.Adj (e (PortCertificates.terminal i)) (e (PortCertificates.e22 i))
    cases h : PortCertificates.left i
    · simpa [PortCertificates.terminal,h,tb] using (F.eB _ (hB i h)).1
    · simpa [PortCertificates.terminal,h,ta] using (F.eA _ (hA i h)).1
  · intro k
    change G.Adj (e PortCertificates.a) (e (PortCertificates.c22 k))
    rw [ta]
    exact (F.common _ (hC k)).1
  · intro k
    change G.Adj (e PortCertificates.b) (e (PortCertificates.c22 k))
    rw [tb]
    exact (F.common _ (hC k)).2
  · intro i u
    have h : act i := of_decide_eq_true u
    obtain ⟨z,m,j⟩ := h
    obtain ⟨t,rfl⟩ := e.surjective z
    refine ⟨t,?_,j⟩
    cases hi : PortCertificates.left i <;> simp only [hi,Bool.false_eq_true,if_false,if_true] at m ⊢
    · exact mem_filter.mpr ⟨mem_univ _,m⟩
    · exact mem_filter.mpr ⟨mem_univ _,m⟩
  · intro k i j ne
    have cM : e (PortCertificates.c22 k)∈Vis D := F.visiblePart ▸ mem_union.mpr (.inr (hC k))
    have eM (u : Fin 4) : e (PortCertificates.e22 u)∈Vis D := by
      rw [←F.visiblePart]
      apply mem_union.mpr
      left
      cases h : PortCertificates.left u
      · exact mem_union.mpr (.inr (hB u h))
      · exact mem_union.mpr (.inl (hA u h))
    have ce : ∀ (k : Fin 2) (u : Fin 4),PortCertificates.c22 k≠PortCertificates.e22 u := by decide
    have einj : Function.Injective PortCertificates.e22 := by decide
    rcases visible_four_forces_either (G:=G) _ v6 cM (eM i) (eM j)
        (fun h=>ce k i (e.injective h)) (fun h=>ce k j (e.injective h))
        (fun h=>ne (einj (e.injective h))) (F.commonFour _ (hC k)) with p|p
    · exact .inl (decide_eq_true p)
    · exact .inr (decide_eq_true p)
  · intro i u k
    have h : ¬act i := of_decide_eq_false u
    apply decide_eq_true
    change G.Adj (e (PortCertificates.c22 k)) (e (PortCertificates.e22 i))
    apply Adj.symm
    cases hi : PortCertificates.left i
    · exact F.inactiveB _ (hB i hi) (by simpa [act,hi] using h) _ (hC k)
    · exact F.inactiveA _ (hA i hi) (by simpa [act,hi] using h) _ (hC k)

set_option maxHeartbeats 5000000 in
private theorem board12_of_data {D : Cmp G a b} {s : V} (F : ZeroBalanceData G D s)
    (n : Fintype.card V=16) (v6 : (Vis D).card=6)
    (ea : (EA D).card=1) (eb : (EB D).card=2)
    (nl : (strictA D).Nonempty) (nr : (strictB D).Nonempty) :
    ∃ u v,∃ p : G.Walk u v,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  have kc : (Common D).card=3 := by
    have h := common_size F
    omega
  obtain ⟨x,xs⟩ := card_eq_one.mp ea
  obtain ⟨y,y',_,ys⟩ := card_eq_two.mp eb
  obtain ⟨c,c',c'',_,_,_,cs⟩ := card_eq_three.mp kc
  let q : Fin 9→V := ![a,b,s,x,y,y',c,c',c'']
  have cover (z : V) : (∃ j,q j=z) ∨ z∈Dark D := by
    rcases F.cover z with e|e|e|v|d
    · exact .inl ⟨0,e.symm⟩
    · exact .inl ⟨1,e.symm⟩
    · exact .inl ⟨2,e.symm⟩
    · rw [←F.visiblePart,xs,ys,cs] at v
      simp only [mem_union,mem_insert,mem_singleton] at v
      rcases v with (e|(e|e))|(e|e|e)
      · exact .inl ⟨3,e.symm⟩
      · exact .inl ⟨4,e.symm⟩
      · exact .inl ⟨5,e.symm⟩
      · exact .inl ⟨6,e.symm⟩
      · exact .inl ⟨7,e.symm⟩
      · exact .inl ⟨8,e.symm⟩
    · exact .inr d
  obtain ⟨e,tab,ed⟩ := label_nine_and_seven n q _ F.dark7 cover
  have hA : e PortCertificates.x12∈EA D := by
    change e (widenPort 3)∈EA D
    rw [tab,xs]
    simp [q]
  have hB (i : Fin 2) : e (PortCertificates.y12 i)∈EB D := by
    fin_cases i
    · change e (widenPort 4)∈EB D
      rw [tab,ys]
      simp [q]
    · change e (widenPort 5)∈EB D
      rw [tab,ys]
      simp [q]
  have hC (i : Fin 3) : e (PortCertificates.c12 i)∈Common D := by
    fin_cases i
    · change e (widenPort 6)∈Common D
      rw [tab,cs]
      simp [q]
    · change e (widenPort 7)∈Common D
      rw [tab,cs]
      simp [q]
    · change e (widenPort 8)∈Common D
      rw [tab,cs]
      simp [q]
  have ta : e PortCertificates.a=a := tab 0
  have tb : e PortCertificates.b=b := tab 1
  have ts : e PortCertificates.s=s := tab 2
  let J := G.comap e
  let L := univ.filter (fun i=>e i∈strictA D)
  let R := univ.filter (fun i=>e i∈strictB D)
  let act (i : Fin 2) : Prop := ∃ z∈strictB D,G.Adj (e (PortCertificates.y12 i)) z
  let A : Fin 2→Bool := fun i=>decide (act i)
  obtain ⟨lD,rD,lr,dg⟩ := transfer_dark F e ed
  have rootA : ∃ t∈L,J.Adj PortCertificates.x12 t := by
    obtain ⟨z,m⟩ := nl
    obtain ⟨w,wm,edge⟩ := F.rootsA z m
    rw [xs,mem_singleton] at wm
    subst w
    obtain ⟨j,rfl⟩ := e.surjective z
    refine ⟨j,mem_filter.mpr ⟨mem_univ _,m⟩,?_⟩
    change G.Adj (e (widenPort 3)) (e j)
    rw [tab]
    exact edge
  have actR : A 0=true ∨ A 1=true := by
    obtain ⟨z,zr⟩ := nr
    obtain ⟨d,dr,dz⟩ := F.rootsB z zr
    rw [ys] at dr
    rcases mem_insert.mp dr with p|p
    · subst d
      exact .inl (decide_eq_true ⟨z,zr,(tab 4).symm ▸ dz⟩)
    · have p : d=y' := mem_singleton.mp p
      subst d
      exact .inr (decide_eq_true ⟨z,zr,(tab 5).symm ▸ dz⟩)
  apply traceable_label (SimpleGraph.Iso.comap e G)
  apply PortCertificates.traceable_of_one_two_exclusive_zero_balanced (A:=A) (L:=L) (R:=R)
  refine ⟨?_,?_,?_,?_,?_,?_,rootA,?_,lD,rD,lr,dg,?_,actR⟩
  · change G.Adj (e PortCertificates.s) (e PortCertificates.a)
    rw [ts,ta]
    exact F.sa
  · change G.Adj (e PortCertificates.s) (e PortCertificates.b)
    rw [ts,tb]
    exact F.sb
  · change G.Adj (e PortCertificates.a) (e PortCertificates.x12)
    rw [ta]
    exact (F.eA _ hA).1
  · intro i
    change G.Adj (e PortCertificates.b) (e (PortCertificates.y12 i))
    rw [tb]
    exact (F.eB _ (hB i)).1
  · intro k
    change G.Adj (e PortCertificates.a) (e (PortCertificates.c12 k))
    rw [ta]
    exact (F.common _ (hC k)).1
  · intro k
    change G.Adj (e PortCertificates.b) (e (PortCertificates.c12 k))
    rw [tb]
    exact (F.common _ (hC k)).2
  · intro i u
    obtain ⟨z,m,j⟩ : act i := of_decide_eq_true u
    obtain ⟨t,rfl⟩ := e.surjective z
    exact ⟨t,mem_filter.mpr ⟨mem_univ _,m⟩,j⟩
  · intro i
    let P : Finset (Fin 16) := {3,4,5,6,7,8}
    have pVis (j : Fin 16) : j∈P ↔ e j∈Vis D := by
      have p : j∈P ↔ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by
        simp [P]
      rw [p,←F.visiblePart,xs,ys,cs]
      simp only [mem_union,mem_insert,mem_singleton]
      have h (k : Fin 9) : e j=q k ↔ j=widenPort k := by rw [←tab k,e.injective.eq_iff]
      have h3 : e j=x ↔ j=3 := h 3
      have h4 : e j=y ↔ j=4 := h 4
      have h5 : e j=y' ↔ j=5 := h 5
      have h6 : e j=c ↔ j=6 := h 6
      have h7 : e j=c' ↔ j=7 := h 7
      have h8 : e j=c'' ↔ j=8 := h 8
      simp only [h3,h4,h5,h6,h7,h8]
      simp only [or_assoc]
    have b := F.commonFour _ (hC i)
    have deg : 4≤(inside J P (PortCertificates.c12 i)).card := by
      change 4≤(inside (G.comap e) P (PortCertificates.c12 i)).card
      exact (inside_label (G:=G) e P (Vis D) pVis (PortCertificates.c12 i)).symm ▸ b
    have zz (j : Fin 16) : (inside J (∅ : Finset (Fin 16)) j).card=0 := by simp [inside]
    have sc3 := inside_insert_score (G:=J) (P:=({4,5,6,7,8} : Finset (Fin 16))) (x:=3)
      (c:=PortCertificates.c12 i) (by decide)
    have sc4 := inside_insert_score (G:=J) (P:=({5,6,7,8} : Finset (Fin 16))) (x:=4)
      (c:=PortCertificates.c12 i) (by decide)
    have sc5 := inside_insert_score (G:=J) (P:=({6,7,8} : Finset (Fin 16))) (x:=5)
      (c:=PortCertificates.c12 i) (by decide)
    have sc6 := inside_insert_score (G:=J) (P:=({7,8} : Finset (Fin 16))) (x:=6)
      (c:=PortCertificates.c12 i) (by decide)
    have sc7 := inside_insert_score (G:=J) (P:=({8} : Finset (Fin 16))) (x:=7)
      (c:=PortCertificates.c12 i) (by decide)
    have sc8 := inside_insert_score (G:=J) (P:=(∅ : Finset (Fin 16))) (x:=8)
      (c:=PortCertificates.c12 i) (by decide)
    have hex : insert (8 : Fin 16) (∅ : Finset (Fin 16)) = ({(8 : Fin 16)} : Finset (Fin 16)) := by decide
    rw [hex,zz] at sc8
    change 4≤(inside J (insert 3 {4,5,6,7,8}) (PortCertificates.c12 i)).card at deg
    rw [sc3,sc4,sc5,sc6,sc7,sc8] at deg
    change 4≤PortCertificates.marks (decide (J.Adj (PortCertificates.c12 i) 6))+
      PortCertificates.marks (decide (J.Adj (PortCertificates.c12 i) 7))+
      PortCertificates.marks (decide (J.Adj (PortCertificates.c12 i) 8))+
      PortCertificates.marks (decide (J.Adj (PortCertificates.c12 i) 3))+
      PortCertificates.marks (decide (J.Adj (PortCertificates.c12 i) 4))+
      PortCertificates.marks (decide (J.Adj (PortCertificates.c12 i) 5))
    omega

#print axioms board22_of_data
#print axioms board12_of_data
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
