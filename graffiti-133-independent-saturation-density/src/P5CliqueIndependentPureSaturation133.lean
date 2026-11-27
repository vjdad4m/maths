import P5CliqueIndependentPureAnchor133
import P5CliqueIncomingLong133
import P5CliqueTwoIncomingNearest133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133 Graffiti133Camby
open scoped Classical BigOperators
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem nearest_stem_reindex (D : Finset V) (p : Fin 4→V) (e : Fin 4 ≃ Fin 4)
    (i j : Fin 4) (d : Nat) (stem : IsNearestPortStem (G:=G) D p (e i) (e j) d) :
    IsNearestPortStem (G:=G) D (p∘e) i j d := by
  obtain ⟨w,wp,wd,l,r,core,front⟩ := stem
  refine ⟨w,wp,wd,l,r,fun t tl tr c=>core t tl tr (e c),?_⟩
  intro k kl c cn a
  exact front k kl (e c) (fun he=>cn (e.injective he)) a

/-- With two outside-occupied port pairs at each home and no triple inner
anchor, no label can support two pure score-four clients. -/
theorem four_port_pure_highs_at_most_four_when_pairs_occupied
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7)
    (good : ∀ i : Fin 4,∀ v∈D,G.Adj (p i) v → ∀ j k : Fin 4,j≠i→k≠i→j≠k→
      ¬(G.Adj (p j) v ∧ G.Adj (p k) v))
    (partners : ∀ h : Fin 4,∃ a b : Fin 4,a≠h ∧ b≠h ∧ a≠b ∧
      (∃ x∉D,G.Adj (p h) x ∧ G.Adj (p a) x) ∧
      (∃ y∉D,G.Adj (p h) y ∧ G.Adj (p b) y)) :
    let Q := (Finset.univ : Finset V)\D
    (Q.filter (fun q=>3<localIndependence G q ∧ (D.filter (G.Adj q)).card=1)).card≤4 := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let B (h : Fin 4) := Q.filter (fun q=>(∀ w∈D,G.Adj q w↔w=p h) ∧ 3<localIndependence G q)
  let U := Q.filter (fun q=>3<localIndependence G q ∧ (D.filter (G.Adj q)).card=1)
  have qo (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have cover : U⊆Finset.univ.biUnion B := by
    intro q qm
    obtain ⟨qQ,high,d1⟩ := Finset.mem_filter.mp qm
    obtain ⟨t,qt⟩ := attach q (qo _ qQ)
    have one := Finset.card_le_one.mp d1.le
    have own (w : V) (wd : w∈D) : G.Adj q w↔w=p t := by
      constructor
      · intro a
        exact one _ (Finset.mem_filter.mpr ⟨wd,a⟩) _ (Finset.mem_filter.mpr ⟨pm _,qt⟩)
      · rintro rfl
        exact qt
    exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_univ _,Finset.mem_filter.mpr ⟨qQ,own,high⟩⟩
  have frame (h : Fin 4) (e : Fin 4 ≃ Fin 4) (e0 : e 0=h) :
      ∃ fn : V→Fin 4→V,PortFanFamily G (D : Set V) (p∘e) (B h) fn := by
    have att' (q : V) (out : q∉D) : ∃ i,G.Adj q ((p∘e) i) := by
      obtain ⟨j,hj⟩ := attach q out
      exact ⟨e.symm j,by simpa using hj⟩
    have pal' (q : V) (out : q∉D) (x : V) (xd : x∈D) (ax : G.Adj q x) :
        ∃ i,x=(p∘e) i := by
      obtain ⟨j,hj⟩ := palette q out x xd ax
      exact ⟨e.symm j,by simpa using hj⟩
    apply pure_high_family h4 D (p∘e) (fun i=>pm (e i)) (pi.comp e.injective) att' pal' (B h)
    intro q qm
    obtain ⟨qQ,hom,hi⟩ := Finset.mem_filter.mp qm
    exact ⟨qo q qQ,by simpa [Function.comp_apply,e0] using hom,hi⟩
  have caps (h : Fin 4) : (B h).card≤1 := by
    apply Finset.card_le_one.mpr
    intro q qm r rm
    by_cases qr : q=r
    · exact qr
    exfalso
    obtain ⟨a,b,ah,bh,ab,ha,hb⟩ := partners h
    obtain ⟨e,e0,e1,e2⟩ := put_three_labels h a b ah.symm bh.symm ab
    let t : Fin 4→V := p∘e
    have te0 : t 0=p h := by simp [t,e0]
    have te1 : t 1=p a := by simp [t,e1]
    have te2 : t 2=p b := by simp [t,e2]
    have tm (i : Fin 4) : t i∈D := pm (e i)
    have ti : Function.Injective t := pi.comp e.injective
    have nt (i j : Fin 4) : ¬G.Adj (t i) (t j) := ind (e i) (e j)
    have chart (ρ : Fin 4 ≃ Fin 4) (ρ0 : ρ 0=0) :
        ∃ fn : V→Fin 4→V,PortFanFamily G (D : Set V) (t∘ρ) (B h) fn := by
      have eρ : (ρ.trans e) 0=h := by
        change e (ρ 0)=h
        rw [ρ0,e0]
      exact frame h (ρ.trans e) eρ
    have goodt (i : Fin 4) (v : V) (vd : v∈D) (vi : G.Adj (t i) v)
        (j k : Fin 4) (ji : j≠i) (ki : k≠i) (jk : j≠k) :
        ¬(G.Adj (t j) v ∧ G.Adj (t k) v) :=
      good (e i) v vd vi (e j) (e k) (fun eq=>ji (e.injective eq))
        (fun eq=>ki (e.injective eq)) (fun eq=>jk (e.injective eq))
    have len3 (i : Fin 4) (i0 : i≠0)
        (oc : ∃ x∉D,G.Adj (t 0) x ∧ G.Adj (t i) x) :
        IsNearestPortStem (G:=G) D t i 0 3 := by
      obtain ⟨j,ji,d,d2,d5,st⟩ := each_has_nearest_clean_port_stem D t tm ti nt hc h7 i
      have j0 : j=0 := by
        by_cases j0 : j=0
        · exact j0
        exfalso
        obtain ⟨ρ,ρ0,ρ1,ρ2⟩ := put_three_labels 0 i j i0.symm (fun eq=>j0 eq.symm) ji.symm
        obtain ⟨F,H⟩ := chart ρ ρ0
        have alt : IsNearestPortStem (G:=G) D (t∘ρ) 1 2 d :=
          nearest_stem_reindex D t ρ 1 2 d (by rwa [ρ1,ρ2])
        rcases ForeignStem.foreign_nearest_stem_without_relay_forces_p9 h4 D (t∘ρ) (B h) F H
          (fun a b=>nt (ρ a) (ρ b)) q r qm rm qr d d2 d5 alt with hp|⟨_,v,vd,vi,vj,tag⟩
        · exact h9 hp
        change G.Adj (t (ρ 1)) v at vi
        change G.Adj (t (ρ 2)) v at vj
        rw [ρ1] at vi
        rw [ρ2] at vj
        rcases tag with z|z
        · exact goodt i v vd vi j (ρ 0) ji (fun h=>(by decide : (0:Fin 4)≠1) (ρ.injective (h.trans ρ1.symm)))
            (fun h=>(by decide : (2:Fin 4)≠0) (ρ.injective (ρ2.trans h))) ⟨vj,z⟩
        · exact goodt i v vd vi j (ρ 3) ji (fun h=>(by decide : (3:Fin 4)≠1) (ρ.injective (h.trans ρ1.symm)))
            (fun h=>(by decide : (2:Fin 4)≠3) (ρ.injective (ρ2.trans h))) ⟨vj,z⟩
      subst j
      have not2 : d≠2 := by
        intro eq
        subst d
        obtain ⟨w,wp,wd,l,hh,_,_⟩ := st
        obtain ⟨x,xo,hx,ix⟩ := oc
        have iw : G.Adj (t i) (w 1) := by
          rw [←l]
          exact (wp.2 0 1 (by decide)).mpr (by decide)
        have hw : G.Adj (t 0) (w 1) := by
          rw [←hh,SimpleGraph.adj_comm]
          exact (wp.2 1 2 (by decide)).mpr (by decide)
        have e := h4 (t i) (t 0) x (w 1) (fun z=>i0 (ti z)) ix hx iw hw
        exact xo (e.symm ▸ wd _)
      have notLong : ¬4≤d := by
        intro large
        let ρ := Equiv.swap 1 i
        have ρ0 : ρ 0=0 := Equiv.swap_apply_of_ne_of_ne (by decide) i0.symm
        have ρ1 : ρ 1=i := Equiv.swap_apply_left _ _
        obtain ⟨F,H⟩ := chart ρ ρ0
        have alt : IsNearestPortStem (G:=G) D (t∘ρ) 1 0 d :=
          nearest_stem_reindex D t ρ 1 0 d (by rwa [ρ1,ρ0])
        exact h9 (IncomingLongStem.incoming_nearest_stem_length_four_or_five_forces_p9
          h4 D (t∘ρ) (B h) F H (fun a b=>nt (ρ a) (ρ b)) q r qm rm qr d large d5 alt)
      have eq : d=3 := by omega
      rwa [eq] at st
    have P1 : ∃ x∉D,G.Adj (t 0) x ∧ G.Adj (t 1) x := by rwa [te0,te1]
    have P2 : ∃ x∉D,G.Adj (t 0) x ∧ G.Adj (t 2) x := by rwa [te0,te2]
    obtain ⟨F,H⟩ := frame h e e0
    exact h9 (TwoIncomingNearest.two_nearest_three_edge_incoming_stems_or_induced_p9
      h4 D t (B h) F H nt q r qm rm qr
      (len3 1 (by decide) P1) (len3 2 (by decide) P2))
  have sum : (∑ a : Fin 4,(B a).card)≤4 := by
    calc
      _≤∑ _i : Fin 4,(1:Nat) := Finset.sum_le_sum (fun i _=>caps i)
      _=4 := by decide
  exact (Finset.card_le_card cover).trans (Finset.card_biUnion_le.trans sum)

#print axioms nearest_stem_reindex
#print axioms four_port_pure_highs_at_most_four_when_pairs_occupied
end Graffiti133P5CliqueArms
