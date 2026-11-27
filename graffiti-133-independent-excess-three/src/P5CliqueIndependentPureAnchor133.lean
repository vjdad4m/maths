import P5CliqueForeignNearest133
import P5CliqueIndependentFanBudget133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133 Graffiti133Camby
open scoped Classical BigOperators
set_option maxHeartbeats 3500000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem put_three_labels (a b c : Fin 4) (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    ∃ e : Fin 4 ≃ Fin 4, e 0=a ∧ e 1=b ∧ e 2=c := by
  let f := Equiv.swap 0 a
  have f0 : f 0=a := Equiv.swap_apply_left _ _
  let j := f.symm b
  have fj : f j=b := f.apply_symm_apply b
  have j0 : j≠0 := fun h=>ab (f0.symm.trans ((congrArg f h).symm.trans fj))
  let g := (Equiv.swap 1 j).trans f
  have g0 : g 0=a := by
    change f (Equiv.swap 1 j 0)=a
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 4)≠1) j0.symm,f0]
  have g1 : g 1=b := by
    change f (Equiv.swap 1 j 1)=b
    rw [Equiv.swap_apply_left,fj]
  let k := g.symm c
  have gk : g k=c := g.apply_symm_apply c
  have k0 : k≠0 := fun h=>ac (g0.symm.trans ((congrArg g h).symm.trans gk))
  have k1 : k≠1 := fun h=>bc (g1.symm.trans ((congrArg g h).symm.trans gk))
  let e := (Equiv.swap 2 k).trans g
  refine ⟨e,?_,?_,?_⟩
  · change g (Equiv.swap 2 k 0)=a
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 4)≠2) k0.symm,g0]
  · change g (Equiv.swap 2 k 1)=b
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 4)≠2) k1.symm,g1]
  · change g (Equiv.swap 2 k 2)=c
    rw [Equiv.swap_apply_left,gk]

theorem pure_high_family (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V)
    (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ w∈D,G.Adj q w→∃ i,w=p i)
    (A : Finset V)
    (qa : ∀ q∈A,q∉D ∧ (∀ w∈D,G.Adj q w↔ w=p 0) ∧ 3<localIndependence G q) :
    ∃ f : V→Fin 4→V,PortFanFamily G (D : Set V) p A f := by
  classical
  have ex (q : {v : V // v∈A}) : ∃ F : Fin 4→V, F 0=q.val ∧ (∀ i,F i∉D) ∧
      (∀ i w,w∈D→(G.Adj (F i) w↔w=p i)) ∧ ∀ i j,i<j→(G.Adj (F i) (F j)↔i=0) := by
    obtain ⟨qo,tag,score⟩ := qa q.val q.property
    exact high_single_site_has_clean_four_port_fan h4 D p pm pi attach palette _ qo tag score
  choose f fc fo fp fs using ex
  let fn (q : V) (i : Fin 4) := if h : q∈A then f ⟨q,h⟩ i else q
  refine ⟨fn,pm,pi,?_,?_,?_,?_⟩
  · intro q qm i
    simpa only [fn,dif_pos qm] using fo ⟨q,qm⟩ i
  · intro q qm
    simpa only [fn,dif_pos qm] using fc ⟨q,qm⟩
  · intro q qm i w wd
    simpa only [fn,dif_pos qm] using fp ⟨q,qm⟩ i w wd
  · intro q qm i j ij
    simpa only [fn,dif_pos qm] using fs ⟨q,qm⟩ i j ij

/-- If some port cannot meet two other ports through a single inner vertex,
there are at most six pure score-four exterior vertices. -/
theorem four_port_pure_highs_at_most_six_of_good_anchor
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D : Finset V) (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (ind : ∀ i j,¬G.Adj (p i) (p j))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7)
    (i : Fin 4)
    (good : ∀ v∈D,G.Adj (p i) v → ∀ j k : Fin 4,j≠i→k≠i→j≠k→
      ¬(G.Adj (p j) v ∧ G.Adj (p k) v)) :
    let Q := (Finset.univ : Finset V)\D
    (Q.filter (fun q=>3<localIndependence G q ∧ (D.filter (G.Adj q)).card=1)).card≤6 := by
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
  have caps (h : Fin 4) : (B h).card≤2 := by
    let e := Equiv.swap 0 h
    obtain ⟨fn,H⟩ := frame h e (Equiv.swap_apply_left _ _)
    exact independent_palette_at_most_two_fans h4 h9 H (fun i j=>ind (e i) (e j))
  obtain ⟨j,ji,d,d2,d5,stem⟩ := each_has_nearest_clean_port_stem D p pm pi ind hc h7 i
  have short (h : Fin 4) (hi : h≠i) (hj : h≠j) : (B h).card≤1 := by
    apply Finset.card_le_one.mpr
    intro x xm y ym
    by_cases xy : x=y
    · exact xy
    exfalso
    obtain ⟨e,e0,e1,e2⟩ := put_three_labels h i j hi hj ji.symm
    obtain ⟨fn,H⟩ := frame h e e0
    have stem' : IsNearestPortStem (G:=G) D (p∘e) 1 2 d := by
      obtain ⟨w,wp,wd,l,r,core,front⟩ := stem
      refine ⟨w,wp,wd,?_,?_,fun t tl tr c=>core t tl tr (e c),?_⟩
      · simpa only [Function.comp_apply,e1] using l
      · simpa only [Function.comp_apply,e2] using r
      · intro t tl c cn a
        have away : e c≠i := fun eq=>cn (e.injective (eq.trans e1.symm))
        exact front t tl (e c) away a
    rcases ForeignStem.foreign_nearest_stem_without_relay_forces_p9 h4 D (p∘e) (B h) fn H
      (fun a b=>ind (e a) (e b)) x y xm ym xy d d2 d5 stem' with hp|⟨_,v,vd,vi,vj,vl⟩
    · exact h9 hp
    change G.Adj (p (e 1)) v at vi
    change G.Adj (p (e 2)) v at vj
    rw [e1] at vi
    rw [e2] at vj
    rcases vl with vl|vl
    · exact good v vd vi j (e 0) ji (fun eq=>(by decide : (0:Fin 4)≠1) (e.injective (eq.trans e1.symm)))
        (fun eq=>(by decide : (2:Fin 4)≠0) (e.injective (e2.trans eq))) ⟨vj,vl⟩
    · exact good v vd vi j (e 3) ji (fun eq=>(by decide : (3:Fin 4)≠1) (e.injective (eq.trans e1.symm)))
        (fun eq=>(by decide : (2:Fin 4)≠3) (e.injective (e2.trans eq))) ⟨vj,vl⟩
  let T : Finset (Fin 4) := {i,j}
  have two : T.card=2 := by simp [T,ji.symm]
  have sum : (∑ a : Fin 4,(B a).card)≤6 := by
    have point (a : Fin 4) : (B a).card≤1+(if a∈T then 1 else 0) := by
      by_cases yes : a∈T
      · rw [if_pos yes]
        exact caps a
      have ai : a≠i := fun e=>yes (e.symm ▸ Finset.mem_insert_self _ _)
      have aj : a≠j := fun e=>yes (e.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rw [if_neg yes,Nat.add_zero]
      exact short a ai aj
    have ss := Finset.sum_le_sum (fun a (_ : a∈(Finset.univ : Finset (Fin 4)))=>point a)
    rw [Finset.sum_add_distrib] at ss
    have zz : (∑ a : Fin 4,(if a∈T then 1 else 0 : Nat))=T.card := by
      rw [←Finset.card_filter]
      congr 1
      ext a
      simp
    have cc : (∑ _a : Fin 4,(1:Nat))=4 := by decide
    rw [zz,cc,two] at ss
    exact ss
  exact (Finset.card_le_card cover).trans (Finset.card_biUnion_le.trans sum)

#print axioms pure_high_family
#print axioms four_port_pure_highs_at_most_six_of_good_anchor
end Graffiti133P5CliqueArms
