import P5CliqueFourNearThreeArmFans133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem high_single_site_has_clean_four_port_fan
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V)
    (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ w∈D,G.Adj q w→∃ i,w=p i)
    (q : V) (qo : q∉D) (home : ∀ w∈D,G.Adj q w↔w=p 0) (high : 3<localIndependence G q) :
      ∃ fn : Fin 4→V,fn 0=q ∧
        (∀ i,fn i∉D) ∧
        (∀ i x,x∈D→(G.Adj (fn i) x↔x=p i)) ∧
        ∀ i j,i<j→(G.Adj (fn i) (fn j)↔i=0) := by
  classical
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  choose lab hlab using attach
  let tag (q : V) := if h : q∉D then p (lab q h) else q
  have pick (q : V) (qo : q∉D) : tag q∈D ∧ tag q∈P ∧ G.Adj q (tag q) := by
    have e : tag q=p (lab q qo) := dif_pos qo
    rw [e]
    exact ⟨pm _,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,hlab q qo⟩
  have ne : (localIndependentSets G q).Nonempty := by
    refine ⟨∅,?_⟩
    simp [localIndependentSets]
  obtain ⟨S,hS,sval⟩ := Finset.exists_mem_eq_sup _ ne Finset.card
  have sc : S.card≥4 := by
    change localIndependence G q=S.card at sval
    omega
  have info : (∀ x∈S,G.Adj q x) ∧ (∀ x∈S,∀ y∈S,¬G.Adj x y) := by
    simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,
      Finset.subset_iff,Finset.mem_univ,true_and] using hS
  let g (x : V) := if x∈D then x else tag x
  have hit (x : V) (xm : x∈S) : g x∈P := by
    by_cases xd : x∈D
    · obtain ⟨i,ix⟩ := palette q qo x xd (info.1 _ xm)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simpa only [g,if_pos xd] using ix.symm⟩
    · simpa only [g,if_neg xd] using (pick x xd).2.1
  have inj : Set.InjOn g (S : Set V) := by
    intro v vm w wm e
    by_cases vd : v∈D
    · by_cases wd : w∈D
      · simpa only [g,if_pos vd,if_pos wd] using e
      simp only [g,if_pos vd,if_neg wd] at e
      exact ((info.2 w wm v vm) (e.symm ▸ (pick w wd).2.2)).elim
    by_cases wd : w∈D
    · simp only [g,if_neg vd,if_pos wd] at e
      exact ((info.2 v vm w wm) (e ▸ (pick v vd).2.2)).elim
    simp only [g,if_neg vd,if_neg wd] at e
    have qn : q≠tag v := fun eq=>qo (eq.symm ▸ (pick v vd).1)
    exact h4 q (tag v) v w qn (info.1 _ vm) (pick v vd).2.2.symm
      (info.1 _ wm) (e.symm ▸ (pick w wd).2.2).symm
  have sub : S.image g⊆P := by
    intro v vm
    obtain ⟨w,wm,rfl⟩ := Finset.mem_image.mp vm
    exact hit w wm
  have im := Finset.card_image_of_injOn inj
  have eq : S.image g=P := Finset.eq_of_subset_of_card_le sub (by omega)
  have repr (i : Fin 4) (i0 : i≠0) : ∃ x∈S,x∉D ∧ ∀ w∈D,G.Adj x w↔w=p i := by
    have M : p i∈S.image g := eq.symm ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    obtain ⟨x,xS,xg⟩ := Finset.mem_image.mp M
    have xo : x∉D := by
      intro xm
      have xp : x=p 0 := (home x xm).mp (info.1 _ xS)
      simp only [g,if_pos xm] at xg
      exact i0 (pi (xg.symm.trans xp))
    simp only [g,if_neg xo] at xg
    have xi : G.Adj x (p i) := xg ▸ (pick x xo).2.2
    refine ⟨x,xS,xo,?_⟩
    intro y yd
    constructor
    · intro xy
      obtain ⟨j,jy⟩ := palette x xo y yd xy
      by_cases ji : j=i
      · exact jy.trans (congrArg p ji)
      have pj : p j∈S.image g := eq.symm ▸ Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
      obtain ⟨z,zS,zg⟩ := Finset.mem_image.mp pj
      by_cases zd : z∈D
      · have zp : z=p j := by simpa only [g,if_pos zd] using zg
        have xz : G.Adj x z := (jy.trans zp.symm) ▸ xy
        exact ((info.2 x xS z zS) xz).elim
      · simp only [g,if_neg zd] at zg
        have zx : G.Adj z (p j) := zg ▸ (pick z zd).2.2
        have xx : G.Adj x (p j) := jy ▸ xy
        have id := h4 q (p j) x z (fun e=>qo (e.symm ▸ pm j))
          (info.1 _ xS) xx.symm (info.1 _ zS) zx.symm
        have pEq : p i=p j := xg.symm.trans ((congrArg tag id).trans zg)
        exact (ji (pi pEq).symm).elim
    · rintro rfl
      exact xi
  choose v vS vo va using repr
  let fn (i : Fin 4) := if h : i=0 then q else v i h
  have z : fn 0=q := dif_pos rfl
  have s (i : Fin 4) (i0 : i≠0) : fn i=v i i0 := dif_neg i0
  have out (i : Fin 4) : fn i∉D := by
    by_cases e : i=0
    · subst i
      simpa only [z] using qo
    · rw [s i e]
      exact vo i e
  have only (i : Fin 4) (w : V) (wd : w∈D) : G.Adj (fn i) w↔w=p i := by
    by_cases ei : i=0
    · subst i
      simpa only [z] using home w wd
    · rw [s i ei]
      exact va i ei w wd
  refine ⟨fn,z,out,only,?_⟩
  intro i j ij
  have j0 : j≠0 := by
    intro e
    subst j
    exact (not_lt_of_ge (Fin.zero_le i)) ij
  by_cases i0 : i=0
  · subst i
    rw [z,s j j0]
    exact ⟨fun _=>rfl,fun _=>info.1 _ (vS j j0)⟩
  · rw [s i i0,s j j0]
    exact ⟨fun e=>(info.2 _ (vS i i0) _ (vS j j0) e).elim,fun e=>(i0 e).elim⟩

#print axioms high_single_site_has_clean_four_port_fan
end Graffiti133P5CliqueArms
