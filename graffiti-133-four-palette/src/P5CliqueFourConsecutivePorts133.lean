import P5CliqueMultiPortBudget133
import Mathlib.Data.Finset.Powerset

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem outside_independence_le_of_nonisolated_port
    (h4 : FourCycleFree G) (D : Finset V) (tag : V→V)
    (choosePort : ∀ v∉D,tag v∈D ∧ G.Adj v (tag v))
    (P : Finset V) (pc : P.card=4)
    (palette : ∀ q∉D, ∀ p∈D,G.Adj q p →p∈P)
    (q : V) (qo : q∉D) (p t : V) (pm : p∈D) (tm : t∈D) (tp : t∈P)
    (qp : G.Adj q p) (pt : G.Adj p t) : localIndependence G q≤3 := by
  classical
  let Q := (Finset.univ : Finset V)\D
  unfold localIndependence
  apply Finset.sup_le_iff.mpr
  intro S hS
  have info : (∀ x∈S,G.Adj q x) ∧ (∀ x∈S,∀ y∈S,¬G.Adj x y) := by
    simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,
      Finset.mem_univ,true_and] using hS
  let f (v : V) := if v∈D then v else tag v
  have hit (v : V) (vm : v∈S) : f v∈P := by
    by_cases vd : v∈D
    · simpa only [f,if_pos vd] using palette q qo v vd (info.1 _ vm)
    · simpa only [f,if_neg vd] using palette v vd (tag v) (choosePort v vd).1 (choosePort v vd).2
  have inj : Set.InjOn f (S : Set V) := by
    intro v vm w wm e
    by_cases vd : v∈D
    · by_cases wd : w∈D
      · simpa only [f,if_pos vd,if_pos wd] using e
      simp only [f,if_pos vd,if_neg wd] at e
      exact ((info.2 w wm v vm) (e.symm ▸ (choosePort w wd).2)).elim
    by_cases wd : w∈D
    · simp only [f,if_neg vd,if_pos wd] at e
      exact ((info.2 v vm w wm) (e ▸ (choosePort v vd).2)).elim
    simp only [f,if_neg vd,if_neg wd] at e
    have qn : q≠tag v := fun eq=>qo (eq.symm ▸ (choosePort v vd).1)
    exact h4 q (tag v) v w qn (info.1 _ vm) (choosePort v vd).2.symm
      (info.1 _ wm) (e.symm ▸ (choosePort w wd).2).symm
  have sub : S.image f⊆P := by
    intro v vm
    obtain ⟨w,wm,rfl⟩ := Finset.mem_image.mp vm
    exact hit w wm
  have miss : ¬(p∈S.image f ∧ t∈S.image f) := by
    rintro ⟨hp,ht⟩
    obtain ⟨x,xm,ex⟩ := Finset.mem_image.mp hp
    obtain ⟨y,ym,ey⟩ := Finset.mem_image.mp ht
    have yd : y∈D := by
      by_contra yd
      simp only [f,if_neg yd] at ey
      have ty : G.Adj t y := (ey ▸ (choosePort y yd).2).symm
      have e := h4 q t p y (fun e=>qo (e.symm ▸ tm)) qp pt.symm (info.1 _ ym) ty
      exact yd (e ▸ pm)
    have yt : y=t := by simpa only [f,if_pos yd] using ey
    subst y
    by_cases xd : x∈D
    · have xp : x=p := by simpa only [f,if_pos xd] using ex
      subst x
      exact info.2 p xm t ym pt
    · simp only [f,if_neg xd] at ex
      have px : G.Adj p x := (ex ▸ (choosePort x xd).2).symm
      have e := h4 q p x t (fun e=>qo (e.symm ▸ pm)) (info.1 _ xm) px (info.1 _ ym) pt
      exact xd (e.symm ▸ tm)
  have lt : (S.image f).card<P.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨sub,?_⟩
    intro eq
    exact miss ⟨eq.symm ▸ palette q qo p pm qp,eq.symm ▸ tp⟩
  rw [Finset.card_image_of_injOn inj,pc] at lt
  omega

theorem extra_port_incidence_le_admissible_pair
    (h4 : FourCycleFree G) (D P : Finset V) (sub : P⊆D) (tag : V→V)
    (choosePort : ∀ v∉D,tag v∈P ∧ G.Adj v (tag v))
    (palette : ∀ v∉D,∀ w∈D,G.Adj v w→w∈P) :
    let Q := (Finset.univ : Finset V)\D
    (∑ q∈Q,((D.filter (G.Adj q)).card-1))≤((P.powersetCard 2).filter (fun F=>¬∃ x∈D,∀ p∈F,G.Adj x p)).card := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let F (q : V) := (D.filter (G.Adj q)).erase (tag q)
  let A (q : V) := (F q).image (fun p=>(q,p))
  let Pair := Q.biUnion A
  have qout (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have dis : (Q : Set V).PairwiseDisjoint A := by
    intro q _ r _ ne
    apply Finset.disjoint_left.mpr
    intro x xm xn
    obtain ⟨a,_,xa⟩ := Finset.mem_image.mp xm
    obtain ⟨b,_,xb⟩ := Finset.mem_image.mp xn
    exact ne (congrArg Prod.fst (xa.trans xb.symm))
  have pairCard : Pair.card=∑ q∈Q,((D.filter (G.Adj q)).card-1) := by
    change (Q.biUnion A).card=_
    rw [Finset.card_biUnion dis]
    apply Finset.sum_congr rfl
    intro q qm
    have e : (A q).card=(F q).card :=
      Finset.card_image_of_injective _ (fun _ _ e=>congrArg Prod.snd e)
    have m : tag q∈D.filter (G.Adj q) :=
      Finset.mem_filter.mpr ⟨sub (choosePort q (qout _ qm)).1,(choosePort q (qout _ qm)).2⟩
    have co : (F q).card+1=(D.filter (G.Adj q)).card := Finset.card_erase_add_one m
    omega
  have info (p : (Pair : Finset (V×V))) : p.val.1∈Q ∧ p.val.2∈D ∧
      G.Adj p.val.1 p.val.2 ∧ p.val.2≠tag p.val.1 := by
    obtain ⟨q,qm,m⟩ := Finset.mem_biUnion.mp p.property
    obtain ⟨w,wm,e⟩ := Finset.mem_image.mp m
    obtain ⟨ne,h⟩ := Finset.mem_erase.mp wm
    obtain ⟨wd,adj⟩ := Finset.mem_filter.mp h
    rw [←e]
    exact ⟨qm,wd,adj,ne⟩
  let Allowed := (P.powersetCard 2).filter (fun F=>¬∃ x∈D,∀ p∈F,G.Adj x p)
  let map : {p : V×V // p∈Pair} → {F : Finset V // F∈Allowed} := fun q=>
    ⟨{tag q.val.1,q.val.2},Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨by
      intro a am
      rcases Finset.mem_insert.mp am with e|e
      · exact e.symm ▸ (choosePort q.val.1 (qout _ (info q).1)).1
      · exact (Finset.mem_singleton.mp e).symm ▸
          palette q.val.1 (qout _ (info q).1) q.val.2 (info q).2.1 (info q).2.2.1,by
      have ne := (info q).2.2.2
      simp [ne.symm]⟩,by
      rintro ⟨x,xd,hx⟩
      have hq := choosePort q.val.1 (qout _ (info q).1)
      have eq := h4 (tag q.val.1) q.val.2 q.val.1 x (info q).2.2.2.symm
        hq.2.symm (info q).2.2.1.symm
        (hx _ (Finset.mem_insert_self _ _)).symm
        (hx _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))).symm
      exact qout _ (info q).1 (eq.symm ▸ xd)⟩⟩
  have inj : Function.Injective map := by
    intro u v e
    have eq : ({tag u.val.1,u.val.2} : Finset V)={tag v.val.1,v.val.2} := congrArg Subtype.val e
    have conn (a : V) (am : a∈({tag u.val.1,u.val.2}:Finset V)) : G.Adj v.val.1 a := by
      rw [eq] at am
      rcases Finset.mem_insert.mp am with h|h
      · exact h.symm ▸ (choosePort v.val.1 (qout _ (info v).1)).2
      · exact (Finset.mem_singleton.mp h).symm ▸ (info v).2.2.1
    have tagV := conn _ (Finset.mem_insert_self _ _)
    have otherV := conn _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have first : u.val.1=v.val.1 :=
      h4 (tag u.val.1) u.val.2 u.val.1 v.val.1 (info u).2.2.2.symm
        (choosePort u.val.1 (qout _ (info u).1)).2.symm (info u).2.2.1.symm tagV.symm otherV.symm
    have m : u.val.2∈({tag v.val.1,v.val.2}:Finset V) := eq ▸
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rcases Finset.mem_insert.mp m with bad|ok
    · exact ((info u).2.2.2 (bad.trans (congrArg tag first).symm)).elim
    exact Subtype.ext (Prod.ext first (Finset.mem_singleton.mp ok))
  have le := Fintype.card_le_of_injective map inj
  have hle : Pair.card≤Allowed.card := by simpa only [Fintype.card_coe] using le
  rw [pairCard] at hle
  exact hle

#print axioms outside_independence_le_of_nonisolated_port
#print axioms extra_port_incidence_le_admissible_pair
private theorem P7free_connected_core_budget (D : Finset V)
    (h4 : FourCycleFree G) (hc : (G.induce (D : Set V)).Connected)
    (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)≤3*D.card := by
  classical
  let J := G.induce (D : Set V)
  have four : FourCycleFree J := by
    intro a b x y ne ax bx ay by'
    exact Subtype.ext (h4 a.val b.val x.val y.val (fun e=>ne (Subtype.ext e)) ax bx ay by')
  have eq : Fintype.card (D : Set V)=D.card := Fintype.card_coe _
  change (∑ x : (D : Set V),localIndependence J x)≤3*D.card
  by_contra h
  have high : 3*Fintype.card (D : Set V)<∑ x : (D : Set V),localIndependence J x := by omega
  have mean : 3<averageLocal J := by
    letI := hc.nonempty
    have pos : (0:ℚ)<(Fintype.card (D : Set V):ℚ) := by exact_mod_cast Fintype.card_pos (α:=(D : Set V))
    unfold averageLocal
    apply (lt_div_iff₀ pos).mpr
    rw [← Nat.cast_sum]
    exact_mod_cast high
  exact h7 (Graffiti133Revisit.P7_of_strict_mean_three J hc four mean)

theorem four_port_nonisolated_admissible_ambient_mean_four
    (h4 : FourCycleFree G) (D P : Finset V) (sub : P⊆D) (pc : P.card=4)
    (attach : ∀ q∉D,∃ p∈P,G.Adj q p)
    (palette : ∀ q∉D,∀ p∈D,G.Adj q p→p∈P)
    (nonisolated : ∀ p∈P,∃ t∈P,G.Adj p t)
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7)
    (paircap : ((P.powersetCard 2).filter (fun F=>¬∃ x∈D,∀ p∈F,G.Adj x p)).card≤D.card) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  choose f fw using attach
  let tag (q : V) := if h : q∉D then f q h else q
  have pick (q : V) (qo : q∉D) : tag q∈P ∧ G.Adj q (tag q) := by simpa only [tag,dif_pos qo] using fw q qo
  have pickD (q : V) (qo : q∉D) : tag q∈D ∧ G.Adj q (tag q) := ⟨sub (pick q qo).1,(pick q qo).2⟩
  have localBound (q : V) (qo : q∉D) : localIndependence G q≤3 := by
    obtain ⟨t,tp,e⟩ := nonisolated _ (pick q qo).1
    exact outside_independence_le_of_nonisolated_port h4 D tag pickD P pc palette q qo _ t
      (pickD q qo).1 (sub tp) tp (pickD q qo).2 e
  have outer : (∑ q∈Q, localIndependence G q)≤3*Q.card := by
    calc
      _≤∑ _q∈Q,3 := Finset.sum_le_sum (fun q qm=>localBound q (Finset.mem_sdiff.mp qm).2)
      _=_ := by simp [Nat.mul_comm]
  have extra := extra_port_incidence_le_admissible_pair h4 D P sub tag pick palette
  have cross := core_crossings_eq_card_add_extra D tag pickD
  have bound := core_and_exterior_independence_sum (G:=G) D
  have core := P7free_connected_core_budget D h4 hc h7
  have cards := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at cards
  change Q.card+D.card=Fintype.card V at cards
  change (∑ q∈Q,((D.filter (G.Adj q)).card-1))≤_ at extra
  change (∑ q∈Q,(D.filter (G.Adj q)).card)=Q.card+(∑ q∈Q,((D.filter (G.Adj q)).card-1)) at cross
  change _≤_ + (∑ q∈Q,localIndependence G q) + (∑ q∈Q,(D.filter (G.Adj q)).card) at bound
  omega

theorem four_consecutive_ports_ambient_mean_four
    (h4 : FourCycleFree G) (D : Finset V) (a b c d : V)
    (am : a∈D) (bm : b∈D) (cm : c∈D) (dm : d∈D)
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d)
    (ac : a≠c) (ad : a≠d) (bd : b≠d)
    (attach : ∀ q∉D,∃ t∈({a,b,c,d} : Finset V),G.Adj q t)
    (palette : ∀ q∉D,∀ p∈D,G.Adj q p→p∈({a,b,c,d} : Finset V))
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  have ane := ab.ne
  have bne := bc.ne
  have cne := cd.ne
  let P : Finset V := {a,b,c,d}
  have sub : P⊆D := by
    intro x xm
    simp only [P,Finset.mem_insert,Finset.mem_singleton] at xm
    rcases xm with rfl|rfl|rfl|rfl <;> assumption
  have pc : P.card=4 := by simp [P,ane,ac,ad,bne,bd,cne]
  refine four_port_nonisolated_admissible_ambient_mean_four h4 D P sub pc attach palette ?_ hc h7 ?_
  · intro x xm
    simp only [P,Finset.mem_insert,Finset.mem_singleton] at xm
    rcases xm with rfl|rfl|rfl|rfl
    · exact ⟨b,by simp [P],ab⟩
    · exact ⟨a,by simp [P],ab.symm⟩
    · exact ⟨b,by simp [P],bc.symm⟩
    · exact ⟨c,by simp [P],cd.symm⟩
  · let S := P.powersetCard 2
    let X : Finset V := {a,c}
    let Y : Finset V := {b,d}
    have xc : X∈S := Finset.mem_powersetCard.mpr ⟨by
      intro x xm
      simp only [X,Finset.mem_insert,Finset.mem_singleton] at xm
      rcases xm with rfl|rfl <;> simp [P],by simp [X,ac]⟩
    have yc : Y∈S := Finset.mem_powersetCard.mpr ⟨by
      intro x xm
      simp only [Y,Finset.mem_insert,Finset.mem_singleton] at xm
      rcases xm with rfl|rfl <;> simp [P],by simp [Y,bd]⟩
    have ne : X≠Y := by
      intro eq
      have m : a∈Y := eq ▸ (Finset.mem_insert_self _ _ : a∈X)
      simp [Y,ane,ad] at m
    have suberase :
        (S.filter (fun F=>¬∃ x∈D,∀ p∈F,G.Adj x p))⊆(S.erase X).erase Y := by
      intro F fm
      obtain ⟨fs,bad⟩ := Finset.mem_filter.mp fm
      have fx : F≠X := by
        rintro rfl
        apply bad
        refine ⟨b,bm,?_⟩
        intro z zm
        simp only [X,Finset.mem_insert,Finset.mem_singleton] at zm
        rcases zm with rfl|rfl
        · exact ab.symm
        · exact bc
      have fy : F≠Y := by
        rintro rfl
        apply bad
        refine ⟨c,cm,?_⟩
        intro z zm
        simp only [Y,Finset.mem_insert,Finset.mem_singleton] at zm
        rcases zm with rfl|rfl
        · exact bc.symm
        · exact cd
      exact Finset.mem_erase.mpr ⟨fy,Finset.mem_erase.mpr ⟨fx,fs⟩⟩
    have z1 := Finset.card_erase_add_one xc
    have z2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨ne.symm,yc⟩)
    have s6 : S.card=6 := by rw [Finset.card_powersetCard,pc]; decide
    have le := Finset.card_le_card suberase
    have d4 := Finset.card_le_card sub
    change (S.filter (fun F=>¬∃ x∈D,∀ p∈F,G.Adj x p)).card≤D.card
    omega

#print axioms four_port_nonisolated_admissible_ambient_mean_four
#print axioms four_consecutive_ports_ambient_mean_four
end Graffiti133P5CliqueArms
