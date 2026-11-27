import P5CliqueOnePortAmbientBudget133
import Mathlib.Data.Finset.Powerset

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem outside_independence_le_core_neighbors_union_assigned_ports
    (h4 : FourCycleFree G) (D : Finset V) (tag : V→V)
    (choosePort : ∀ v∉D,tag v∈D ∧ G.Adj v (tag v))
    (q : V) (qo : q∉D) :
    let Q := (Finset.univ : Finset V)\D
    localIndependence G q≤((D.filter (G.Adj q))∪((Q.filter (G.Adj q)).image tag)).card := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let P := (D.filter (G.Adj q))∪((Q.filter (G.Adj q)).image tag)
  unfold localIndependence
  apply Finset.sup_le_iff.mpr
  intro S hS
  have info : (∀ x∈S,G.Adj q x) ∧ (∀ x∈S,∀ y∈S,¬G.Adj x y) := by
    simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,
      Finset.mem_univ,true_and] using hS
  let f (v : V) := if v∈D then v else tag v
  have hit (v : V) (vm : v∈S) : f v∈P := by
    by_cases vd : v∈D
    · have m : v∈D.filter (G.Adj q) := Finset.mem_filter.mpr ⟨vd,info.1 _ vm⟩
      exact Finset.mem_union.mpr (Or.inl (by simpa only [f,if_pos vd] using m))
    have m : tag v∈(Q.filter (G.Adj q)).image tag :=
      Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,vd⟩,info.1 _ vm⟩,rfl⟩
    exact Finset.mem_union.mpr (Or.inr (by simpa only [f,if_neg vd] using m))
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
  rw [← Finset.card_image_of_injOn inj]
  exact Finset.card_le_card sub

theorem outside_independence_le_attachment_palette
    (h4 : FourCycleFree G) (D P : Finset V) (tag : V→V)
    (choosePort : ∀ v∉D,tag v∈D ∧ tag v∈P ∧ G.Adj v (tag v))
    (palette : ∀ v∉D,∀ w∈D,G.Adj v w→w∈P)
    (q : V) (qo : q∉D) :
    localIndependence G q≤P.card := by
  classical
  apply (outside_independence_le_core_neighbors_union_assigned_ports h4 D tag
    (fun v vo=>⟨(choosePort v vo).1,(choosePort v vo).2.2⟩) q qo).trans
  apply Finset.card_le_card
  apply Finset.union_subset
  · intro w wm
    exact palette q qo w (Finset.mem_filter.mp wm).1 (Finset.mem_filter.mp wm).2
  · intro v vm
    obtain ⟨w,wm,rfl⟩ := Finset.mem_image.mp vm
    exact (choosePort w (Finset.mem_sdiff.mp (Finset.mem_filter.mp wm).1).2).2.1

theorem outside_independence_le_chosen_visible_add_extra
    (h4 : FourCycleFree G) (D : Finset V) (tag : V→V)
    (choosePort : ∀ v∉D,tag v∈D ∧ G.Adj v (tag v))
    (q : V) (qo : q∉D) :
    let Q := (Finset.univ : Finset V)\D
    localIndependence G q≤(((insert q (Q.filter (G.Adj q))).image tag).card)+
      ((D.filter (G.Adj q)).card-1) := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let N := D.filter (G.Adj q)
  let I := (Q.filter (G.Adj q)).image tag
  let B := (insert q (Q.filter (G.Adj q))).image tag
  have m : tag q∈N := Finset.mem_filter.mpr (choosePort q qo)
  have cover : N∪I⊆B∪N.erase (tag q) := by
    intro v vm
    rcases Finset.mem_union.mp vm with vn|vn
    · by_cases e : v=tag q
      · subst v
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨q,Finset.mem_insert_self _ _,rfl⟩))
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_erase.mpr ⟨e,vn⟩))
    obtain ⟨w,wm,rfl⟩ := Finset.mem_image.mp vn
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨w,Finset.mem_insert_of_mem wm,rfl⟩))
  have a := outside_independence_le_core_neighbors_union_assigned_ports h4 D tag choosePort q qo
  change _≤(N∪I).card at a
  have b := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have c := Finset.card_erase_add_one m
  change _≤B.card+(N.card-1)
  omega

#print axioms outside_independence_le_core_neighbors_union_assigned_ports
#print axioms outside_independence_le_chosen_visible_add_extra

theorem extra_port_incidence_le_choose_pair
    (h4 : FourCycleFree G) (D P : Finset V) (sub : P⊆D) (tag : V→V)
    (choosePort : ∀ v∉D,tag v∈P ∧ G.Adj v (tag v))
    (palette : ∀ v∉D,∀ w∈D,G.Adj v w→w∈P) :
    let Q := (Finset.univ : Finset V)\D
    (∑ q∈Q,((D.filter (G.Adj q)).card-1))≤P.card.choose 2 := by
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
  let map : {p : V×V // p∈Pair} → {F : Finset V // F∈P.powersetCard 2} := fun q=>
    ⟨{tag q.val.1,q.val.2},Finset.mem_powersetCard.mpr ⟨by
      intro a am
      rcases Finset.mem_insert.mp am with e|e
      · exact e.symm ▸ (choosePort q.val.1 (qout _ (info q).1)).1
      · exact (Finset.mem_singleton.mp e).symm ▸
          palette q.val.1 (qout _ (info q).1) q.val.2 (info q).2.1 (info q).2.2.1,by
      have ne := (info q).2.2.2
      simp [ne.symm]⟩⟩
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
  have hle : Pair.card≤(P.powersetCard 2).card := by simpa only [Fintype.card_coe] using le
  rw [pairCard,Finset.card_powersetCard] at hle
  exact hle

#print axioms extra_port_incidence_le_choose_pair

theorem core_and_exterior_independence_sum
    (D : Finset V) :
    let Q := (Finset.univ : Finset V)\D
    (∑ v : V,localIndependence G v)≤
      (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x) +
        (∑ q∈Q, localIndependence G q) + (∑ q∈Q,(D.filter (G.Adj q)).card) := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let J := G.induce (D : Set V)
  let deg (v : V) := (Q.filter (G.Adj v)).card
  have degree : (∑ x∈D,deg x)=∑ y∈Q,(D.filter (G.Adj y)).card := by
    calc
      _ = ∑ x∈D,∑ y∈Q,(if G.Adj x y then 1 else 0 : Nat) := by
        apply Finset.sum_congr rfl
        intro x _
        change (Q.filter (G.Adj x)).card=_
        exact Finset.card_filter (G.Adj x) Q
      _ = ∑ y∈Q,∑ x∈D,(if G.Adj x y then 1 else 0 : Nat) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro y _
        have h : (∑ x∈D,(if G.Adj x y then 1 else 0 : Nat)) =
            ∑ x∈D,(if G.Adj y x then 1 else 0 : Nat) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [SimpleGraph.adj_comm G x y]
        exact h.trans (Finset.card_filter (G.Adj y) D).symm
  have core : (∑ x∈D,localIndependence G x)≤
      (∑ x : (D : Set V),localIndependence J x)+(∑ x∈D,deg x) := by
    calc
      _ = ∑ x : (D : Set V),localIndependence G x.val := Finset.sum_subtype D (fun _=>Iff.rfl) _
      _ ≤ ∑ x : (D : Set V),(localIndependence J x+deg x.val) :=
        Finset.sum_le_sum (fun x _=>core_localIndependence_le_add_outer_degree D x)
      _ = _ := by
        have t : (∑ x : (D : Set V),deg x.val)=∑ x∈D,deg x :=
          (Finset.sum_subtype (p:=fun x=>x∈D) D (fun _=>Iff.rfl) deg).symm
        rw [Finset.sum_add_distrib,t]
  have eq := Finset.sum_sdiff (Finset.subset_univ D) (f:=localIndependence G)
  change (∑ q∈Q,localIndependence G q)+(∑ x∈D,localIndependence G x)=(∑ v : V,localIndependence G v) at eq
  change _≤(∑ x : (D : Set V),localIndependence J x)+(∑ q∈Q,localIndependence G q)+(∑ q∈Q,(D.filter (G.Adj q)).card)
  omega

theorem core_crossings_eq_card_add_extra
    (D : Finset V) (tag : V→V) (choosePort : ∀ v∉D,tag v∈D ∧ G.Adj v (tag v)) :
    let Q := (Finset.univ : Finset V)\D
    (∑ q∈Q,(D.filter (G.Adj q)).card)=Q.card+(∑ q∈Q,((D.filter (G.Adj q)).card-1)) := by
  classical
  let Q := (Finset.univ : Finset V)\D
  have h (q : V) (qm : q∈Q) : 0<(D.filter (G.Adj q)).card :=
    Finset.card_pos.mpr ⟨tag q,Finset.mem_filter.mpr (choosePort q (Finset.mem_sdiff.mp qm).2)⟩
  change (∑ q∈Q,(D.filter (G.Adj q)).card)=Q.card+(∑ q∈Q,((D.filter (G.Adj q)).card-1))
  calc
    _ = ∑ q∈Q,(1+((D.filter (G.Adj q)).card-1)) := by
      apply Finset.sum_congr rfl
      intro q qm
      have e := h q qm
      omega
    _ = _ := by simp [Finset.sum_add_distrib]

theorem multi_attachment_visible_budget
    (h4 : FourCycleFree G) (D : Finset V) (tag : V→V)
    (choosePort : ∀ v∉D,tag v∈D ∧ G.Adj v (tag v)) :
    let Q := (Finset.univ : Finset V)\D
    (∑ v : V,localIndependence G v)≤
      (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x) + Q.card +
        (∑ q∈Q,((insert q (Q.filter (G.Adj q))).image tag).card) +
        2*(∑ q∈Q,((D.filter (G.Adj q)).card-1)) := by
  classical
  let Q := (Finset.univ : Finset V)\D
  have a := core_and_exterior_independence_sum (G:=G) D
  have b := core_crossings_eq_card_add_extra (G:=G) D tag choosePort
  change (∑ q∈Q,(D.filter (G.Adj q)).card)=Q.card+(∑ q∈Q,((D.filter (G.Adj q)).card-1)) at b
  have out : (∑ q∈Q,localIndependence G q) ≤
      ∑ q∈Q,(((insert q (Q.filter (G.Adj q))).image tag).card+((D.filter (G.Adj q)).card-1)) :=
    Finset.sum_le_sum (fun q qm=>outside_independence_le_chosen_visible_add_extra h4 D tag
      choosePort q (Finset.mem_sdiff.mp qm).2)
  rw [Finset.sum_add_distrib] at out
  change (∑ v : V,localIndependence G v)≤
    (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+(∑ q∈Q,localIndependence G q)+
      (∑ q∈Q,(D.filter (G.Adj q)).card) at a
  change _≤(∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+Q.card+
    (∑ q∈Q,((insert q (Q.filter (G.Adj q))).image tag).card)+2*(∑ q∈Q,((D.filter (G.Adj q)).card-1))
  omega

#print axioms core_and_exterior_independence_sum
#print axioms multi_attachment_visible_budget

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

/-- No bound of one attachment per exterior vertex is imposed: instead
all exterior crossings land at at most three middle ports. -/
theorem three_port_palette_multi_attachment_ambient_mean_four
    (h4 : FourCycleFree G) (D P : Finset V) (sub : P⊆D)
    (few : P.card≤3)
    (attach : ∀ v∉D,∃ w∈P,G.Adj v w)
    (palette : ∀ v∉D,∀ w∈D,G.Adj v w→w∈P)
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  have qout (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  choose f fw using attach
  let tag (v : V) := if h : v∉D then f v h else v
  have pick (q : V) (qo : q∉D) : tag q∈P ∧ G.Adj q (tag q) := by simpa only [tag,dif_pos qo] using fw q qo
  have pc (q : V) (qo : q∉D) : tag q∈D ∧ tag q∈P ∧ G.Adj q (tag q) :=
    ⟨sub (pick q qo).1,pick q qo⟩
  have out : (∑ q∈Q,localIndependence G q)≤3*Q.card := by
    calc
      _ ≤ ∑ _q∈Q,3 := Finset.sum_le_sum (fun q qm=>
        (outside_independence_le_attachment_palette h4 D P tag pc palette q (qout _ qm)).trans few)
      _ = _ := by simp [Nat.mul_comm]
  have cap := extra_port_incidence_le_choose_pair h4 D P sub tag pick palette
  have small : P.card.choose 2≤P.card := by
    have z : P.card=0 ∨ P.card=1 ∨ P.card=2 ∨ P.card=3 := by omega
    rcases z with e|e|e|e <;> rw [e] <;> decide
  have leD := Finset.card_le_card sub
  have crossings := core_crossings_eq_card_add_extra D tag (fun q qo=>⟨(pc q qo).1,(pc q qo).2.2⟩)
  have base := P7free_connected_core_budget D h4 hc h7
  have all := core_and_exterior_independence_sum (G:=G) D
  have cards := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at cards
  change Q.card+D.card=Fintype.card V at cards
  change (∑ q∈Q,((D.filter (G.Adj q)).card-1))≤P.card.choose 2 at cap
  change (∑ q∈Q,(D.filter (G.Adj q)).card)=Q.card+(∑ q∈Q,((D.filter (G.Adj q)).card-1)) at crossings
  change _≤(∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+
    (∑ q∈Q,localIndependence G q)+(∑ q∈Q,(D.filter (G.Adj q)).card) at all
  omega

theorem multi_attachment_weighted_slack_P7free_ambient_mean_four
    (h4 : FourCycleFree G) (D : Finset V) (tag : V→V)
    (choosePort : ∀ v∉D,tag v∈D ∧ G.Adj v (tag v))
    (hc : (G.induce (D : Set V)).Connected) (h7 : NoPath (G.induce (D : Set V)) 7)
    (slack : let Q := (Finset.univ : Finset V)\D
      (∑ q∈Q,((insert q (Q.filter (G.Adj q))).image tag).card)+
        2*(∑ q∈Q,((D.filter (G.Adj q)).card-1))≤3*Q.card+D.card) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  let Q := (Finset.univ : Finset V)\D
  have base := P7free_connected_core_budget D h4 hc h7
  have all := multi_attachment_visible_budget h4 D tag choosePort
  have cards := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at cards
  change Q.card+D.card=Fintype.card V at cards
  change _≤(∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+Q.card+
    (∑ q∈Q,((insert q (Q.filter (G.Adj q))).image tag).card)+2*(∑ q∈Q,((D.filter (G.Adj q)).card-1)) at all
  change (∑ q∈Q,((insert q (Q.filter (G.Adj q))).image tag).card)+
    2*(∑ q∈Q,((D.filter (G.Adj q)).card-1))≤3*Q.card+D.card at slack
  omega

#print axioms three_port_palette_multi_attachment_ambient_mean_four
#print axioms multi_attachment_weighted_slack_P7free_ambient_mean_four

/-- The global collection of ports may be arbitrary: width two only along
each closed outer neighborhood suffices, regardless of multi-attachment. -/
theorem local_two_port_palette_multi_attachment_ambient_mean_four
    (h4 : FourCycleFree G) (D : Finset V)
    (attach : ∀ v∉D,∃ w∈D,G.Adj v w)
    (near : ∀ q∉D,∃ P : Finset V,P.card≤2 ∧ (∀ w∈D,G.Adj q w→w∈P) ∧
      ∀ v∉D,G.Adj q v→∀ w∈D,G.Adj v w→w∈P)
    (base : (∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)≤4*D.card) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  have qout (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  choose f fw using attach
  let tag (q : V) := if h : q∉D then f q h else q
  have pick (q : V) (qo : q∉D) : tag q∈D ∧ G.Adj q (tag q) := by simpa only [tag,dif_pos qo] using fw q qo
  have cap (q : V) (qo : q∉D) :
      localIndependence G q≤2 ∧ (D.filter (G.Adj q)).card≤2 := by
    obtain ⟨P,few,qp,adjp⟩ := near q qo
    have qsub : D.filter (G.Adj q)⊆P := fun _ m=>qp _ (Finset.mem_filter.mp m).1 (Finset.mem_filter.mp m).2
    have sub : (D.filter (G.Adj q))∪((Q.filter (G.Adj q)).image tag)⊆P := by
      apply Finset.union_subset qsub
      intro a am
      obtain ⟨v,vm,rfl⟩ := Finset.mem_image.mp am
      obtain ⟨vq,qv⟩ := Finset.mem_filter.mp vm
      exact adjp v (qout _ vq) qv _ (pick v (qout _ vq)).1 (pick v (qout _ vq)).2
    have l := outside_independence_le_core_neighbors_union_assigned_ports h4 D tag pick q qo
    exact ⟨l.trans ((Finset.card_le_card sub).trans few),(Finset.card_le_card qsub).trans few⟩
  have outer : (∑ q∈Q,localIndependence G q)≤2*Q.card := by
    calc
      _ ≤ ∑ _q∈Q,2 := Finset.sum_le_sum (fun q qm=>(cap q (qout _ qm)).1)
      _ = _ := by simp [Nat.mul_comm]
  have crosses : (∑ q∈Q,(D.filter (G.Adj q)).card)≤2*Q.card := by
    calc
      _ ≤ ∑ _q∈Q,2 := Finset.sum_le_sum (fun q qm=>(cap q (qout _ qm)).2)
      _ = _ := by simp [Nat.mul_comm]
  have all := core_and_exterior_independence_sum (G:=G) D
  have cards := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at cards
  change Q.card+D.card=Fintype.card V at cards
  change _≤(∑ x : (D : Set V),localIndependence (G.induce (D : Set V)) x)+
    (∑ q∈Q,localIndependence G q)+(∑ q∈Q,(D.filter (G.Adj q)).card) at all
  omega

#print axioms local_two_port_palette_multi_attachment_ambient_mean_four
end Graffiti133P5CliqueArms
