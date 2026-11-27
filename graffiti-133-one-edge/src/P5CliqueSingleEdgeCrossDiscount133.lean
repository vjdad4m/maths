import P5CliqueMultiPortBudget133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem extra_port_incidence_le_erase_unrealized_pair
    (h4 : FourCycleFree G) (D P : Finset V) (sub : P⊆D) (tag : V→V)
    (choosePort : ∀ v∉D,tag v∈P ∧ G.Adj v (tag v))
    (palette : ∀ v∉D,∀ w∈D,G.Adj v w→w∈P)
    (a b : V) (no : ∀ q∉D,¬(G.Adj q a ∧ G.Adj q b)) :
    let Q := (Finset.univ : Finset V)\D
    (∑ q∈Q,((D.filter (G.Adj q)).card-1))≤((P.powersetCard 2).erase {a,b}).card := by
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
  let Allowed := (P.powersetCard 2).erase {a,b}
  let map : {p : V×V // p∈Pair} → {F : Finset V // F∈Allowed} := fun q=>
    ⟨{tag q.val.1,q.val.2},Finset.mem_erase.mpr ⟨by
      intro eq
      have only (x : V) (xm : x∈({tag q.val.1,q.val.2}:Finset V)) : G.Adj q.val.1 x := by
        rcases Finset.mem_insert.mp xm with h|h
        · exact h.symm ▸ (choosePort q.val.1 (qout _ (info q).1)).2
        · exact (Finset.mem_singleton.mp h).symm ▸ (info q).2.2.1
      refine no q.val.1 (qout _ (info q).1) ⟨only a ?_,only b ?_⟩
      · rw [eq]; simp
      · rw [eq]; simp
      ,Finset.mem_powersetCard.mpr ⟨by
      intro a am
      rcases Finset.mem_insert.mp am with e|e
      · exact e.symm ▸ (choosePort q.val.1 (qout _ (info q).1)).1
      · exact (Finset.mem_singleton.mp e).symm ▸
          palette q.val.1 (qout _ (info q).1) q.val.2 (info q).2.1 (info q).2.2.1,by
      have ne := (info q).2.2.2
      simp [ne.symm]⟩⟩⟩
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

theorem core_local_triangle_crossing_discount
    (h4 : FourCycleFree G) (D : Finset V) (v c : (D : Set V)) (u : V) (uo : u∉D)
    (vc : G.Adj v.val c.val) (vu : G.Adj v.val u) (cu : G.Adj c.val u) :
    localIndependence G v.val + 1 ≤ localIndependence (G.induce (D : Set V)) v +
      (((Finset.univ : Finset V)\D).filter (G.Adj v.val)).card := by
  classical
  let J := G.induce (D : Set V)
  let X := (((Finset.univ : Finset V)\D).filter (G.Adj v.val))
  have ux : u∈X := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,uo⟩,vu⟩
  have xp : 0<X.card := Finset.card_pos.mpr ⟨u,ux⟩
  change localIndependence G v.val + 1 ≤ localIndependence J v + X.card
  suffices small : localIndependence G v.val ≤ localIndependence J v + X.card-1 by omega
  unfold localIndependence
  apply Finset.sup_le_iff.mpr
  intro S sM
  have hS : (∀ x∈S,G.Adj v.val x) ∧ (∀ x∈S,∀ y∈S,¬G.Adj x y) := by
    simpa only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,
      Finset.mem_univ,true_and] using sM
  let T := S.subtype (fun x=>x∈D)
  have tM : T∈localIndependentSets (G.induce (D : Set V)) v := by
    simp only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,
      Finset.mem_univ,true_and]
    exact ⟨fun x hx=>hS.1 x.val (Finset.mem_subtype.mp hx),
      fun x hx y hy=>hS.2 x.val (Finset.mem_subtype.mp hx) y.val (Finset.mem_subtype.mp hy)⟩
  have le := Finset.le_sup (f:=Finset.card) tM
  rw [show T.card=(S.filter (fun x=>x∈D)).card from Finset.card_subtype _ _] at le
  have ssub : S.filter (fun x=>x∉D)⊆((Finset.univ\D).filter (G.Adj v.val)) := by
    intro x hx
    obtain ⟨xs,xd⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,xd⟩,hS.1 x xs⟩
  have lt := Finset.card_le_card ssub
  have eq := Finset.filter_card_add_filter_neg_card_eq_card (s:=S) (fun x=>x∈D)
  change S.card≤localIndependence J v+X.card-1
  change (S.filter (fun x=>x∈D)).card≤localIndependence J v at le
  change (S.filter (fun x=>x∉D)).card≤X.card at lt
  by_cases us : u∈S
  · have cm : c∉T := by
      intro cs
      exact hS.2 c.val (Finset.mem_subtype.mp cs) u us cu
    have more : insert c T∈localIndependentSets J v := by
      simp only [localIndependentSets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_iff,
        Finset.mem_univ,true_and]
      have only (x : (D : Set V)) (xm : x∈T) : ¬G.Adj c.val x.val := by
        intro cx
        have e := h4 v.val c.val x.val u vc.ne (hS.1 _ (Finset.mem_subtype.mp xm)) cx vu cu
        exact uo (e ▸ x.property)
      refine ⟨?_,?_⟩
      · intro x xm
        rcases Finset.mem_insert.mp xm with e|t
        · exact e.symm ▸ vc
        · exact hS.1 x.val (Finset.mem_subtype.mp t)
      · intro x xm y ym
        rcases Finset.mem_insert.mp xm with xe|xt <;> rcases Finset.mem_insert.mp ym with ye|yt
        · subst x; subst y; exact G.loopless _
        · exact xe.symm ▸ only y yt
        · exact ye.symm ▸ fun e=>only x xt e.symm
        · exact hS.2 _ (Finset.mem_subtype.mp xt) _ (Finset.mem_subtype.mp yt)
    have extra := Finset.le_sup (f:=Finset.card) more
    rw [Finset.card_insert_of_not_mem cm,Finset.card_subtype] at extra
    change (S.filter (fun x=>x∈D)).card+1≤localIndependence J v at extra
    have bound : S.card+1≤localIndependence J v+X.card := by omega
    omega
  have small : S.filter (fun x=>x∉D)⊆X.erase u := by
    intro y ym
    refine Finset.mem_erase.mpr ⟨?_,ssub ym⟩
    intro e
    exact us (e ▸ (Finset.mem_filter.mp ym).1)
  have sz := Finset.card_le_card small
  have ee := Finset.card_erase_add_one ux
  have bound : S.card+1≤localIndependence J v+X.card := by omega
  omega

#print axioms extra_port_incidence_le_erase_unrealized_pair
#print axioms core_local_triangle_crossing_discount
theorem core_and_exterior_triangle_discount_sum
    (h4 : FourCycleFree G) (D : Finset V) (b c : (D : Set V))
    (u : V) (uo : u∉D) (bc : G.Adj b.val c.val) (bu : G.Adj b.val u) (cu : G.Adj c.val u) :
    let Q := (Finset.univ : Finset V)\D
    (∑ v : V,localIndependence G v)+1≤
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
  have core : (∑ x∈D,localIndependence G x)+1≤
      (∑ x : (D : Set V),localIndependence J x)+(∑ x∈D,deg x) := by
    have point (x : (D : Set V)) : localIndependence G x.val+(if x=b then 1 else 0)≤
        localIndependence J x+deg x.val := by
      by_cases eq : x=b
      · subst x
        rw [if_pos rfl]
        exact core_local_triangle_crossing_discount h4 D b c u uo bc bu cu
      · rw [if_neg eq,Nat.add_zero]
        exact core_localIndependence_le_add_outer_degree D x
    have le := Finset.sum_le_sum (fun (x : (D : Set V)) (_ : x∈Finset.univ)=>point x)
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at le
    have ind : (∑ x : (D : Set V),(if x=b then 1 else 0 : Nat))=1 := by simp
    have l : (∑ x : (D : Set V),localIndependence G x.val)=∑ x∈D,localIndependence G x :=
      (Finset.sum_subtype (p:=fun x=>x∈D) D (fun _=>Iff.rfl) (localIndependence G)).symm
    have r : (∑ x : (D : Set V),deg x.val)=∑ x∈D,deg x :=
      (Finset.sum_subtype (p:=fun x=>x∈D) D (fun _=>Iff.rfl) deg).symm
    rwa [ind,l,r] at le
  have eq := Finset.sum_sdiff (Finset.subset_univ D) (f:=localIndependence G)
  change (∑ q∈Q,localIndependence G q)+(∑ x∈D,localIndependence G x)=(∑ v : V,localIndependence G v) at eq
  change (∑ v : V,localIndependence G v)+1≤(∑ x : (D : Set V),localIndependence J x)+(∑ q∈Q,localIndependence G q)+(∑ q∈Q,(D.filter (G.Adj q)).card)
  omega

#print axioms core_and_exterior_triangle_discount_sum
end Graffiti133P5CliqueArms
