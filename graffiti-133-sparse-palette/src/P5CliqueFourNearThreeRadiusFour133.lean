import P5CliqueFourNearThreeArmMetric133
import P5CliqueFourNearThreeArmFans133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem P7free_connected_core_budget_near_three (D : Finset V)
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

theorem near_three_independent_singleton_palette_radius_four_mean_four
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V)
    (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (t : V) (td : t∈D) (tn : ∀ i,t≠p i)
    (indep : ∀ i j,¬G.Adj (p i) (p j))
    (near : 3≤((Finset.univ : Finset (Fin 4)).filter (fun i=>G.Adj t (p i))).card)
    (twostep : ∀ i,(G.induce (D : Set V)).dist ⟨t,td⟩ ⟨p i,pm i⟩≤2)
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ w∈D,G.Adj q w→∃ i,w=p i)
    (single : ∀ q∉D,∀ i,G.Adj q (p i)→∀ x∈D,G.Adj q x↔x=p i)
    (noP9 : NoPath G 9)
    (conn : G.Connected) (r : 4≤radius G)
    (Dconn : (G.induce (D : Set V)).Connected)
    (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  obtain ⟨Arm,ar,armD,arm0,armFar,armNe⟩ := near_three_radius_four_gives_core_arm conn r D Dconn p pm t td twostep attach
  let Q := (Finset.univ : Finset V)\D
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  let A := Q.filter (fun q=>3<localIndependence G q)
  let B (i : Fin 4) := Q.filter (fun q=>G.Adj q (p i) ∧ 3<localIndependence G q)
  let N := (Finset.univ : Finset (Fin 4)).filter (fun i=>G.Adj t (p i))
  have caps (i : Fin 4) : (B i).card≤6 := by
    have ne2 : 2≤(N.erase i).card := by
      have le := Finset.pred_card_le_card_erase (s:=N) (a:=i)
      change 3≤N.card at near
      omega
    obtain ⟨j,jm⟩ := Finset.card_pos.mp (show 0<(N.erase i).card by omega)
    have ne1 := Finset.card_erase_add_one jm
    obtain ⟨k,km⟩ := Finset.card_pos.mp (show 0<((N.erase i).erase j).card by omega)
    obtain ⟨ji,jN⟩ := Finset.mem_erase.mp jm
    obtain ⟨kj,km'⟩ := Finset.mem_erase.mp km
    obtain ⟨ki,kN⟩ := Finset.mem_erase.mp km'
    have tj : G.Adj t (p j) := (Finset.mem_filter.mp jN).2
    have tk : G.Adj t (p k) := (Finset.mem_filter.mp kN).2
    let e0 := Equiv.swap 0 i
    have e0i : e0 0=i := by simp [e0]
    let j' := e0.symm j
    have j0 : j'≠0 := fun h=>ji (by simpa [j',e0i] using congrArg e0 h)
    let e1 := Equiv.swap 2 j'
    have e1z : e1 0=0 := Equiv.swap_apply_of_ne_of_ne (by decide) (fun h=>j0 h.symm)
    have e1j : e1 2=j' := Equiv.swap_apply_left _ _
    let e01 := e1.trans e0
    have e01z : e01 0=i := by simp [e01,e1z,e0i]
    have e01j : e01 2=j := by simp [e01,e1j,j']
    let k' := e01.symm k
    have k0 : k'≠0 := fun h=>ki (by simpa [k',e01z] using congrArg e01 h)
    have k2 : k'≠2 := fun h=>kj (by simpa [k',e01j] using congrArg e01 h)
    let e2 := Equiv.swap 3 k'
    have e2z : e2 0=0 := Equiv.swap_apply_of_ne_of_ne (by decide) (fun h=>k0 h.symm)
    have e22 : e2 2=2 := Equiv.swap_apply_of_ne_of_ne (by decide) (fun h=>k2 h.symm)
    have e23 : e2 3=k' := Equiv.swap_apply_left _ _
    let e := e2.trans e01
    have e0 : e 0=i := by simp [e,e2z,e01z]
    have e2eq : e 2=j := by simp [e,e22,e01j]
    have e3eq : e 3=k := by simp [e,e23,k']
    let p' (a : Fin 4) := p (e a)
    have p0 : p' 0=p i := congrArg p e0
    have p2 : p' 2=p j := congrArg p e2eq
    have p3 : p' 3=p k := congrArg p e3eq
    have att' (q : V) (qo : q∉D) : ∃ l,G.Adj q (p' l) := by
      obtain ⟨l,hl⟩ := attach q qo
      exact ⟨e.symm l,by simpa [p'] using hl⟩
    have pal' (q : V) (qo : q∉D) (x : V) (xd : x∈D) (qx : G.Adj q x) : ∃ l,x=p' l := by
      obtain ⟨l,hl⟩ := palette q qo x xd qx
      exact ⟨e.symm l,by simpa [p'] using hl⟩
    have finfo (q : {q : V // q∈B i}) :
        ∃ fn : Fin 4→V,fn 0=q.val ∧ (∀ l,fn l∉D) ∧
          (∀ l x,x∈D→(G.Adj (fn l) x↔x=p' l)) ∧
          ∀ l m,l<m→(G.Adj (fn l) (fn m)↔l=0) := by
      obtain ⟨qQ,qi,hq⟩ := Finset.mem_filter.mp q.property
      exact high_client_singleton_four_port_has_fan h4 D p' (fun l=>pm (e l)) (pi.comp e.injective)
        att' pal' (fun q qo l=>single q qo (e l)) q.val (Finset.mem_sdiff.mp qQ).2 (p0.symm ▸ qi) hq
    choose f fc fo fp fs using finfo
    let f' (q : V) (l : Fin 4) := if h : q∈B i then f ⟨q,h⟩ l else q
    have family : PortFanFamily G (D : Set V) p' (B i) f' := by
      refine ⟨(fun l=>pm (e l)),pi.comp e.injective,?_,?_,?_,?_⟩
      · intro q qm l
        simpa only [f',dif_pos qm] using fo ⟨q,qm⟩ l
      · intro q qm
        simpa only [f',dif_pos qm] using fc ⟨q,qm⟩
      · intro q qm l x xm
        simpa only [f',dif_pos qm] using fp ⟨q,qm⟩ l x xm
      · intro q qm l m lm
        simpa only [f',dif_pos qm] using fs ⟨q,qm⟩ l m lm
    have jt : G.Adj (p' 2) t := by rw [p2]; exact tj.symm
    have tk' : G.Adj t (p' 3) := by rw [p3]; exact tk
    have ant : ¬G.Adj (p' 2) (p' 3) := indep (e 2) (e 3)
    exact six_same_port_fans_or_induced_P9 h4 family t td (fun l=>tn (e l)) jt tk' ant noP9
  have qa (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have owns (q : V) (qo : q∉D) (hi : 3<localIndependence G q) (i : Fin 4) (qi : G.Adj q (p i)) :
      p i=Arm 1 ∨ p i=Arm 2 := by
    let e := Equiv.swap 0 i
    let p' (j : Fin 4) := p (e j)
    have e0 : p' 0=p i := by simp [p',e]
    have newattach (q : V) (qo : q∉D) : ∃ j,G.Adj q (p' j) := by
      obtain ⟨k,ok⟩ := attach q qo
      exact ⟨e.symm k,by simpa [p'] using ok⟩
    have newpal (q : V) (qo : q∉D) (w : V) (wd : w∈D) (qw : G.Adj q w) : ∃ j,w=p' j := by
      obtain ⟨k,eq⟩ := palette q qo w wd qw
      exact ⟨e.symm k,by simpa [p'] using eq⟩
    have nc : ((Finset.univ : Finset (Fin 4)).filter (fun a=>G.Adj t (p' a))).card=N.card := by
      let F := (Finset.univ : Finset (Fin 4)).filter (fun a=>G.Adj t (p' a))
      have ef : F.image e=N := by
        ext a
        constructor
        · intro h
          obtain ⟨b,bm,rfl⟩ := Finset.mem_image.mp h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp bm).2⟩
        · intro h
          exact Finset.mem_image.mpr ⟨e.symm a,Finset.mem_filter.mpr
            ⟨Finset.mem_univ _,by simpa [p'] using (Finset.mem_filter.mp h).2⟩,e.apply_symm_apply a⟩
      rw [←ef,Finset.card_image_of_injective _ e.injective]
    have nc3 : 3≤((Finset.univ : Finset (Fin 4)).filter (fun a=>G.Adj t (p' a))).card := by
      rw [nc]
      exact near
    have eq := high_near_three_port_on_first_two_arm_vertices h4 D p' (fun j=>pm (e j))
      (pi.comp e.injective) t (fun j=>tn (e j)) nc3 (fun j k=>indep (e j) (e k)) newattach newpal
      (fun q qo j=>single q qo (e j)) Arm ar armD arm0 (fun j k=>armFar (e j) k)
      (fun j k=>armNe (e j) k) noP9 q qo (e0.symm ▸ qi) hi
    exact e0.symm ▸ eq
  have same (i j : Fin 4) (a : p i=Arm 1 ∨ p i=Arm 2) (b : p j=Arm 1 ∨ p j=Arm 2) :
      p i=p j := by
    have e : G.Adj (Arm 1) (Arm 2) := (ar.2 1 2 (by decide)).mpr (by decide)
    rcases a with a|a <;> rcases b with b|b
    · exact a.trans b.symm
    · exact (indep i j (a.symm ▸ (b.symm ▸ e))).elim
    · exact (indep j i (b.symm ▸ (a.symm ▸ e))).elim
    · exact a.trans b.symm
  have a6 : A.card≤6 := by
    by_cases no : A=∅
    · simp [no]
    obtain ⟨q,qm⟩ := Finset.nonempty_iff_ne_empty.mpr no
    obtain ⟨qQ,hq⟩ := Finset.mem_filter.mp qm
    obtain ⟨i,qi⟩ := attach q (qa q qQ)
    have o := owns q (qa q qQ) hq i qi
    have sub : A⊆B i := by
      intro w wm
      obtain ⟨wQ,hw⟩ := Finset.mem_filter.mp wm
      obtain ⟨j,wj⟩ := attach w (qa w wQ)
      have eq := owns w (qa w wQ) hw j wj
      exact Finset.mem_filter.mpr ⟨wQ,(same j i eq o) ▸ wj,hw⟩
    exact (Finset.card_le_card sub).trans (caps i)
  have np (j : Fin 5) (jl : 3≤j.val) : Arm j∉P := by
    intro jm
    obtain ⟨i,_,eq⟩ := Finset.mem_image.mp jm
    exact armNe i j jl eq.symm
  have ne23 : Arm 3≠Arm 4 := fun e=>(by decide : (3:Fin 5)≠4) (ar.1 e)
  have z1 := Finset.card_insert_of_not_mem (np 3 (by decide))
  have none : Arm 4∉insert (Arm 3) P := by
    intro h
    exact (Finset.mem_insert.mp h).elim (fun e=>ne23 e.symm) (np 4 (by decide))
  have z2 := Finset.card_insert_of_not_mem none
  have subD : insert (Arm 4) (insert (Arm 3) P) ⊆ D := by
    intro x xm
    rcases Finset.mem_insert.mp xm with e|xm
    · exact e.symm ▸ armD 4
    rcases Finset.mem_insert.mp xm with e|xm
    · exact e.symm ▸ armD 3
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp xm
    exact pm i
  have d6 : 6≤D.card := by
    have c := Finset.card_le_card subD
    omega
  have core := P7free_connected_core_budget_near_three D h4 Dconn h7
  choose tag htag using attach
  let f (q : V) := if h : q∉D then p (tag q h) else q
  have pick (q : V) (qo : q∉D) : f q∈D ∧ f q∈P ∧ G.Adj q (f q) := by
    have e : f q=p (tag q qo) := dif_pos qo
    rw [e]
    exact ⟨pm _,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,htag q qo⟩
  have palette' (q : V) (qo : q∉D) (w : V) (wd : w∈D) (qw : G.Adj q w) : w∈P := by
    obtain ⟨i,e⟩ := palette q qo w wd qw
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩
  have localCap (q : V) (qo : q∉D) : localIndependence G q≤4 :=
    p4 ▸ outside_independence_le_attachment_palette h4 D P f pick palette' q qo
  have outer : (∑ q∈Q,localIndependence G q)≤3*Q.card+6 := by
    have point (q : V) (qm : q∈Q) : localIndependence G q≤3+(if q∈A then 1 else 0) := by
      by_cases high : 3<localIndependence G q
      · rw [if_pos (Finset.mem_filter.mpr ⟨qm,high⟩)]
        exact localCap q (qa q qm)
      · have hA : q∉A := fun e=>high (Finset.mem_filter.mp e).2
        rw [if_neg hA]
        omega
    have ss := Finset.sum_le_sum point
    rw [Finset.sum_add_distrib] at ss
    have hsum : (∑ q∈Q,(if q∈A then 1 else 0 : Nat))=A.card := by
      rw [←Finset.card_filter]
      congr 1
      ext q
      simp only [Finset.mem_filter,A]
      tauto
    have cs : (∑ _q∈Q,(3:Nat))=3*Q.card := by simp [Nat.mul_comm]
    rw [hsum,cs] at ss
    exact ss.trans (Nat.add_le_add_left a6 _)
  have crossings : (∑ q∈Q,(D.filter (G.Adj q)).card)=Q.card := by
    calc
      _=∑ _q∈Q,1 := by
        apply Finset.sum_congr rfl
        intro q qm
        have att := htag q (qa q qm)
        have once := single q (qa q qm) _ att
        have eq : D.filter (G.Adj q)={p (tag q (qa q qm))} := by
          ext w
          constructor
          · intro wm
            obtain ⟨wd,e⟩ := Finset.mem_filter.mp wm
            exact Finset.mem_singleton.mpr ((once w wd).mp e)
          · intro wm
            obtain rfl := Finset.mem_singleton.mp wm
            exact Finset.mem_filter.mpr ⟨pm _,att⟩
        rw [eq,Finset.card_singleton]
      _=_ := by simp
  have bound := core_and_exterior_independence_sum (G:=G) D
  have cards := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  rw [Finset.card_univ] at cards
  change Q.card+D.card=Fintype.card V at cards
  change _≤_ + (∑ q∈Q,localIndependence G q) + (∑ q∈Q,(D.filter (G.Adj q)).card) at bound
  omega

#print axioms near_three_independent_singleton_palette_radius_four_mean_four
end Graffiti133P5CliqueArms
