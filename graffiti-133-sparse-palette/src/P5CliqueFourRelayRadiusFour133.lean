import P5CliqueFourRelayArmMetric133
import P5CliqueFourRelayArmFans133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem P7free_connected_core_budget_relay (D : Finset V)
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

theorem common_relay_palette_radius_four_mean_four
    (h4 : FourCycleFree G) (D : Finset V) (p : Fin 4→V)
    (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (t : V) (td : t∈D) (relay : ∀ i,G.Adj t (p i))
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ w∈D,G.Adj q w→∃ i,w=p i)
    (noP9 : NoPath G 9)
    (conn : G.Connected) (r : 4≤radius G)
    (Dconn : (G.induce (D : Set V)).Connected)
    (h7 : NoPath (G.induce (D : Set V)) 7) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  obtain ⟨Arm,ar,armD,arm0,armFar⟩ := common_relay_radius_four_gives_core_arm conn r D Dconn p pm t td relay attach
  let Q := (Finset.univ : Finset V)\D
  let P := (Finset.univ : Finset (Fin 4)).image p
  have p4 : P.card=4 := by rw [Finset.card_image_of_injective _ pi,Finset.card_univ]; decide
  let A := Q.filter (fun q=>3<localIndependence G q)
  let B (i : Fin 4) := Q.filter (fun q=>G.Adj q (p i) ∧ 3<localIndependence G q)
  have caps (i : Fin 4) : (B i).card≤6 := by
    let swap0 := Equiv.swap 0 i
    have noBoth (adj : G.Adj (p (swap0 2)) (p (swap0 3))) :
        ¬G.Adj (p (swap0 1)) (p (swap0 3)) := by
      intro bad
      have eq := h4 t (p (swap0 3)) (p (swap0 2)) (p (swap0 1))
        (relay (swap0 3)).ne (relay (swap0 2)) adj.symm (relay (swap0 1)) bad.symm
      exact (by decide : (2:Fin 4)≠1) (swap0.injective (pi eq))
    let s := if G.Adj (p (swap0 2)) (p (swap0 3)) then Equiv.swap (1:Fin 4) 2 else Equiv.refl (Fin 4)
    let e := s.trans swap0
    have s0 : s 0=0 := by
      by_cases adj : G.Adj (p (swap0 2)) (p (swap0 3)) <;> simp [s,adj,Equiv.swap_apply_of_ne_of_ne]
    have far : ¬G.Adj (p (e 2)) (p (e 3)) := by
      by_cases adj : G.Adj (p (swap0 2)) (p (swap0 3))
      · simpa [e,s,adj,Equiv.swap_apply_of_ne_of_ne] using noBoth adj
      · simp [e,s,adj]
    let p' (j : Fin 4) := p (e j)
    have e0 : p' 0=p i := by simp [p',e,s0,swap0]
    have newattach (q : V) (qo : q∉D) : ∃ j,G.Adj q (p' j) := by
      obtain ⟨k,ok⟩ := attach q qo
      exact ⟨e.symm k,by simpa [p'] using ok⟩
    have newpal (q : V) (qo : q∉D) (w : V) (wd : w∈D) (qw : G.Adj q w) : ∃ j,w=p' j := by
      obtain ⟨k,eq⟩ := palette q qo w wd qw
      exact ⟨e.symm k,by simpa [p'] using eq⟩
    have exact := high_clients_at_one_relay_port_at_most_six h4 D p' (fun j=>pm (e j))
      (pi.comp e.injective) t td (fun j=>relay (e j)) far newattach newpal noP9
    simpa only [B,Q,e0] using exact
  have qa (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have owns (q : V) (qo : q∉D) (hi : 3<localIndependence G q) (i : Fin 4) (qi : G.Adj q (p i)) :
      p i=Arm 1 := by
    let e := Equiv.swap 0 i
    let p' (j : Fin 4) := p (e j)
    have e0 : p' 0=p i := by simp [p',e]
    have newattach (q : V) (qo : q∉D) : ∃ j,G.Adj q (p' j) := by
      obtain ⟨k,ok⟩ := attach q qo
      exact ⟨e.symm k,by simpa [p'] using ok⟩
    have newpal (q : V) (qo : q∉D) (w : V) (wd : w∈D) (qw : G.Adj q w) : ∃ j,w=p' j := by
      obtain ⟨k,eq⟩ := palette q qo w wd qw
      exact ⟨e.symm k,by simpa [p'] using eq⟩
    have eq := high_relay_fan_port_eq_first_arm_vertex h4 D p' (fun j=>pm (e j))
      (pi.comp e.injective) t td (fun j=>relay (e j))
      newattach newpal Arm ar armD arm0 (fun j k=>armFar (e j) k) noP9 q qo (e0.symm ▸ qi) hi
    exact e0.symm ▸ eq
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
      exact Finset.mem_filter.mpr ⟨wQ,(eq.trans o.symm) ▸ wj,hw⟩
    exact (Finset.card_le_card sub).trans (caps i)
  have np (j : Fin 5) (jl : 2≤j.val) : Arm j∉P := by
    intro jm
    obtain ⟨i,_,eq⟩ := Finset.mem_image.mp jm
    have adj : G.Adj (Arm 0) (Arm j) := arm0.symm ▸ (eq ▸ relay i)
    have oj : (0:Fin 5)<j := by
      change 0<j.val
      omega
    have close := (ar.2 0 j oj).mp adj
    change 0+1=j.val at close
    omega
  have ne23 : Arm 2≠Arm 3 := fun e=>(by decide : (2:Fin 5)≠3) (ar.1 e)
  have z1 := Finset.card_insert_of_not_mem (np 2 (by decide))
  have none : Arm 3∉insert (Arm 2) P := by
    intro h
    exact (Finset.mem_insert.mp h).elim (fun e=>ne23 e.symm) (np 3 (by decide))
  have z2 := Finset.card_insert_of_not_mem none
  have subD : insert (Arm 3) (insert (Arm 2) P) ⊆ D := by
    intro x xm
    rcases Finset.mem_insert.mp xm with e|xm
    · exact e.symm ▸ armD 3
    rcases Finset.mem_insert.mp xm with e|xm
    · exact e.symm ▸ armD 2
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp xm
    exact pm i
  have d6 : 6≤D.card := by
    have c := Finset.card_le_card subD
    omega
  have core := P7free_connected_core_budget_relay D h4 Dconn h7
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
        have once := common_relay_forces_singleton_attachment h4 D p t td relay palette q (qa q qm) _ att
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

#print axioms common_relay_palette_radius_four_mean_four
end Graffiti133P5CliqueArms
