import DeficitShore189
import DeficitDonors189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack Graffiti189LongestPath.PinRun
open Graffiti189LongestPath.DeficitActive Graffiti189LongestPath.DeficitLongest
open Graffiti189LongestPath.DeficitShore Graffiti189LongestPath.DeficitThirdShell
open Graffiti189LongestPath.DeficitDonors Graffiti189LongestPath.ActiveStarHeight
open private Graffiti189LongestPath.Rigidity.mem_omittedStar Graffiti189LongestPath.Rigidity.mem_external from Rigidity189
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.boundary_except_pins_two Graffiti189LongestPath.OneSlack.card_pinVertices
  Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary from OneSlack189
set_option warningAsError true
set_option maxHeartbeats 7000000
namespace Graffiti189LongestPath.DeficitThree
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- #189 for connectivity at least d−3 and degree threshold d≥403.
No normalized attachment or separator geometry is assumed. -/
theorem traceable_of_connectivity_d_minus_three (hc : G.Connected) (k : Nat) (hk : 400≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+4)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+3≤G.degree u ∨ k+3≤G.degree v) :
    ∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ z,z∈q.support := by
  classical
  apply Classical.byContradiction
  intro fail
  obtain ⟨a,b,p,hp⟩ := Rigidity.exists_longest hc
  have no : ∃ x,x∉p.support := Classical.byContradiction (fun h =>
    fail ⟨a,b,p,hp.1,fun z => Classical.byContradiction (fun e => h ⟨z,e⟩)⟩)
  obtain ⟨x,hx,xh,i,hi⟩ := deficit_three_has_high_active hc k (by omega) cap conn deg hp no
  let d := k+3
  let A := OmittedStar p x
  let B := External G A
  let P := PinVertices p x
  let C := B\P
  let H := Shell G x 3
  let W := Shell G x 4
  let U := (univ:Finset V)\(A∪B)
  have cap₂ (v : V) : (DistanceTwo G v).card≤d := distanceTwo_le_of_even d v (cap v)
  have pack := high_omitted_pin_budget hc d k cap conn hp hx (Graffiti189LongestPath.pin_data hi).2 xh
  have p3 : (Pins p x).card≤3 := by dsimp [d] at pack; omega
  have w3 : W.card≤3 := by change k+(Pins p x).card+W.card≤d at pack; dsimp [d] at pack; omega
  have rad (z : V) : G.dist x z≤4 := by
    by_contra! far
    have c := shell_card_of_far hc k conn (x:=x) (y:=z) (i:=4) (by decide) (by omega)
    change k≤W.card at c
    omega
  have height : k+1≤A.card := by
    have e := star_card_degree_and_pins hp hx
    change A.card+(Pins p x).card=G.degree x+1 at e
    omega
  have cc : C.card≤d := (card_le_card
    (Graffiti189LongestPath.OneSlack.boundary_except_pins_two hc hp hx)).trans (cap₂ x)
  have pp : P.card≤3 := by
    have e := Graffiti189LongestPath.OneSlack.card_pinVertices hp (x:=x)
    change P.card=(Pins p x).card at e
    omega
  have bc : C.card+P.card=B.card :=
    card_sdiff_add_card_eq_card (Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary hx)
  have bk : B.card≤k+6 := by dsimp [d] at cc; omega
  have floor (z : V) : 2≤G.degree z := by
    have ne : a≠x := fun e => hx (e ▸ p.start_mem_support)
    have n := enough_vertices_of_degree (k+3) deg ne
    have kdeg := degree_floor_when_enough_vertices k conn (by omega) z
    omega
  have largeP := longest_length_ge_twice_of_not_traceable hc d (by omega) floor deg fail hp
  have far : k≤U.card := by
    have cover : p.support.toFinset⊆B∪U := by
      intro z hz
      by_cases zb : z∈B
      · exact mem_union.mpr (Or.inl zb)
      have za : z∉A := fun e => (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp e).1 (List.mem_toFinset.mp hz)
      exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨mem_univ z,fun e => (mem_union.mp e).elim za zb⟩))
    have h := (card_le_card cover).trans (card_union_le B U)
    rw [List.toFinset_card_of_nodup hp.1.support_nodup,length_support] at h
    dsimp [d] at largeP
    omega
  have order := order_le_star_cut_two_three_four hc hx rad
  change Fintype.card V≤A.card+B.card+(DistanceTwo G x).card+H.card+W.card at order
  have base : Fintype.card V≤A.card+2*k+12+H.card := by
    have cx := cap₂ x
    dsimp [d] at cx
    omega
  have bd : Fintype.card V<A.card+k+(k+1)*(A.card-10) := by
    by_cases small : A.card≤k+30
    · have fl := fun v => six_defect_induced_floor hc k (by omega) cap conn hp hx bk far v
      have hs := donor_shell_upper hc k hk cap₂ hp hx p3 fl small
      change H.card≤(k-27)*d ∨ H.card≤d*(d-80)+3*d at hs
      have hs' : H.card≤(k-27)*d := by
        rcases hs with h|h
        · exact h
        have id : d*(d-80)+3*d=(d-80+3)*d := by
          calc
            d*(d-80)+3*d = (d-80)*d+3*d := by rw [Nat.mul_comm d (d-80)]
            _ = _ := (Nat.add_mul (d-80) 3 d).symm
        rw [id] at h
        exact h.trans (Nat.mul_le_mul_right d (by dsimp [d]; omega))
      have gear := Nat.mul_le_mul_left (k+1) (show k-9≤A.card-10 by omega)
      have l : (k+1)*(k-9)+9*(k+1)=(k+1)*k := by
        rw [Nat.mul_comm 9,←Nat.mul_add,show k-9+9=k by omega]
      have u : (k-27)*d+27*d=k*d := by rw [←Nat.add_mul,show k-27+27=k by omega]
      have i : (k+1)*k=k*k+k := by rw [Nat.add_mul,one_mul]
      have j : k*d=k*k+3*k := by dsimp [d]; rw [Nat.mul_add,Nat.mul_comm k 3]
      have j₁ : 27*d=27*k+81 := by simp [d,Nat.mul_add]
      have j₂ : 9*(k+1)=9*k+9 := by rw [Nat.mul_add,Nat.mul_one]
      omega
    · have xa : x∈A := Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
      have gate (v : V) : ∃ u,u∈A ∧ (v∈C → G.Adj u v) := by
        by_cases h : v∈C
        · obtain ⟨_,u,ua,e⟩ := Graffiti189LongestPath.Rigidity.mem_external.mp (mem_sdiff.mp h).1
          exact ⟨u,ua,fun _ => e⟩
        · exact ⟨x,xa,fun q => (h q).elim⟩
      choose f ff using gate
      have fa (v : V) (vc : v∈C) : f v∈A ∧ G.Adj (f v) v := ⟨(ff v).1,(ff v).2 vc⟩
      let D := C.image f
      let HD := D.biUnion (gateThird G x C)
      let HP := P.biUnion (fun t => H∩DistanceTwo G t)
      have cov : H⊆HD∪HP := shell_three_donor_cover hc hp hx f fa
      have each (v : V) (vd : v∈D) : (gateThird G x C v).card≤d := by
        obtain ⟨u,uc,rfl⟩ := mem_image.mp vd
        exact (card_le_card (gate_third_subset hc (fa u uc).1 C)).trans (cap₂ _)
      have co : HD.card≤D.card*d := card_biUnion_le_card_mul D _ d each
      have pin : HP.card≤P.card*d := card_biUnion_le_card_mul P _ d
        (fun v _ => (card_le_card inter_subset_right).trans (cap₂ v))
      have dc : D.card≤C.card := card_image_le
      have e := (card_le_card cov).trans (card_union_le HD HP)
      have u := Nat.mul_le_mul_right d (show D.card+P.card≤k+6 by omega)
      rw [Nat.add_mul] at u
      have b := Nat.mul_le_mul_left (k+1) (show k+20≤A.card-10 by omega)
      have j : (k+6)*d=k*k+9*k+18 := by
        dsimp [d]
        rw [Nat.add_mul,Nat.mul_add,Nat.mul_add,Nat.mul_comm k 3]
        omega
      have l : (k+1)*(k+20)=k*k+21*k+20 := by
        rw [Nat.add_mul,one_mul,Nat.mul_add,Nat.mul_comm k 20]
        omega
      omega
  obtain ⟨z,c,cyc,cl⟩ := six_defect_root_deleted_long_cycle hc k (by omega) cap conn hp hx bk far height deg
  have len : A.card-11+1=A.card-10 := by omega
  have lim : Fintype.card V<A.card+k+(k+1)*(A.card-11+1) := by rwa [len]
  change 2*((A.card-10)/2)≤c.length at cl
  exact six_defect_no_long_shore_cycle hc k (by omega) cap conn hp hx bk far (show 24<A.card by omega)
    (A.card-11) (show k≤A.card by omega) lim ⟨z,c,cyc,by omega⟩

#print axioms traceable_of_connectivity_d_minus_three
end Graffiti189LongestPath.DeficitThree
