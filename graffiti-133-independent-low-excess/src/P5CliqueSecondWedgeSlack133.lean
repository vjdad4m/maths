import P5CliqueWedgeSlack133
import Mathlib.Data.Finset.Powerset

namespace Graffiti133P5CliqueArms.SecondWedge
open SimpleGraph Finset Graffiti133 Graffiti133ExteriorSlack
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def pairSet : Sym2 V → Finset V :=
  Sym2.lift ⟨fun a b=>{a,b},fun a b=>by ext x; simp [or_comm]⟩

private theorem edgeCard_eq_twoCliques : G.edgeFinset.card=(G.cliqueFinset 2).card := by
  classical
  apply Finset.card_bij (fun e _=>pairSet e)
  · intro e em
    induction e using Sym2.ind with
    | h a b =>
      have ad : G.Adj a b := SimpleGraph.mem_edgeFinset.mp em
      apply SimpleGraph.mem_cliqueFinset_iff.mpr
      refine ⟨?_,by simp [pairSet,ad.ne]⟩
      simp only [pairSet,Sym2.lift_mk,Finset.coe_insert,Finset.coe_singleton]
      exact SimpleGraph.isClique_pair.mpr (fun _=>ad)
  · intro e em f fm eq
    induction e using Sym2.ind with
    | h a b =>
      induction f using Sym2.ind with
      | h c d =>
        have ab : a≠b := (show G.Adj a b from SimpleGraph.mem_edgeFinset.mp em).ne
        have cd : c≠d := (show G.Adj c d from SimpleGraph.mem_edgeFinset.mp fm).ne
        change ({a,b} : Finset V)={c,d} at eq
        have ca : c∈({a,b} : Finset V) := eq.symm ▸ (Finset.mem_insert_self _ _)
        have da : d∈({a,b} : Finset V) := eq.symm ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        simp only [Finset.mem_insert,Finset.mem_singleton] at ca da
        apply Sym2.eq_iff.mpr
        rcases ca with e|e <;> rcases da with d'|d'
        · exact (cd (e.trans d'.symm)).elim
        · exact Or.inl ⟨e.symm,d'.symm⟩
        · exact Or.inr ⟨d'.symm,e.symm⟩
        · exact (cd (e.trans d'.symm)).elim
  · intro S sm
    obtain ⟨hc,cc⟩ := SimpleGraph.mem_cliqueFinset_iff.mp sm
    obtain ⟨a,b,ab,rfl⟩ := Finset.card_eq_two.mp cc
    have hc' : G.IsClique ({a,b}:Set V) := by simpa only [Finset.coe_insert,Finset.coe_singleton] using hc
    have ad := SimpleGraph.isClique_pair.mp hc' ab
    exact ⟨Sym2.mk (a,b),SimpleGraph.mem_edgeFinset.mpr ad,rfl⟩

private theorem paired_neighbors_card (v : V) :
    ((G.neighborFinset v).powersetCard 2).card=(G.degree v).choose 2 := by
  rw [Finset.card_powersetCard,G.card_neighborFinset_eq_degree]

private theorem adjacent_neighbor_pair_card (v : V) :
    (((G.neighborFinset v).powersetCard 2).filter (fun (P : Finset V)=>G.IsClique (P : Set V))).card =
      triangleIncidence G v := by
  classical
  unfold triangleIncidence
  apply Finset.card_bij (fun P _=>insert v P)
  · intro P pm
    obtain ⟨shape,cl⟩ := Finset.mem_filter.mp pm
    obtain ⟨sub,pc⟩ := Finset.mem_powersetCard.mp shape
    have nv : v∉P := fun m=>G.loopless v ((G.mem_neighborFinset _ _).mp (sub m))
    refine Finset.mem_filter.mpr ⟨SimpleGraph.mem_cliqueFinset_iff.mpr ⟨?_,?_⟩,Finset.mem_insert_self _ _⟩
    · rw [Finset.coe_insert,SimpleGraph.isClique_insert]
      exact ⟨cl,fun b bm _=>(G.mem_neighborFinset _ _).mp (sub bm)⟩
    · rw [Finset.card_insert_of_not_mem nv,pc]
  · intro A am B bm eq
    have away (T : Finset V) (tm : T∈((G.neighborFinset v).powersetCard 2).filter (fun (P : Finset V)=>G.IsClique (P:Set V))) : v∉T :=
      fun m=>G.loopless v ((G.mem_neighborFinset _ _).mp ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp tm).1).1 m))
    have e := congrArg (fun T : Finset V=>T.erase v) eq
    simpa only [Finset.erase_insert (away A am),Finset.erase_insert (away B bm)] using e
  · intro T tm
    obtain ⟨tc,vt⟩ := Finset.mem_filter.mp tm
    obtain ⟨cl,cc⟩ := SimpleGraph.mem_cliqueFinset_iff.mp tc
    refine ⟨T.erase v,Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_,?_⟩,?_⟩,Finset.insert_erase vt⟩
    · intro x xm
      obtain ⟨xv,xt⟩ := Finset.mem_erase.mp xm
      exact (G.mem_neighborFinset _ _).mpr (cl vt xt xv.symm)
    · rw [Finset.card_erase_of_mem vt,cc]
    · intro a am b bm ne
      exact cl (Finset.erase_subset v T am) (Finset.erase_subset v T bm) ne

private noncomputable def nonedgeWedges (v : V) : Finset (Finset V) := by
  classical
  exact ((G.neighborFinset v).powersetCard 2).filter (fun (P : Finset V)=>¬G.IsClique (P : Set V))

private noncomputable def ambientNonedges : Finset (Finset V) := by
  classical
  exact ((Finset.univ : Finset V).powersetCard 2).filter (fun (P : Finset V)=>¬G.IsClique (P : Set V))

private theorem ambientNonedges_add_edges : (ambientNonedges G).card+G.edgeFinset.card=(Fintype.card V).choose 2 := by
  classical
  let F := (Finset.univ : Finset V).powersetCard 2
  have e : F.filter (fun (P : Finset V)=>G.IsClique (P:Set V))=G.cliqueFinset 2 := by
    ext P
    simp [F,SimpleGraph.mem_cliqueFinset_iff,SimpleGraph.isNClique_iff,and_comm]
  rw [edgeCard_eq_twoCliques,←e]
  change (F.filter (fun (P : Finset V)=>¬G.IsClique (P:Set V))).card+_=_
  rw [Nat.add_comm,Finset.filter_card_add_filter_neg_card_eq_card,Finset.card_powersetCard,Finset.card_univ]

private theorem nonedgeWedges_card (v : V) :
    (nonedgeWedges G v).card+triangleIncidence G v=(G.degree v).choose 2 := by
  classical
  rw [←adjacent_neighbor_pair_card,←paired_neighbors_card G v]
  unfold nonedgeWedges
  rw [Nat.add_comm]
  exact Finset.filter_card_add_filter_neg_card_eq_card (s:=(G.neighborFinset v).powersetCard 2) (fun (P : Finset V)=>G.IsClique (P:Set V))

private theorem nonedgeWedges_disjoint (h4 : FourCycleFree G) :
    ((Finset.univ : Finset V) : Set V).PairwiseDisjoint (nonedgeWedges G) := by
  classical
  intro v _ w _ ne
  apply Finset.disjoint_left.mpr
  intro S vm wm
  obtain ⟨vs,vs2⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp vm).1
  obtain ⟨ws,_⟩ := Finset.mem_powersetCard.mp (Finset.mem_filter.mp wm).1
  obtain ⟨a,b,ab,rfl⟩ := Finset.card_eq_two.mp vs2
  have am : a∈({a,b} : Finset V) := Finset.mem_insert_self _ _
  have bm : b∈({a,b} : Finset V) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact ab (h4 v w a b ne ((G.mem_neighborFinset _ _).mp (vs am)) ((G.mem_neighborFinset _ _).mp (ws am))
    ((G.mem_neighborFinset _ _).mp (vs bm)) ((G.mem_neighborFinset _ _).mp (ws bm)))

private theorem nonedgeWedges_sub_ambient :
    Finset.univ.biUnion (nonedgeWedges G)⊆ambientNonedges G := by
  classical
  intro P pm
  obtain ⟨v,_,vm⟩ := Finset.mem_biUnion.mp pm
  obtain ⟨form,no⟩ := Finset.mem_filter.mp vm
  obtain ⟨_,pc⟩ := Finset.mem_powersetCard.mp form
  exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,pc⟩,no⟩

private theorem wedgeBudget (h4 : FourCycleFree G) :
    (∑ v : V,(G.degree v).choose 2)+G.edgeFinset.card ≤
      (Fintype.card V).choose 2 + 3*triangleCount G := by
  classical
  have sub := nonedgeWedges_sub_ambient G
  have b := Finset.card_le_card sub
  rw [Finset.card_biUnion (nonedgeWedges_disjoint G h4)] at b
  have sum := Finset.sum_congr rfl (fun v (_ : v∈(Finset.univ : Finset V))=>nonedgeWedges_card G v)
  rw [Finset.sum_add_distrib,sum_incidence] at sum
  have eq := ambientNonedges_add_edges G
  omega

private theorem choose_degree_lower_three (d : Nat) : 3*d≤d.choose 2+6 := by
  have H (k : Nat) : 3*(k+3)≤(k+3).choose 2+6 := by
    induction k with
    | zero=>decide
    | succ k ih=>
      have e : (k+3+1).choose 2=(k+3)+(k+3).choose 2 := by
        rw [Nat.choose_succ_succ,Nat.choose_one_right]
      change 3*(k+3+1)≤(k+3+1).choose 2+6
      omega
  rcases d with _|_|_|d
  · decide
  · decide
  · decide
  exact H d

theorem local_sum_second_wedge_upper (h4 : FourCycleFree G) :
    (∑ v : V,localIndependence G v)+5*G.edgeFinset.card≤
      (Fintype.card V).choose 2+6*Fintype.card V := by
  classical
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun v (_ : v∈(Finset.univ : Finset V))=>
    choose_degree_lower_three (G.degree v))
  have constant : (∑ _v : V,(6:Nat))=6*Fintype.card V := by simp [Nat.mul_comm]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,G.sum_degrees_eq_twice_card_edges,constant] at sum
  have wedge := wedgeBudget G h4
  have e := Graffiti133ExactTriangleCharge.sum_degree_eq_local_add_triangles (G:=G) h4
  omega

theorem order_eleven_below_three_twelve_signed_slack (h11 : Fintype.card V=11)
    (h4 : FourCycleFree G) (h : (∑ v : V,localIndependence G v)≤33) :
    (∑ v : V,localIndependence G v)+12≤4*Fintype.card V := by
  have w := local_sum_second_wedge_upper G h4
  have e := Graffiti133ExactTriangleCharge.sum_degree_eq_local_add_triangles (G:=G) h4
  rw [h11,show Nat.choose 11 2=55 by decide] at w
  rw [h11]
  by_cases lo : G.edgeFinset.card≤16
  · omega
  by_cases seventeen : G.edgeFinset.card=17
  · have one : 1≤triangleCount G := by omega
    omega
  omega

theorem order_ten_with_unrepresented_nonedge_twelve_signed_slack
    (h10 : Fintype.card V=10) (h4 : FourCycleFree G)
    (a b : V) (ab : a≠b) (nonedge : ¬G.Adj a b)
    (unrepresented : ¬∃ c,G.Adj a c ∧ G.Adj b c) :
    (∑ v : V,localIndependence G v)+12≤4*Fintype.card V := by
  have w := Graffiti133P5CliqueArms.local_sum_wedge_upper G h4
  have e := Graffiti133ExactTriangleCharge.sum_degree_eq_local_add_triangles (G:=G) h4
  have low : (∑ v : V,localIndependence G v)≤29 := by
    by_contra no
    exact unrepresented
      (Graffiti133P5CliqueArms.order_ten_exact_three_nonedge_common_neighbor G h10 h4 (by omega) a b ab nonedge)
  rw [h10,show Nat.choose 10 2=45 by decide] at w
  rw [h10]
  by_cases lo : G.edgeFinset.card≤14
  · omega
  by_cases hi : 16≤G.edgeFinset.card
  · omega
  have t : G.edgeFinset.card=15 := by omega
  have r : 1≤triangleCount G := by omega
  omega

#print axioms local_sum_second_wedge_upper
#print axioms order_eleven_below_three_twelve_signed_slack
#print axioms order_ten_with_unrepresented_nonedge_twelve_signed_slack

end Graffiti133P5CliqueArms.SecondWedge
