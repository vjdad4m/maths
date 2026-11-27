import DegreeFiveFourPort189
import DegreeFiveActualCut189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
open private d2 foreign_subset from CrossSaturation189
open private side_universal_if_no_local_d2 from DegreeFiveFourPort189
open private left_boundary from AdjacentCut189
open private CutGraph Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

def CommonPorts (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (a b : V) : Finset V := G.neighborFinset a ∩ G.neighborFinset b

def Nonports (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (a b : V) : Finset V :=
  ((univ.erase a).erase b) \ (G.neighborFinset a ∪ G.neighborFinset b)

theorem degree_sum_cut_port_identity (distinct : a≠b) (no : ¬G.Adj a b) :
    G.degree a+G.degree b+(Nonports G a b).card =
      Fintype.card V-2+(CommonPorts G a b).card := by
  classical
  let P := G.neighborFinset a ∪ G.neighborFinset b
  let U := ((univ : Finset V).erase a).erase b
  have sub : P⊆U := by
    intro x hx
    have nA : x≠a := by
      intro e
      subst x
      exact (mem_union.mp hx).elim
        (fun h=>G.loopless a ((mem_neighborFinset G a a).mp h))
        (fun h=>no ((mem_neighborFinset G b a).mp h).symm)
    have nB : x≠b := by
      intro e
      subst x
      exact (mem_union.mp hx).elim (fun h=>no ((mem_neighborFinset G a b).mp h))
        (fun h=>G.loopless b ((mem_neighborFinset G b b).mp h))
    exact mem_erase.mpr ⟨nB,mem_erase.mpr ⟨nA,mem_univ _⟩⟩
  have count : U.card=Fintype.card V-2 := by
    dsimp [U]
    rw [card_erase_of_mem (mem_erase.mpr ⟨distinct.symm,mem_univ _⟩),
      card_erase_of_mem (mem_univ _),card_univ]
    omega
  have sums := card_sdiff_add_card_eq_card sub
  change (Nonports G a b).card+P.card=U.card at sums
  rw [count] at sums
  have e := card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
  rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at e
  change P.card+(CommonPorts G a b).card=_ at e
  omega

theorem degree_sum_threshold_iff_at_unique_common (two : G.dist a b=2)
    (one : (CommonPorts G a b).card=1) :
    Fintype.card V-2≤G.degree a+G.degree b ↔ (Nonports G a b).card≤1 := by
  have dis : a≠b := by intro h; rw [h,SimpleGraph.dist_self] at two; omega
  have no : ¬G.Adj a b := by intro h; have := dist_eq_one_iff_adj.mpr h; omega
  have e := degree_sum_cut_port_identity dis no
  omega

namespace Split.Five

private theorem opposite_ports_at_exclusive_le_four (S : Split G a b) (hc : G.Connected)
    (even : ∀ x,(EvenFrom G x).card≤6)
    {u : V} (uL : u∈S.L) (au : G.Adj a u) (bno : ¬G.Adj b u) :
    S.foreignA.card≤4 := by
  classical
  have other : ∃ z, z∈DistanceTwo G u ∧ (z=b ∨ z∈S.L) := by
    by_cases side : ∃ z∈S.L,z∈DistanceTwo G u
    · obtain ⟨z,zL,z2⟩ := side
      exact ⟨z,z2,.inr zL⟩
    obtain ⟨w,wL,bw⟩ := S.leftB
    have universal := side_universal_if_no_local_d2 S hc uL
      (fun z zl z2=>side ⟨z,zl,z2⟩) w wL
    rcases universal with e|uw
    · exact (bno (e ▸ bw)).elim
    have ub : u≠b := fun e=>S.leftOff.2 (e ▸ uL)
    exact ⟨b,d2 hc ub (fun e=>bno e.symm) uw bw.symm,.inl rfl⟩
  obtain ⟨z,z2,side⟩ := other
  have off : z∉S.foreignA := by
    intro zp
    have zr := (mem_filter.mp zp).1
    rcases side with rfl|zl
    · exact S.rightOff.2 zr
    exact disjoint_left.mp S.dis zl zr
  have sub : insert z S.foreignA ⊆ DistanceTwo G u := by
    intro x hx
    rcases mem_insert.mp hx with rfl|xp
    · exact z2
    exact foreign_subset S hc uL au xp
  have c := card_le_card sub
  rw [card_insert_of_not_mem off] at c
  have cap := distanceTwo_le_of_even 5 u (even u)
  omega

/-- Under the original graph's parity bound, the unique-common-port
version of the degree-sum edge-closure test only arises up to order 15. -/
theorem order_le_fifteen_of_unique_common_closure_test (S : Split G a b)
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (rightConn : (G.induce (↑S.R : Set V)).Connected)
    (rightA : ∃ u∈S.R,G.Adj a u) (rightB : ∃ u∈S.R,G.Adj b u)
    {x : V} (xL : x∈S.L) (ax : G.Adj a x) (bx : G.Adj b x)
    (one : (CommonPorts G a b).card=1)
    (test : Fintype.card V-2≤G.degree a+G.degree b) :
    Fintype.card V≤15 := by
  classical
  let T := switch S rightConn rightA rightB
  have no : ¬G.Adj a b := by intro h; have := dist_eq_one_iff_adj.mpr h; omega
  have commonEq : CommonPorts G a b={x} := by
    symm
    apply eq_of_subset_of_card_le
    · intro z hz
      have e := mem_singleton.mp hz
      subst z
      exact mem_inter.mpr ⟨(mem_neighborFinset G a x).mpr ax,(mem_neighborFinset G b x).mpr bx⟩
    simp [one]
  have noCommonR {u : V} (ur : u∈S.R) (au : G.Adj a u) (bu : G.Adj b u) : False := by
    have j : u∈CommonPorts G a b :=
      mem_inter.mpr ⟨(mem_neighborFinset G a u).mpr au,(mem_neighborFinset G b u).mpr bu⟩
    rw [commonEq] at j
    exact disjoint_left.mp S.dis xL (mem_singleton.mp j ▸ ur)
  obtain ⟨u,uR,au⟩ := rightA
  obtain ⟨v,vR,bv⟩ := rightB
  have LA := opposite_ports_at_exclusive_le_four T hc even uR au (noCommonR uR au)
  have LB := opposite_ports_at_exclusive_le_four T.flip hc even
    vR bv (fun av=>noCommonR vR av bv)
  let A := S.L.filter (G.Adj a)
  let B := S.L.filter (G.Adj b)
  change A.card≤4 at LA
  change B.card≤4 at LB
  have intersection : 1≤(A∩B).card := card_pos.mpr ⟨x,
    mem_inter.mpr ⟨mem_filter.mpr ⟨xL,ax⟩,mem_filter.mpr ⟨xL,bx⟩⟩⟩
  have leftCap : (A∪B).card≤7 := by have h := card_union_add_card_inter A B; omega
  have foreign : S.foreignPorts ⊆ DistanceTwo G x := by
    intro y yp
    obtain ⟨yr,p⟩ := mem_filter.mp yp
    have ne : x≠y := fun e=>disjoint_left.mp S.dis xL (e.symm ▸ yr)
    have na := S.cross x xL y yr
    exact p.elim (fun ay=>d2 hc ne na ax.symm ay) (fun by'=>d2 hc ne na bx.symm by')
  have rightCap := (card_le_card foreign).trans (distanceTwo_le_of_even 5 x (even x))
  have all : G.neighborFinset a ∪ G.neighborFinset b ⊆ (A∪B)∪S.foreignPorts := by
    intro z zp
    have h : G.Adj a z ∨ G.Adj b z := (mem_union.mp zp).imp
      ((mem_neighborFinset G a z).mp) ((mem_neighborFinset G b z).mp)
    rcases S.cover z with rfl|rfl|zl|zr
    · exact h.elim (fun e=> (G.loopless _ e).elim) (fun e=>(no e.symm).elim)
    · exact h.elim (fun e=>(no e).elim) (fun e=>(G.loopless _ e).elim)
    · exact mem_union_left _ (h.elim (fun e=>mem_union_left _ (mem_filter.mpr ⟨zl,e⟩))
        (fun e=>mem_union_right _ (mem_filter.mpr ⟨zl,e⟩)))
    exact mem_union_right _ (mem_filter.mpr ⟨zr,h⟩)
  have bound := (card_le_card all).trans (card_union_le (A∪B) S.foreignPorts)
  have sum := card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
  rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at sum
  change _+(CommonPorts G a b).card=_ at sum
  omega

#print axioms degree_sum_threshold_iff_at_unique_common
#print axioms order_le_fifteen_of_unique_common_closure_test
end Split.Five
end Graffiti189LongestPath.CrossSaturation

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph Finset
open private CutGraph Shore mem_shore shore_off shore_disjoint shore_closed shore_connected
  shore_hit_a shore_hit_b from DegreeFiveActualCut189
open private two_walk_middle from DistanceTwoCut189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem order_le_fifteen_of_actual_unique_common_closure_test {a b : V}
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (conn : ∀ R : Finset V,R.card<2 → (G.induce ((↑R : Set V)ᶜ)).Connected)
    (comp : Nat.card (CutGraph (G:=G) a b).ConnectedComponent=2)
    (one : (CommonPorts G a b).card=1)
    (test : Fintype.card V-2≤G.degree a+G.degree b) :
    Fintype.card V≤15 := by
  classical
  let J := CutGraph (G:=G) a b
  haveI : Finite J.ConnectedComponent := Finite.of_surjective J.connectedComponentMk (fun c=>c.exists_rep)
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  change Nat.card J.ConnectedComponent=2 at comp
  rw [Nat.card_eq_fintype_card] at comp
  have ab : a≠b := by intro eq; rw [eq,SimpleGraph.dist_self] at two; omega
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist a b
  obtain ⟨x,ax,xb⟩ := two_walk_middle p (pl.trans two)
  let C := J.connectedComponentMk ⟨x,ax.ne.symm,xb.ne⟩
  have xC : x∈Shore C := mem_shore.mpr ⟨⟨ax.ne.symm,xb.ne⟩,rfl⟩
  let T := (univ : Finset J.ConnectedComponent).erase C
  have tc : T.card=1 := by
    dsimp [T]
    rw [card_erase_of_mem (mem_univ _),card_univ,comp]
  obtain ⟨D,hD⟩ := card_eq_one.mp tc
  have dt : D∈T := by simp [hD]
  have DC : D≠C := (mem_erase.mp dt).1
  have dis : Disjoint (Shore C) (Shore D) := shore_disjoint DC.symm
  have cover (u : V) : u=a ∨ u=b ∨ u∈Shore C ∨ u∈Shore D := by
    by_cases ua : u=a
    · exact .inl ua
    by_cases ub : u=b
    · exact .inr (.inl ub)
    let E := J.connectedComponentMk ⟨u,ua,ub⟩
    have eu : u∈Shore E := mem_shore.mpr ⟨⟨ua,ub⟩,rfl⟩
    by_cases ec : E=C
    · exact .inr (.inr (.inl (ec ▸ eu)))
    have et : E∈T := mem_erase.mpr ⟨ec,mem_univ _⟩
    rw [hD] at et
    exact .inr (.inr (.inr (mem_singleton.mp et ▸ eu)))
  have cross (u : V) (uC : u∈Shore C) (v : V) (vD : v∈Shore D) : ¬G.Adj u v := by
    intro uv
    rcases shore_closed C u uC v uv with rfl|rfl|vC
    · exact (shore_off D).1 vD
    · exact (shore_off D).2 vD
    exact disjoint_left.mp dis vC vD
  let S : Split G a b :=
    ⟨Shore C,Shore D,dis,shore_off C,shore_off D,shore_connected C,cross,
      shore_hit_a ab conn C,shore_hit_b ab conn C,cover⟩
  exact Split.Five.order_le_fifteen_of_unique_common_closure_test S hc two even
    (shore_connected D) (shore_hit_a ab conn D) (shore_hit_b ab conn D)
    xC ax xb.symm one test

#print axioms order_le_fifteen_of_actual_unique_common_closure_test
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
