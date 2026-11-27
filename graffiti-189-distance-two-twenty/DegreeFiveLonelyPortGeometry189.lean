import DegreeFiveActualCut189
import DegreeFiveDistanceTwoThreeClose189
import DegreeFiveThreeForeignImpossible189
import DegreeFiveExclusiveGateway189

namespace Graffiti189LongestPath.CrossSaturation.FiveActualCut
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private CutGraph Shore shore_off shore_disjoint shore_closed shore_connected
  from DegreeFiveActualCut189
open private secondShore anywhere_high_of_two from DegreeFiveDistanceTwoThreeClose189
open private Cmp portColor two_shore_budget foreign_exclusive_subset_at_port
  universal_if_no_own_second from DegreeFiveThreeForeignImpossible189
open private boundary_permuted nonport_is_low_on_small_shore walk_three_data
  from DegreeFiveExclusiveGateway189
open private d2 from CrossSaturation189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V}
set_option linter.unusedSectionVars false

theorem lonely_high_port_geometry
    (hc : G.Connected) (two : G.dist a b=2) (even : ∀ x,(EvenFrom G x).card≤6)
    (degree : ∀ u v : V,u≠v → 5≤G.degree u ∨ 5≤G.degree v)
    {C D : Cmp (G:=G) (a:=a) (b:=b)} (cd : C≠D)
    {c d u : V} (perm : (c=a ∧ d=b) ∨ (c=b ∧ d=a))
    (uD : u∈Shore D) (cu : G.Adj c u) (du : ¬G.Adj d u) (u5 : 5≤G.degree u)
    (one : (portColor D c).card=1) (four : (portColor C c).card=4)
    (p3 : (cutPorts D).card≤3) :
    ∃ q∈Shore D, (inside G (Shore D) u).card=4 ∧ secondShore D u={q} ∧
      (∀ z∈Shore D,G.Adj d z → ¬G.Adj u z) ∧
      (∀ t∈inside G (Shore D) u, 5≤G.degree t →
        G.Adj t q ∧ ∀ z∈inside G (Shore D) u,z≠t → G.Adj t z) ∧
      (∀ z∈Shore D,z≠u → ¬ G.Adj u z → z≠q → G.Adj q z) := by
  classical
  let O := Shore D
  let N := inside G O u
  let Q := secondShore D u
  let F := portColor C c
  have ct : c=a ∨ c=b := perm.elim (fun e=>.inl e.1) (fun e=>.inr e.1)
  have cOff : c∉Shore C ∧ c∉O := by
    rcases perm with ⟨rfl,_⟩|⟨rfl,_⟩
    · exact ⟨(shore_off C).1,(shore_off D).1⟩
    exact ⟨(shore_off C).2,(shore_off D).2⟩
  have dOff : d∉Shore C ∧ d∉O := by
    rcases perm with ⟨_,rfl⟩|⟨_,rfl⟩
    · exact ⟨(shore_off C).2,(shore_off D).2⟩
    exact ⟨(shore_off C).1,(shore_off D).1⟩
  have dist : G.dist c d=2 := by
    rcases perm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact two
    rwa [SimpleGraph.dist_comm]
  have cdNo : ¬G.Adj c d := by intro h; have := dist_eq_one_iff_adj.mpr h; omega
  have onlyC (z : V) (zl : z∈O) (cz : G.Adj c z) : z=u := by
    have h : z∈portColor D c := mem_filter.mpr ⟨zl,cz⟩
    exact card_le_one.mp one.le z h u (mem_filter.mpr ⟨uD,cu⟩)
  have N4 : N.card=4 := by
    have d := two_shore_budget cd dOff dist even
    have sub : N⊆secondShore D c := by
      intro z zn
      obtain ⟨zl,uz⟩ := mem_filter.mp zn
      have ne : c≠z := fun e=>cOff.2 (e.symm ▸ zl)
      exact mem_inter.mpr ⟨zl,d2 hc ne (fun e=>uz.ne.symm (onlyC z zl e)) cu uz⟩
    have l := card_le_card sub
    have nc : G.neighborFinset u⊆insert c N := by
      intro z hz
      have uz := (mem_neighborFinset G u z).mp hz
      rcases boundary_permuted perm u uD z uz with rfl|rfl|zl
      · exact mem_insert_self _ _
      · exact (du uz.symm).elim
      exact mem_insert_of_mem (mem_filter.mpr ⟨zl,uz⟩)
    have r := (card_le_card nc).trans (card_insert_le c N)
    rw [card_neighborFinset_eq_degree] at r
    omega
  have foreign : F⊆DistanceTwo G u := foreign_exclusive_subset_at_port hc cd ct uD cu
  have qf : Disjoint Q F := (shore_disjoint cd.symm).mono inter_subset_left (filter_subset _ _)
  have sub : Q∪F⊆DistanceTwo G u := union_subset inter_subset_right foreign
  have s := card_le_card sub
  rw [card_union_of_disjoint qf] at s
  change F.card=4 at four
  have budget := distanceTwo_le_of_even 5 u (even u)
  have Q1 : Q.card≤1 := by omega
  have noB {z : V} (zl : z∈O) (dz : G.Adj d z) : ¬G.Adj u z := by
    intro uz
    have h := d2 hc (show u≠d from fun e=>dOff.2 (e ▸ uD)) (fun e=>du e.symm) uz dz.symm
    have off : d∉Q∪F := by
      intro e
      exact (mem_union.mp e).elim (fun e=>dOff.2 (mem_inter.mp e).1)
        (fun e=>dOff.1 (mem_filter.mp e).1)
    have s' : insert d (Q∪F)⊆DistanceTwo G u := by
      intro z hz
      exact (mem_insert.mp hz).elim (fun e=>e.symm ▸ h) (fun e=>sub e)
    have s1 := card_le_card s'
    rw [card_insert_of_not_mem off,card_union_of_disjoint qf] at s1
    have all := universal_if_no_own_second hc uD (by change Q.card=0; omega)
    have sub' : O⊆insert u N := by
      intro z zs
      exact (all z zs).elim (fun e=>mem_insert.mpr (.inl e))
        (fun e=>mem_insert_of_mem (mem_filter.mpr ⟨zs,e⟩))
    have le5 := (card_le_card sub').trans (card_insert_le u N)
    have uN : u∉N := fun e=>G.loopless u (mem_filter.mp e).2
    have five : O.card=5 := by
      have n := card_le_card (show insert u N⊆O from fun _ h=>
        (mem_insert.mp h).elim (fun e=>e.symm ▸ uD) (fun e=>(mem_filter.mp e).1))
      rw [card_insert_of_not_mem uN,N4] at n
      omega
    let I := O \ cutPorts D
    have psub : cutPorts D⊆O := filter_subset _ _
    have c := card_sdiff_add_card_eq_card psub
    change I.card+(cutPorts D).card=O.card at c
    obtain ⟨x,xI,y,yI,xy⟩ := one_lt_card.mp (show 1<I.card by omega)
    have lo (t : V) (tt : t∈I) : ¬5≤G.degree t := by
      obtain ⟨tD,tOff⟩ := mem_sdiff.mp tt
      exact nonport_is_low_on_small_shore five.le tD
        (fun e=>tOff (mem_filter.mpr ⟨tD,.inl e⟩))
        (fun e=>tOff (mem_filter.mpr ⟨tD,.inr e⟩))
    exact (degree x y xy).elim (lo x xI) (lo y yI)
  obtain ⟨t,tN,t5⟩ := anywhere_high_of_two degree (show 2≤N.card by omega)
  have allSub (t : V) (tN : t∈N) :
      G.neighborFinset t⊆insert u (N.erase t∪Q) := by
    obtain ⟨tO,ut⟩ := mem_filter.mp tN
    have tc : ¬G.Adj c t := fun e=>ut.ne.symm (onlyC t tO e)
    have td : ¬G.Adj d t := fun e=>noB tO e ut
    intro z hz
    have tz := (mem_neighborFinset G t z).mp hz
    rcases boundary_permuted perm t tO z tz with rfl|rfl|zo
    · exact (tc tz.symm).elim
    · exact (td tz.symm).elim
    by_cases zu : z=u
    · exact mem_insert.mpr (.inl zu)
    apply mem_insert_of_mem
    by_cases uz : G.Adj u z
    · exact mem_union_left _ (mem_erase.mpr ⟨tz.ne.symm,mem_filter.mpr ⟨zo,uz⟩⟩)
    exact mem_union_right _ (mem_inter.mpr ⟨zo,d2 hc (Ne.symm zu) uz ut tz⟩)
  let Z := insert u (N.erase t∪Q)
  have tsub : G.neighborFinset t⊆Z := allSub t tN
  have zCap := card_insert_le u (N.erase t∪Q)
  change Z.card≤_ at zCap
  have zCap' := card_union_le (N.erase t) Q
  rw [card_erase_of_mem tN] at zCap'
  have zCount := card_le_card tsub
  rw [card_neighborFinset_eq_degree] at zCount
  have Qeq1 : Q.card=1 := by omega
  obtain ⟨w,wEq⟩ := card_eq_one.mp Qeq1
  have wQ : w∈Q := by simp [wEq]
  have uRad (z : V) : G.dist u z≤3 := by
    apply Classical.byContradiction
    intro no
    have far : 4≤G.dist u z := by omega
    have lo := distanceTwo_add_two_le_even_of_far hc far
    have b := even u
    omega
  let H := insert u (N∪Q)
  let J := O \ H
  have far (z : V) (zj : z∈J) : G.Adj w z := by
    obtain ⟨zo,nH⟩ := mem_sdiff.mp zj
    have ne : u≠z := fun e=>nH (mem_insert.mpr (.inl e.symm))
    have nu : ¬G.Adj u z := fun e=>nH
      (mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨zo,e⟩)))
    have n2 : z∉DistanceTwo G u := fun e=>nH
      (mem_insert_of_mem (mem_union_right _ (mem_inter.mpr ⟨zo,e⟩)))
    have ge := hc.one_lt_dist_of_ne_of_not_adj ne nu
    have hi := uRad z
    have d3 : G.dist u z=3 := by
      by_cases h : G.dist u z=2
      · exact (n2 (by simp [DistanceTwo,h])).elim
      omega
    obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist u z
    obtain ⟨i,j,ui,ij,jz⟩ := walk_three_data p (pl.trans d3)
    have io : i∈O := by
      rcases boundary_permuted perm u uD i ui with rfl|rfl|io
      · rcases boundary_permuted perm z zo j jz.symm with rfl|rfl|jo
        · exact (G.loopless _ ij).elim
        · exact (cdNo ij).elim
        have ju := onlyC j jo ij
        exact (nu (ju ▸ jz)).elim
      · exact (du ui.symm).elim
      exact io
    have jo : j∈O := by
      rcases boundary_permuted perm i io j ij with rfl|rfl|jO
      · exact (ne (onlyC z zo jz).symm).elim
      · exact (noB io ij.symm ui).elim
      exact jO
    have uj : ¬G.Adj u j := by
      intro e
      have l := G.dist_le (Walk.cons e (Walk.cons jz .nil))
      simp at l
      omega
    have ujne : u≠j := fun e=>nu (e.symm ▸ jz)
    have jq : j∈Q := mem_inter.mpr ⟨jo,d2 hc ujne uj ui ij⟩
    have jw : j=w := by simpa [wEq] using jq
    exact jw ▸ jz
  refine ⟨w,(mem_inter.mp wQ).1,N4,wEq,fun z zl dz=>noB zl dz,?_,?_⟩
  · intro v vN v5
    have vc := allSub v vN
    have bp := card_insert_le u (N.erase v∪Q)
    have bq := card_union_le (N.erase v) Q
    have erased : (N.erase v).card=3 := by rw [card_erase_of_mem vN,N4]
    rw [erased,Qeq1] at bq
    have bp' : (insert u (N.erase v∪Q)).card≤5 :=
      bp.trans (Nat.add_le_add_right bq 1)
    have eq := eq_of_subset_of_card_le vc (by
      rw [card_neighborFinset_eq_degree]
      exact bp'.trans v5)
    refine ⟨(mem_neighborFinset G v w).mp
      (eq.symm ▸ mem_insert_of_mem (mem_union_right _ wQ)),?_⟩
    intro z zN zv
    exact (mem_neighborFinset G v z).mp
      (eq.symm ▸ mem_insert_of_mem (mem_union_left _ (mem_erase.mpr ⟨zv,zN⟩)))
  intro z zD zu no zw
  apply far z
  refine mem_sdiff.mpr ⟨zD,?_⟩
  intro hz
  rcases mem_insert.mp hz with rfl|h
  · exact zu rfl
  rcases mem_union.mp h with zN|zQ
  · exact no (mem_filter.mp zN).2
  exact zw (by simpa [wEq] using zQ)

#print axioms lonely_high_port_geometry
end Graffiti189LongestPath.CrossSaturation.FiveActualCut
