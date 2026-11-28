import SixSingletonQ1Exception189
import SixSingletonQ1Sparse1Actual189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair Graffiti189Ore PortCertificates
open private walk_of_chain from ArticulationClique189
open private Cmp from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark Common strictA strictB from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b s z : V} {D : Cmp G a b}
set_option linter.unusedSectionVars false
set_option maxHeartbeats 14000000

private theorem route_of_list (x : V) (L : List V) (h : (x::L).Chain' G.Adj)
    (n : (x::L).Nodup) : ∃ y,RouteOn G (x::L).toFinset x y := by
  obtain ⟨y,p,ph⟩ := walk_of_chain x L h
  refine ⟨y,p,IsPath.mk' (ph.symm ▸ n),?_⟩
  intro w
  rw [ph,List.mem_toFinset]

theorem q1_exception_traceable (F : SixVisibleData G D s) (P : Q1PortBoard D s 1)
    (n : Fintype.card V=16) (bal : nearBal D={z})
    (ea : (EA D).card≤2) (eb : (EB D).card≤2)
    (v6 : (Vis D).card=6) (l2 : (strictA D).card=2) (r4 : (strictB D).card=4)
    (bad : Q1Sparse1.Bad (Q1Sparse1Actual.bits (G:=G) (fun i : Fin 6=>P.label (widenQ1 (by decide : 6≤9) i)) z)) :
    Traceable G := by
  classical
  let f (i : Fin 6) := P.label (widenQ1 (by decide : 6≤9) i)
  let J := (Dark D).erase z
  let tag := addQ1 P.label z
  obtain ⟨ext,inj⟩ := q1_exterior_coverage F n P.label P.aEq P.bEq P.sEq P.portImage
  obtain ⟨ext10,inj10⟩ := q1_exterior_add_balance F bal P.label ext inj
  have fi : Function.Injective f := inj.comp (widenQ1_injective (by decide : 6≤9))
  have fvis (i : Fin 6) : f i∈Vis D := P.portImage ▸ mem_image.mpr ⟨i,mem_univ _,rfl⟩
  have fy : f 1∈EB D := P.right 1 (by decide) (by decide)
  have fy' : f 2∈EB D := P.right 2 (by decide) (by decide)
  have c2 : f 5∈Common D := P.common 5 (by decide)
  obtain ⟨x01,x02,x03,_,_,x12,x13,x14,x15,x23,x24,x25,x34,_,x45⟩ := bad
  have no1 : ∀ i : Fin 6, ¬G.Adj (f 1) (f i) := by
    intro i
    fin_cases i
    · exact fun h=>of_decide_eq_false x01 h.symm
    · exact G.loopless _
    · exact of_decide_eq_false x12
    · exact of_decide_eq_false x13
    · exact of_decide_eq_false x14
    exact of_decide_eq_false x15
  have no2 : ∀ i : Fin 6, ¬G.Adj (f 2) (f i) := by
    intro i
    fin_cases i
    · exact fun h=>of_decide_eq_false x02 h.symm
    · exact fun h=>of_decide_eq_false x12 h.symm
    · exact G.loopless _
    · exact of_decide_eq_false x23
    · exact of_decide_eq_false x24
    exact of_decide_eq_false x25
  have iso (i : Fin 6) (h : ∀ j,¬G.Adj (f i) (f j)) : inside G (Vis D) (f i)=∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro w hw
    have ⟨wv,wa⟩ := mem_filter.mp hw
    rw [←P.portImage] at wv
    obtain ⟨j,_,rfl⟩ := mem_image.mp wv
    exact h j wa
  have rne : (strictB D).Nonempty := card_pos.mp (by omega)
  obtain ⟨u,ur,v,vr,core⟩ := q1_right_pair_route F bal ea eb l2 rne
  have link1 := q1_exception_right_links F bal r4 fy (iso 1 no1) u ur
  have link2 := q1_exception_right_links F bal r4 fy' (iso 2 no2) v vr
  have cz := q1_exception_common_link F bal v6 c2 (fvis 5) (fvis 1) (fvis 2)
    (fun h=> (by decide : (5:Fin 6)≠1) (fi h))
    (fun h=> (by decide : (5:Fin 6)≠2) (fi h))
    (fun h=> (by decide : (1:Fin 6)≠2) (fi h))
    (fun h=>no1 5 h.symm) (fun h=>no2 5 h.symm)
  have yd : f 1∉J := by
    intro j
    exact (mem_sdiff.mp (mem_erase.mp j).2).2 (fvis 1)
  have disj : Disjoint ({f 1}:Finset V) J := by simpa using yd
  have frontRoute := (RouteOn.singleton (G:=G) (x:=f 1)).join core disj link1
  let L : List (Fin 10) := [2,7,8,6,0,3,4,5,9]
  have cl : (L.map tag).Chain' G.Adj := by
    change List.Chain' G.Adj [f 2,P.label 7,P.label 8,P.label 6,f 0,f 3,f 4,f 5,z]
    rw [P.bEq,P.sEq,P.aEq]
    repeat' apply List.Chain'.cons
    all_goals first | exact (F.eB _ fy').1.symm | exact F.sb.symm | exact F.sa |
      exact (F.eA _ (P.left 0 (by decide))).1 | exact of_decide_eq_true x03 |
      exact of_decide_eq_true x34 | exact of_decide_eq_true x45 | exact cz | exact List.chain'_singleton _
  have nd : (L.map tag).Nodup := (show L.Nodup by decide).map inj10
  obtain ⟨t,tail⟩ := route_of_list (tag 2) ([7,8,6,0,3,4,5,9].map tag) cl nd
  have exterior : (L.map tag).toFinset = (univ\J).erase (f 1) := by
    rw [←ext10]
    ext w
    rw [List.mem_toFinset,List.mem_map,mem_erase,mem_image]
    simp only [mem_univ,true_and]
    constructor
    · rintro ⟨i,hi,rfl⟩
      refine ⟨?_,⟨i,rfl⟩⟩
      intro e
      have ei : i=1 := inj10 e
      subst i
      exact (by decide : (1:Fin 10)∉L) hi
    rintro ⟨hne,i,rfl⟩
    refine ⟨i,?_,rfl⟩
    have m : ∀ i : Fin 10,i≠1 → i∈L := by decide
    exact m i (fun h=>hne (h ▸ rfl))
  have eq : (univ\J).erase (f 1) = univ\(({f 1}:Finset V)∪J) := by
    ext w
    simp only [mem_erase,mem_sdiff,mem_univ,true_and,mem_union,mem_singleton,not_or]
  change RouteOn G (L.map tag).toFinset (f 2) t at tail
  rw [exterior,eq] at tail
  exact splice_route_to_complement frontRoute tail link2.symm

#print axioms q1_exception_traceable
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
