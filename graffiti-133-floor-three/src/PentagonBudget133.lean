import PentagonStructure133

namespace Graffiti133Pentagon
namespace PentagonFrame
open SimpleGraph Graffiti133 Graffiti133Revisit Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : PentagonFrame G)

noncomputable def singleSite (i : Fin 5) : Finset V := by
  classical
  exact univ.filter (fun x => One G F.c x i)

private lemma site_mem {i : Fin 5} {x : V} :
    x ∈ F.singleSite i ↔ One G F.c x i := by
  classical
  simp [singleSite]

private lemma pent_neighbors : ∀ i j : Fin 5, pent i j ↔ j = i+1 ∨ j = i+4 := by decide
private lemma pent_ne : ∀ i j : Fin 5, pent i j → i ≠ j := by decide

private def CSeat (y : V) (j : Fin 5) : Prop :=
  y = F.c j ∨ (Outside F.c y ∧ G.Adj y (F.c j))

private theorem seat_for_non_single {i : Fin 5} {y : V} (ha : G.Adj (F.c i) y)
    (no : y ∉ F.singleSite i) : ∃ j, pent i j ∧ F.CSeat y j := by
  classical
  by_cases h : Outside F.c y
  · rcases F.classify_contact y h with ⟨j,hj⟩ | ⟨j,hj⟩
    · have e := (hj.2 i).mp ha.symm
      exact (no ((F.site_mem).mpr (e.symm ▸ hj))).elim
    · rcases (hj.2 i).mp ha.symm with eq | eq
      · exact ⟨j+1,Or.inl (by rw [eq]),Or.inr ⟨h,(hj.2 _).mpr (Or.inr rfl)⟩⟩
      · exact ⟨j,Or.inr eq.symm,Or.inr ⟨h,(hj.2 _).mpr (Or.inl rfl)⟩⟩
  · obtain ⟨j,hj⟩ : ∃ j, y = F.c j := by
      apply Classical.byContradiction
      intro hh
      exact h fun j e => hh ⟨j,e⟩
    exact ⟨j,(F.adj _ _).mp (hj ▸ ha),Or.inl hj⟩

private theorem cSeat_inj {i j : Fin 5} {y z : V}
    (hij : pent i j) (hy : G.Adj (F.c i) y) (hz : G.Adj (F.c i) z)
    (e : ¬G.Adj y z) (sy : F.CSeat y j) (sz : F.CSeat z j) :
    y = z := by
  rcases sy with sy | ⟨hoy,hyt⟩ <;> rcases sz with sz | ⟨hoz,hzt⟩
  · exact sy.trans sz.symm
  · exact (e (sy.symm ▸ hzt.symm)).elim
  · exact (e (sz.symm ▸ hyt)).elim
  · exact F.h4 (F.c i) (F.c j) y z (fun h => pent_ne i j hij (F.inj h))
      hy hyt.symm hz hzt.symm

/-- In a local independent set at a cycle vertex, each non-singleton neighbor
can occupy one of only two seats, indexed by the adjacent cycle vertices. -/
theorem local_cycle_bound (i : Fin 5) :
    localIndependence G (F.c i) ≤ 2 + (F.singleSite i).card := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  obtain ⟨hN,hI⟩ := memLocalSet.mp hA
  let B := A \ F.singleSite i
  have haveLabel (y : V) (hy : y ∈ B) : ∃ j, pent i j ∧ F.CSeat y j :=
    F.seat_for_non_single (hN y (Finset.mem_sdiff.mp hy).1) (Finset.mem_sdiff.mp hy).2
  let rho (y : V) : Fin 5 := if hy : y ∈ B then Classical.choose (haveLabel y hy) else i
  have labels (y : V) (hy : y ∈ B) : pent i (rho y) ∧ F.CSeat y (rho y) := by
    rw [show rho y = Classical.choose (haveLabel y hy) from dif_pos hy]
    exact Classical.choose_spec (haveLabel y hy)
  have hinj : Set.InjOn rho (↑B : Set V) := by
    intro y hy z hz he
    exact F.cSeat_inj (labels y hy).1
      (hN _ (Finset.mem_sdiff.mp hy).1) (hN _ (Finset.mem_sdiff.mp hz).1)
      (hI _ (Finset.mem_sdiff.mp hy).1 _ (Finset.mem_sdiff.mp hz).1)
      (labels y hy).2 (he.symm ▸ (labels z hz).2)
  have hcard : B.card ≤ 2 := by
    let T : Finset (Fin 5) := {i+1,i+4}
    have c : B.card ≤ T.card := Finset.card_le_card_of_injOn rho
      (fun y hy => by simpa [T] using (pent_neighbors _ _).mp (labels y hy).1) hinj
    exact c.trans ((Finset.card_insert_le _ _).trans (by simp))
  have hB : B.card + (A ∩ F.singleSite i).card = A.card := Finset.card_sdiff_add_card_inter A (F.singleSite i)
  have hI := Finset.card_le_card (show A ∩ F.singleSite i ⊆ F.singleSite i from Finset.inter_subset_right)
  omega

noncomputable def allSingles : Finset V := by
  classical
  exact Finset.univ.filter fun x => ∃ i, One G F.c x i

noncomputable def allHigh : Finset V := by
  classical
  exact F.allSingles.filter fun x => 3 ≤ localIndependence G x

noncomputable def index (x : V) : Fin 5 := by
  classical
  exact if h : ∃ i, One G F.c x i then Classical.choose h else 0

private lemma mem_singles {x : V} : x ∈ F.allSingles ↔ ∃ i, One G F.c x i := by
  classical
  simp [allSingles]

private lemma index_valid {x : V} (hx : x ∈ F.allSingles) : One G F.c x (F.index x) := by
  classical
  have h := F.mem_singles.mp hx
  unfold index
  rw [dif_pos h]
  exact Classical.choose_spec h

private lemma same_single_site {x : V} {i j : Fin 5}
    (hi : One G F.c x i) (hj : One G F.c x j) : i = j :=
  (hj.2 _).mp ((hi.2 _).mpr rfl)

private lemma site_filter (i : Fin 5) :
    F.singleSite i = F.allSingles.filter (fun x => F.index x = i) := by
  classical
  ext x
  rw [F.site_mem,Finset.mem_filter]
  refine ⟨?_,fun ⟨h,he⟩ => he ▸ F.index_valid h⟩
  intro h
  have hx := F.mem_singles.mpr ⟨i,h⟩
  exact ⟨hx,F.same_single_site (F.index_valid hx) h⟩

private lemma allSites_sum :
    (∑ i : Fin 5, (F.singleSite i).card) = F.allSingles.card := by
  classical
  simpa only [F.site_filter] using
    (Finset.card_eq_sum_card_fiberwise (s:=F.allSingles) (t:=Finset.univ)
      (f:=F.index) (fun _ _ => Finset.mem_univ _)).symm

private lemma mem_high {x : V} :
    x ∈ F.allHigh ↔ x ∈ F.allSingles ∧ 3 ≤ localIndependence G x := by
  classical simp [allHigh]

private lemma high_inj : Set.InjOn F.index (↑F.allHigh : Set V) := by
  intro x hx y hy he
  obtain ⟨hxs,hxd⟩ := F.mem_high.mp hx
  obtain ⟨hys,hyd⟩ := F.mem_high.mp hy
  have sx := F.index_valid hxs
  have sy := he.symm ▸ F.index_valid hys
  obtain ⟨⟨u,hu,eu,uOne⟩,_⟩ := F.high_unique_opposite sx hxd
  obtain ⟨w,z,hw,hz,ew,ez⟩ := F.high_opposite sy hyd
  have eq := uOne w hw
  have hY : G.Adj y u := eq ▸ ew
  let j := F.index x
  have ne : j+2 ≠ j := (by decide : ∀ i : Fin 5, i+2≠i) j
  have hux := (hu.2 _).mpr rfl
  have ec : G.Adj x (F.c (F.index x)) := (sx.2 _).mpr rfl
  have ec' : G.Adj y (F.c (F.index x)) := (sy.2 _).mpr rfl
  exact F.h4 u (F.c j) x y (hu.1 j) eu.symm ec.symm hY.symm ec'.symm

private lemma high_le_five : F.allHigh.card ≤ 5 := by
  classical
  have h := Finset.card_le_card_of_injOn F.index (fun _ _ => Finset.mem_univ _)
    F.high_inj
  simpa using h

private noncomputable def charge (x : V) : ℕ := by
  classical
  exact ∑ i : Fin 5, if x = F.c i then (F.singleSite i).card else 0

private lemma charge_sum : (∑ x : V, F.charge x) = F.allSingles.card := by
  classical
  unfold charge
  rw [Finset.sum_comm]
  simp [F.allSites_sum]

private noncomputable def bonus (x : V) : ℕ := by
  classical
  exact if x ∈ F.allHigh then 1 else 0

private lemma bonus_sum : (∑ x : V, F.bonus x) = F.allHigh.card := by
  classical
  simp [bonus,Finset.sum_ite]

private lemma charge_pointwise (x : V) :
    localIndependence G x ≤ 2 + F.charge x + F.bonus x := by
  classical
  by_cases out : Outside F.c x
  · by_cases hd : 3 ≤ localIndependence G x
    · rcases F.classify_contact x out with ⟨i,hi⟩ | ⟨i,hi⟩
      · have hH := F.mem_high.mpr ⟨F.mem_singles.mpr ⟨i,hi⟩,hd⟩
        have hh : F.bonus x = 1 := by simp [bonus,hH]
        have hb := F.local_one_le_three hi
        omega
      · have hb := F.local_two_le_two hi
        omega
    · omega
  · obtain ⟨i,he⟩ : ∃ i, x = F.c i := by
      apply Classical.byContradiction
      intro h
      exact out (fun i e => h ⟨i,e⟩)
    have hd : (F.singleSite i).card ≤ F.charge x := by
      have hh := Finset.single_le_sum (f := fun j : Fin 5 =>
        if x = F.c j then (F.singleSite j).card else 0) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ i)
      simpa [charge,he] using hh
    have hb := F.local_cycle_bound i
    rw [← he] at hb
    omega

theorem total_budget :
    (∑ x, localIndependence G x) ≤ 2 * Fintype.card V + F.allSingles.card + F.allHigh.card := by
  classical
  have h := Finset.sum_le_sum (s:=(Finset.univ : Finset V)) (fun x _ => F.charge_pointwise x)
  simpa [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    F.charge_sum,F.bonus_sum,Nat.mul_comm] using h

private noncomputable def cycleSet : Finset V := by
  classical
  exact Finset.univ.image F.c

private theorem cycleCard : F.cycleSet.card = 5 := by
  classical
  unfold cycleSet
  rw [Finset.card_image_of_injective _ F.inj]
  simp

private theorem cycleSinglesDisj : Disjoint F.cycleSet F.allSingles := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hs
  obtain ⟨i,_,he⟩ := Finset.mem_image.mp hx
  obtain ⟨j,hj⟩ := F.mem_singles.mp hs
  exact hj.1 i he.symm

theorem high_eq_five (h : 3 ≤ averageLocal G) : F.allHigh.card = 5 := by
  classical
  letI : Nonempty V := ⟨F.c 0⟩
  have hD := nat_density_of_le_average G 3 h
  have bd := F.total_budget
  have t := (Finset.card_le_card (Finset.subset_univ (F.cycleSet ∪ F.allSingles)))
  rw [Finset.card_union_of_disjoint F.cycleSinglesDisj,F.cycleCard,Finset.card_univ] at t
  have m := F.high_le_five
  omega

theorem high_at_every_site (h : 3 ≤ averageLocal G) (i : Fin 5) :
    ∃ x, One G F.c x i ∧ x ∈ F.allHigh := by
  classical
  have c : (F.allHigh.image F.index).card = 5 := by
    rw [Finset.card_image_of_injOn F.high_inj,F.high_eq_five h]
  have eq := Finset.eq_of_subset_of_card_le (Finset.subset_univ (F.allHigh.image F.index))
    (by simp [c])
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp (show i ∈ F.allHigh.image F.index by simp [eq])
  exact ⟨x,he ▸ F.index_valid (F.mem_high.mp hx).1,hx⟩

theorem all_outside_singles (h : 3 ≤ averageLocal G) (x : V) (hx : Outside F.c x) :
    x ∈ F.allSingles := by
  classical
  letI : Nonempty V := ⟨F.c 0⟩
  have hD := nat_density_of_le_average G 3 h
  have bd := F.total_budget
  rw [F.high_eq_five h] at bd
  have size : (F.cycleSet ∪ F.allSingles).card = 5 + F.allSingles.card := by
    rw [Finset.card_union_of_disjoint F.cycleSinglesDisj,F.cycleCard]
  have eq := Finset.eq_of_subset_of_card_le (Finset.subset_univ (F.cycleSet ∪ F.allSingles))
    (show (Finset.univ : Finset V).card ≤ _ by rw [Finset.card_univ,size]; omega)
  have he : x ∈ F.cycleSet ∪ F.allSingles := eq.symm ▸ Finset.mem_univ x
  rcases Finset.mem_union.mp he with hx' | hx'
  · obtain ⟨i,_,he⟩ := Finset.mem_image.mp hx'
    exact (hx i he.symm).elim
  · exact hx'

#print axioms total_budget
#print axioms high_at_every_site
#print axioms all_outside_singles

end PentagonFrame
end Graffiti133Pentagon
