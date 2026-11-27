import FarPair133

namespace Graffiti133FarPentagon
namespace Frame
open SimpleGraph Graffiti133 Graffiti133Pentagon Graffiti133NoFive Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

private lemma contacts1 : ∀ i j : Fin 5, ¬pent i j → j=i ∨ j=i+2 ∨ j=i+3 := by decide
private lemma contacts2 : ∀ i j : Fin 5, ¬pent i j → ¬pent (i+1) j → j=i+3 := by decide
private lemma pair_in_slots : ∀ i j : Fin 5, (j=i ∨ j=i+2 ∨ j=i+3) →
    (j+1=i ∨ j+1=i+2 ∨ j+1=i+3) → j=i+2 := by decide
private lemma pentSites : ∀ i j : Fin 5, pent i j ↔ j=i+1 ∨ j=i+4 := by decide
private lemma pentNe : ∀ i j : Fin 5, pent i j → i ≠ j := by decide

private theorem not_adj_sites {x y : V} (hx : ∀ i,x ≠ F.c i) (hy : ∀ i,y ≠ F.c i)
    (e : G.Adj x y) {i j : Fin 5} (xi : G.Adj x (F.c i)) (yj : G.Adj y (F.c j)) :
    ¬pent i j := by
  intro p
  exact hy i (F.h4 x (F.c j) y (F.c i) (hx j) e yj.symm xi ((F.adj _ _).mpr p).symm)

private def Stamp (v : V) (i : Fin 5) : Prop := v = F.c i ∨ G.Adj v (F.c i)

private theorem stamp_inj {x y z : V} {i : Fin 5} (hne : x ≠ F.c i)
    (ey : G.Adj x y) (ez : G.Adj x z) (no : ¬ G.Adj y z)
    (sy : F.Stamp y i) (sz : F.Stamp z i) : y = z := by
  rcases sy with sy | sy <;> rcases sz with sz | sz
  · exact sy.trans sz.symm
  · exact (no (sy.symm ▸ sz.symm)).elim
  · exact (no (sz.symm ▸ sy)).elim
  · exact F.h4 x (F.c i) y z hne ey sy.symm ez sz.symm

private theorem local_le_two_of_seats (x : V) (P Q : V → Prop)
    (seats : ∀ y, G.Adj x y → P y ∨ Q y)
    (seatP : ∀ {y z}, G.Adj x y → G.Adj x z → ¬G.Adj y z → P y → P z → y=z)
    (seatQ : ∀ {y z}, G.Adj x y → G.Adj x z → ¬G.Adj y z → Q y → Q z → y=z) :
    localIndependence G x ≤ 2 := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let f (y : V) : Bool := decide (P y)
  have hh : Set.InjOn f (↑A : Set V) := by
    intro y hy z hz fe
    by_cases hp : P y
    · have hPz : P z := by
        have eq : f y = true := by simp [f,hp]
        simpa [f] using fe.symm.trans eq
      exact seatP (hN _ hy) (hN _ hz) (hI _ hy _ hz) hp hPz
    · have hpz : ¬ P z := by
        have eq : f y = false := by simp [f,hp]
        simpa [f] using fe.symm.trans eq
      exact seatQ (hN _ hy) (hN _ hz) (hI _ hy _ hz)
        ((seats _ (hN _ hy)).resolve_left hp)
        ((seats _ (hN _ hz)).resolve_left hpz)
  have h := Finset.card_le_card_of_injOn f (t:=(Finset.univ : Finset Bool))
    (fun _ _ => Finset.mem_univ _) hh
  simpa using h

private theorem local_one_two (dom : ∀ x, (∀ i, x ≠ F.c i) → Near F x)
    (no6 : ¬Nonempty (Hole G 6)) {x : V} {i : Fin 5} (hx : MakeOne F x i) :
    localIndependence G x ≤ 2 := by
  classical
  apply local_le_two_of_seats x (fun y => F.Stamp y i) (fun y => F.Stamp y (i+2))
  · intro y e
    by_cases out : ∀ j, y ≠ F.c j
    · rcases F.classify (dom y out) with ⟨j,hy⟩ | ⟨j,hy⟩
      · have eq : j = i := by
          apply Classical.byContradiction
          intro ne
          exact no6 (F.different_singles_hole hx hy (fun h => ne h.symm) e)
        exact Or.inl (Or.inr ((hy.2 i).mpr eq.symm))
      · have c1 := contacts1 i j (F.not_adj_sites hx.1 hy.1 e ((hx.2 _).mpr rfl)
          ((hy.2 _).mpr (Or.inl rfl)))
        have c2 := contacts1 i (j+1) (F.not_adj_sites hx.1 hy.1 e ((hx.2 _).mpr rfl)
          ((hy.2 _).mpr (Or.inr rfl)))
        have eq := pair_in_slots i j c1 c2
        exact Or.inr (Or.inr ((hy.2 _).mpr (Or.inl eq.symm)))
    · obtain ⟨j,hj⟩ : ∃ j, y = F.c j := by
        apply Classical.byContradiction
        intro no
        exact out (fun j h => no ⟨j,h⟩)
      have ji := (hx.2 j).mp (hj ▸ e)
      exact Or.inl (Or.inl (hj.trans (congrArg F.c ji)))
  · intro a b e1 e2 no s1 s2
    exact F.stamp_inj (hx.1 i) e1 e2 no s1 s2
  · intro a b e1 e2 no s1 s2
    exact F.stamp_inj (hx.1 (i+2)) e1 e2 no s1 s2

private theorem local_two_two (dom : ∀ x, (∀ i, x ≠ F.c i) → Near F x)
    {x : V} {i : Fin 5} (hx : MakeTwo F x i) :
    localIndependence G x ≤ 2 := by
  classical
  apply local_le_two_of_seats x (fun y => y=F.c i ∨ y=F.c (i+1)) (fun y => F.Stamp y (i+3))
  · intro y e
    by_cases out : ∀ j, y ≠ F.c j
    · obtain ⟨j,hj⟩ := (dom y out).2
      have ne1 := F.not_adj_sites hx.1 out e ((hx.2 _).mpr (Or.inl rfl)) hj
      have ne2 := F.not_adj_sites hx.1 out e ((hx.2 _).mpr (Or.inr rfl)) hj
      exact Or.inr (Or.inr (contacts2 i j ne1 ne2 ▸ hj))
    · obtain ⟨j,hj⟩ : ∃ j, y = F.c j := by
        apply Classical.byContradiction
        intro no
        exact out (fun j h => no ⟨j,h⟩)
      apply Or.inl
      rcases (hx.2 _).mp (hj ▸ e) with eq | eq
      · exact Or.inl (hj.trans (congrArg F.c eq))
      · exact Or.inr (hj.trans (congrArg F.c eq))
  · intro a b e1 e2 no s1 s2
    have adjacent : G.Adj (F.c i) (F.c (i+1)) := (F.adj _ _).mpr (Or.inl rfl)
    rcases s1 with ea | ea <;> rcases s2 with eb | eb
    · exact ea.trans eb.symm
    · exact (no (ea.symm ▸ eb.symm ▸ adjacent)).elim
    · exact (no (ea.symm ▸ eb.symm ▸ adjacent.symm)).elim
    · exact ea.trans eb.symm
  · intro a b e1 e2 no s1 s2
    exact F.stamp_inj (hx.1 (i+3)) e1 e2 no s1 s2

private noncomputable def singleSite (i : Fin 5) : Finset V := by
  classical exact Finset.univ.filter (fun x => MakeOne F x i)

private lemma site_mem {i : Fin 5} {x : V} :
    x ∈ F.singleSite i ↔ MakeOne F x i := by
  classical simp [singleSite]

private theorem local_cycle_bound (dom : ∀ x, (∀ i, x ≠ F.c i) → Near F x) (i : Fin 5) :
    localIndependence G (F.c i) ≤ 2 + (F.singleSite i).card := by
  classical
  apply Finset.sup_le_iff.mpr
  intro A hA
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let B := A \ F.singleSite i
  let seats : Finset (Fin 5) := {i+1,i+4}
  have label (w : V) (hw : w ∈ B) : ∃ j, pent i j ∧ F.Stamp w j := by
    have e := hN w (Finset.mem_sdiff.mp hw).1
    by_cases out : ∀ i, w ≠ F.c i
    · rcases F.classify (dom w out) with ⟨j,hj⟩ | ⟨j,hj⟩
      · have he := (hj.2 i).mp e.symm
        exact ((Finset.mem_sdiff.mp hw).2 (F.site_mem.mpr (he.symm ▸ hj))).elim
      · rcases (hj.2 i).mp e.symm with he | he
        · exact ⟨j+1,Or.inl (by rw [he]),Or.inr ((hj.2 _).mpr (Or.inr rfl))⟩
        · exact ⟨j,Or.inr he.symm,Or.inr ((hj.2 _).mpr (Or.inl rfl))⟩
    · obtain ⟨j,hj⟩ : ∃ j, w = F.c j := by
        apply Classical.byContradiction
        intro no
        exact out (fun j eq => no ⟨j,eq⟩)
      exact ⟨j,(F.adj _ _).mp (hj ▸ e),Or.inl hj⟩
  let f (w : V) := if hw : w ∈ B then Classical.choose (label w hw) else i
  have fs (w : V) (hw : w ∈ B) : pent i (f w) ∧ F.Stamp w (f w) := by
    simpa only [f,dif_pos hw] using Classical.choose_spec (label w hw)
  have hf (w : V) (hw : w ∈ B) : f w ∈ seats := by
    simpa [seats] using (pentSites _ _).mp (fs w hw).1
  have inj : Set.InjOn f (↑B : Set V) := by
    intro y hy z hz e
    have hyA := (Finset.mem_sdiff.mp hy).1
    have hzA := (Finset.mem_sdiff.mp hz).1
    have ne : F.c i ≠ F.c (f y) := F.inj.ne (pentNe _ _ (fs y hy).1)
    exact F.stamp_inj ne (hN _ hyA) (hN _ hzA) (hI _ hyA _ hzA)
      (fs y hy).2 (e.symm ▸ (fs z hz).2)
  have cb : B.card ≤ 2 := (Finset.card_le_card_of_injOn f hf inj).trans
    ((Finset.card_insert_le _ _).trans (by simp))
  have hInt := Finset.card_le_card (show A ∩ F.singleSite i ⊆ F.singleSite i from Finset.inter_subset_right)
  have hC : B.card + (A ∩ F.singleSite i).card = A.card := Finset.card_sdiff_add_card_inter A _
  omega

private noncomputable def singles : Finset V := by
  classical
  exact Finset.univ.filter (fun x => ∃ i, MakeOne F x i)

private lemma singles_iff (x : V) :
    x ∈ F.singles ↔ ∃ i, MakeOne F x i := by classical simp [singles]

private noncomputable def core : Finset V := by
  classical
  exact (Finset.univ : Finset (Fin 5)).image F.c

private noncomputable def fSite (x : V) : Fin 5 := by
  classical exact if h : ∃ i, MakeOne F x i then Classical.choose h else 0

private theorem sum_sites : (∑ i, (F.singleSite i).card) = (F.singles).card := by
  classical
  have fiber (i : Fin 5) : F.singleSite i = (F.singles).filter (fun x => F.fSite x = i) := by
    ext x
    rw [site_mem,Finset.mem_filter]
    have fvalid (h : x ∈ F.singles) : MakeOne F x (F.fSite x) := by
      have q := (F.singles_iff x).mp h
      unfold fSite
      rw [dif_pos q]
      exact Classical.choose_spec q
    refine ⟨?_,fun ⟨h,he⟩ => he ▸ fvalid h⟩
    intro h
    have hS := (F.singles_iff x).mpr ⟨i,h⟩
    exact ⟨hS,(h.2 _).mp (((fvalid hS).2 _).mpr rfl)⟩
  simpa only [fiber] using
    (Finset.card_eq_sum_card_fiberwise (s:=F.singles) (t:=Finset.univ)
      (f:=F.fSite) (fun _ _ => Finset.mem_univ _)).symm

private noncomputable def charge (x : V) : ℕ := by
  classical exact ∑ i : Fin 5, if x = F.c i then (F.singleSite i).card else 0

/-- A dominating induced pentagon, with no induced hexagon, forces the
total local independence to stay below three times the number of vertices. -/
theorem pent_budget (dom : ∀ x, (∀ i, x ≠ F.c i) → Near F x)
    (no6 : ¬Nonempty (Hole G 6)) :
    (∑ x, localIndependence G x) + 5 ≤ 3 * Fintype.card V := by
  classical
  have pointwise (x : V) : localIndependence G x ≤ 2 + F.charge x := by
    by_cases out : ∀ i, x ≠ F.c i
    · rcases F.classify (dom x out) with ⟨i,h⟩ | ⟨i,h⟩
      · have l := F.local_one_two dom no6 h
        omega
      · have l := F.local_two_two dom h
        omega
    · obtain ⟨i,e⟩ : ∃ i, x = F.c i := by
        apply Classical.byContradiction
        intro no
        exact out fun j e => no ⟨j,e⟩
      have hL := F.local_cycle_bound dom i
      rw [← e] at hL
      have hl : (F.singleSite i).card ≤ F.charge x := by
        have hh := Finset.single_le_sum (f := fun j : Fin 5 =>
          if x = F.c j then (F.singleSite j).card else 0) (fun j _ => Nat.zero_le _)
          (Finset.mem_univ i)
        simpa [charge,e] using hh
      omega
  have disj : Disjoint F.core F.singles := by
    apply Finset.disjoint_left.mpr
    intro x hx hs
    obtain ⟨a,_,e⟩ := Finset.mem_image.mp hx
    obtain ⟨i,hi⟩ := (F.singles_iff x).mp hs
    exact hi.1 a e.symm
  have hC : F.core.card = 5 := by
    unfold core
    rw [Finset.card_image_of_injective _ F.inj]
    simp
  have hSize := Finset.card_le_card (Finset.subset_univ (F.core ∪ F.singles))
  rw [Finset.card_union_of_disjoint disj,hC,Finset.card_univ] at hSize
  have hcharge : (∑ x, F.charge x) = F.singles.card := by
    unfold charge
    rw [Finset.sum_comm]
    simp [F.sum_sites]
  have h := Finset.sum_le_sum (s:=(Finset.univ : Finset V)) (fun x _ => pointwise x)
  have hu : (∑ x, localIndependence G x) ≤ 2*Fintype.card V + F.singles.card := by
    simpa [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcharge,
      Nat.mul_comm] using h
  omega

#print axioms pent_budget
end Frame
end Graffiti133FarPentagon
