import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Independent Lean formalization of Jonas J. Gebendorfer's proof of #317.
https://www.researchgate.net/publication/411012117_Three_Well-Total-Domination_Conjectures_from_the_Written_on_the_Wall_II_List_Structural_resolutions_of_Conjectures_315_317_and_322
-/
namespace Graffiti317
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def TotalDominating (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x, ∃ y ∈ S, G.Adj x y

def WellTotalDominated (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, TotalDominating G S →
    (∀ T ⊆ S, TotalDominating G T → T = S) →
      ∀ T : Finset V, TotalDominating G T → S.card ≤ T.card

omit [Fintype V] in
private theorem total_dom_card_ge_two {G : SimpleGraph V} [Nonempty V]
    {T : Finset V} (hT : TotalDominating G T) : 2 ≤ T.card := by
  obtain ⟨a,ha,_⟩ := hT (Classical.choice ‹Nonempty V›)
  obtain ⟨b,hb,he⟩ := hT a
  have h : ({a,b} : Finset V) ⊆ T := by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact ha
    · simpa only [mem_singleton.mp hz] using hb
  have hh := card_le_card h
  simpa [he.ne] using hh

omit [Fintype V] in
theorem private_neighbor_of_minimal_total_domination {G : SimpleGraph V} {S : Finset V}
    (hS : TotalDominating G S) (hmin : ∀ T ⊆ S, TotalDominating G T → T = S)
    {x : V} (hx : x ∈ S) :
    ∃ p, G.Adj p x ∧ ∀ y ∈ S, G.Adj p y → y = x := by
  classical
  have hnot : ¬ TotalDominating G (S.erase x) := by
    intro ht
    have he := hmin _ (erase_subset _ _) ht
    have hh : x ∈ S.erase x := he.symm ▸ hx
    exact (mem_erase.mp hh).1 rfl
  unfold TotalDominating at hnot
  push_neg at hnot
  obtain ⟨p,hp⟩ := hnot
  obtain ⟨q,hq,hpq⟩ := hS p
  have he : q = x := by
    by_cases h : q = x
    · exact h
    · exact (hp q (mem_erase.mpr ⟨h,hq⟩) hpq).elim
  refine ⟨p, he ▸ hpq, ?_⟩
  intro y hy hpy
  by_cases h : y = x
  · exact h
  · exact (hp y (mem_erase.mpr ⟨h,hy⟩) hpy).elim

theorem minimal_total_domination_missing_edge_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} (hS : TotalDominating G S)
    (hmin : ∀ T ⊆ S, TotalDominating G T → T = S) :
    S.card * (S.card-2) ≤ 2 * Gᶜ.edgeFinset.card := by
  classical
  choose p hp hpriv using
    (fun x : S => private_neighbor_of_minimal_total_domination hS hmin x.property)
  have hi : Function.Injective p := by
    intro x y e
    apply Subtype.ext
    exact (hpriv x y.val y.property (e.symm ▸ hp y)).symm
  let R := univ.image p
  have hR : R.card = S.card := by
    rw [card_image_of_injective _ hi,card_univ,Fintype.card_coe]
  have hdeg (x : S) : S.card-2 ≤ Gᶜ.degree (p x) := by
    let D := (S.erase x.val).erase (p x)
    have hD : S.card-2 ≤ D.card := by
      have h₂ := card_erase_add_one x.property
      have h₃ := pred_card_le_card_erase (s := S.erase x.val) (a := p x)
      change (S.erase x.val).card-1 ≤ D.card at h₃
      omega
    have hsub : D ⊆ Gᶜ.neighborFinset (p x) := by
      intro y hy
      obtain ⟨hpy,hy'⟩ := mem_erase.mp hy
      obtain ⟨hxy,hyS⟩ := mem_erase.mp hy'
      exact (Gᶜ.mem_neighborFinset _ _).mpr ((compl_adj _ _ _).mpr
        ⟨hpy.symm,fun e => hxy (hpriv x y hyS e)⟩)
    exact hD.trans (card_le_card hsub)
  calc
    S.card * (S.card-2) = ∑ _x ∈ R, (S.card-2) := by simp [hR]
    _ ≤ ∑ x ∈ R, Gᶜ.degree x := by
      apply sum_le_sum
      intro y hy
      obtain ⟨x,_,rfl⟩ := mem_image.mp hy
      exact hdeg x
    _ ≤ ∑ x : V, Gᶜ.degree x := by
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (by simp)
    _ = 2 * Gᶜ.edgeFinset.card := Gᶜ.sum_degrees_eq_twice_card_edges

#print axioms private_neighbor_of_minimal_total_domination
#print axioms minimal_total_domination_missing_edge_bound
/-- The largest order of an induced tree. -/
noncomputable def treeNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact ((univ : Finset (Finset V)).filter
    (fun S : Finset V => (G.induce (↑S : Set V)).IsTree)).sup Finset.card

theorem induced_tree_lower_bounds_complement (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : (G.induce (↑S : Set V)).IsTree) :
    S.card.choose 2 ≤ S.card-1 + Gᶜ.edgeFinset.card := by
  classical
  let H := G.induce (↑S : Set V)
  have hm : (Hᶜ.edgeFinset.map (Function.Embedding.subtype (↑S : Set V)).sym2Map) ⊆ Gᶜ.edgeFinset := by
    intro e he
    obtain ⟨q,hq,rfl⟩ := mem_map.mp he
    induction q using Sym2.ind with
    | h a b =>
      change s(a.val,b.val) ∈ Gᶜ.edgeFinset
      rw [mem_edgeFinset,mem_edgeSet] at hq ⊢
      have h := (compl_adj H a b).mp hq
      exact (compl_adj G _ _).mpr ⟨fun e => h.1 (Subtype.ext e),h.2⟩
  have hle := card_le_card hm
  rw [Finset.card_map] at hle
  have hj : H.edgeFinset ∪ Hᶜ.edgeFinset = (⊤ : SimpleGraph (↑S : Set V)).edgeFinset := by
    rw [← edgeFinset_sup]
    ext e
    simp only [mem_edgeFinset,sup_compl_eq_top]
  have hd : Disjoint H.edgeFinset Hᶜ.edgeFinset :=
    disjoint_edgeFinset.mpr disjoint_compl_right
  have hsplit := Finset.card_union_of_disjoint hd
  rw [hj,card_edgeFinset_top_eq_card_choose_two] at hsplit
  change (Fintype.card {x // x ∈ S}).choose 2 = _ at hsplit
  rw [Fintype.card_coe] at hsplit
  have hcard := hS.card_edgeFinset
  change H.edgeFinset.card + 1 = Fintype.card {x // x ∈ S} at hcard
  rw [Fintype.card_coe] at hcard
  omega

theorem complement_at_most_four_of_treeNumber (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : Gᶜ.edgeFinset.card ≤ treeNumber G) : Gᶜ.edgeFinset.card ≤ 4 := by
  classical
  let F := (univ : Finset (Finset V)).filter
    (fun S : Finset V => (G.induce (↑S : Set V)).IsTree)
  by_cases hF : F.Nonempty
  · obtain ⟨S,hSF,hmax⟩ := exists_max_image F Finset.card hF
    have ht : treeNumber G ≤ S.card := Finset.sup_le_iff.mpr hmax
    have hsize := h.trans ht
    have hS : (G.induce (↑S : Set V)).IsTree := (mem_filter.mp hSF).2
    have hin := induced_tree_lower_bounds_complement G S hS
    by_cases hk : 5 ≤ S.card
    · have hu : S.card*4 ≤ S.card*(S.card-1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hl : 2*S.card ≤ S.card.choose 2 := by
        rw [Nat.choose_two_right]
        omega
      omega
    · omega
  · have hbot : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    have ht : treeNumber G = 0 := by
      change F.sup Finset.card = 0
      rw [hbot]
      rfl
    omega

theorem minimal_total_domination_at_most_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : Gᶜ.edgeFinset.card ≤ treeNumber G) {S : Finset V} (hS : TotalDominating G S)
    (hm : ∀ T ⊆ S, TotalDominating G T → T = S) : S.card ≤ 4 := by
  have h4 := complement_at_most_four_of_treeNumber G h
  have hb := minimal_total_domination_missing_edge_bound G hS hm
  by_cases hs : 5 ≤ S.card
  · have hu : 3 * S.card ≤ (S.card-2) * S.card :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.mul_comm (S.card-2)] at hu
    omega
  · omega

#print axioms induced_tree_lower_bounds_complement
#print axioms complement_at_most_four_of_treeNumber
#print axioms minimal_total_domination_at_most_four

/-- Private neighbors outside the dominating set each charge |S|-1
distinct missing edges, with no double counting. -/
theorem external_private_missing_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (p : S → V) (hp : Function.Injective p)
    (hpriv : ∀ x : S, ∀ y ∈ S, G.Adj (p x) y → y = x.val) :
    ∃ E : Finset (Sym2 V), E ⊆ Gᶜ.edgeFinset ∧
      E.card = (S.attach.filter (fun x => p x ∉ S)).card * (S.card-1) ∧
      ∀ a ∈ S, ∀ b ∈ S, s(a,b) ∉ E := by
  classical
  let A := S.attach.filter (fun x => p x ∉ S)
  let P := A.sigma (fun x => S.erase x.val)
  let φ : (Σ _ : S, V) → Sym2 V := fun z => s(p z.1,z.2)
  let E := P.image φ
  have out {z : (Σ _ : S, V)} (h : z ∈ P) : p z.1 ∉ S :=
    (mem_filter.mp (mem_sigma.mp h).1).2
  have inS {z : (Σ _ : S, V)} (h : z ∈ P) : z.2 ∈ S :=
    (mem_erase.mp (mem_sigma.mp h).2).2
  have hinj : Set.InjOn φ ↑P := by
    intro a ha b hb he
    rcases a with ⟨a,x⟩
    rcases b with ⟨b,y⟩
    change (Sigma.mk a x : Σ _ : S, V) ∈ P at ha
    change (Sigma.mk b y : Σ _ : S, V) ∈ P at hb
    change s(p a,x) = s(p b,y) at he
    rcases Sym2.mk_eq_mk_iff.mp he with h | h
    · obtain rfl : a = b := hp (congrArg Prod.fst h)
      obtain rfl : x = y := congrArg Prod.snd h
      rfl
    · have eq : p a = y := congrArg Prod.fst h
      exact (out ha (show p a ∈ S by rw [eq]; exact inS hb)).elim
  refine ⟨E,?_,?_,?_⟩
  · intro e he
    obtain ⟨z,hz,rfl⟩ := mem_image.mp he
    have hn : p z.1 ≠ z.2 := fun h => out hz (h.symm ▸ inS hz)
    refine mem_edgeFinset.mpr ((compl_adj G _ _).mpr ⟨hn,?_⟩)
    exact fun h => (mem_erase.mp (mem_sigma.mp hz).2).1 (hpriv z.1 _ (inS hz) h)
  · rw [card_image_of_injOn hinj,card_sigma]
    have hC (x : S) : (S.erase x.val).card = S.card-1 := card_erase_of_mem x.property
    simp only [hC,sum_const,nsmul_eq_mul]
    rfl
  · intro a ha b hb he
    obtain ⟨z,hz,he⟩ := mem_image.mp he
    change s(p z.1,z.2) = s(a,b) at he
    rcases Sym2.mk_eq_mk_iff.mp he with eq | eq
    · have h : p z.1 = a := congrArg Prod.fst eq
      exact out hz (by rw [h]; exact ha)
    · have h : p z.1 = b := congrArg Prod.fst eq
      exact out hz (by rw [h]; exact hb)

#print axioms external_private_missing_edges

omit [Fintype V] in
private theorem triple_subset_eq {S : Finset V} (hc : S.card = 3)
    {a b c : V} (ha : a ∈ S) (hb : b ∈ S) (hz : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a,b,c} : Finset V) = S := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · rw [hc]
    simp [hab,hac,hbc]

theorem minimal_total_domination_not_three (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} (hS : TotalDominating G S)
    (hmin : ∀ T ⊆ S, TotalDominating G T → T = S)
    (h4 : Gᶜ.edgeFinset.card ≤ 4) (h3 : S.card = 3) : False := by
  classical
  choose p hp hpriv using
    (fun x : S => private_neighbor_of_minimal_total_domination hS hmin x.property)
  have hinj : Function.Injective p := by
    intro x y e
    apply Subtype.ext
    exact (hpriv x y.val y.property (e.symm ▸ hp y)).symm
  obtain ⟨E,hE,hEC,hint⟩ := external_private_missing_edges G S p hinj hpriv
  let A := S.attach.filter (fun x => p x ∉ S)
  let B := S.attach.filter (fun x => p x ∈ S)
  have hs : B.card + A.card = S.card := by
    simpa only [A,B,card_attach] using
      (filter_card_add_filter_neg_card_eq_card (s := S.attach) (p := fun x => p x ∈ S))
  have hbcard : B.card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_cases heq : x = y
    · exact heq
    exfalso
    have hpx : p x ∈ S := (mem_filter.mp hx).2
    have hpy : p y ∈ S := (mem_filter.mp hy).2
    have hpq : p x ≠ p y := fun h => heq (hinj h)
    have hxy : x.val ≠ y.val := fun h => heq (Subtype.ext h)
    by_cases he : G.Adj (p x) (p y)
    · have h₁ : p y = x.val := hpriv x _ hpy he
      have h₂ : p x = y.val := hpriv y _ hpx he.symm
      have hsub : ¬ S ⊆ ({p x,p y} : Finset V) := by
        intro hh
        have hh' := card_le_card hh
        simp [hpq,h3] at hh'
      obtain ⟨z,hz,hno⟩ := not_subset.mp hsub
      have hzx : z ≠ p x := by
        intro h
        exact hno (by simp [h])
      have hzy : z ≠ p y := by
        intro h
        exact hno (by simp [h])
      have heqS := triple_subset_eq h3 hpx hpy hz hpq hzx.symm hzy.symm
      obtain ⟨w,hw,hwz⟩ := hS z
      rw [← heqS] at hw
      simp only [mem_insert,mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hzy ((hpriv x _ hz hwz.symm).trans h₁.symm)
      · exact hzx ((hpriv y _ hz hwz.symm).trans h₂.symm)
      · exact G.loopless _ hwz
    · have hxpy : p y ≠ x.val := fun h => he (by rw [h]; exact hp x)
      have hypx : p x ≠ y.val := fun h => he (by rw [h]; exact (hp y).symm)
      have heqS := triple_subset_eq h3 hpx hpy x.property hpq (hp x).ne hxpy
      have heSub : S ⊆ ({p x,p y,x.val} : Finset V) := by
        intro z hz
        simpa only [heqS] using hz
      have hyS := heSub y.property
      simp only [mem_insert,mem_singleton] at hyS
      rcases hyS with h | h | h
      · exact hypx h.symm
      · exact (hp y).ne h.symm
      · exact hxy h.symm
  change E.card = A.card * (S.card-1) at hEC
  by_cases hb0 : B.card = 0
  · have hcard := card_le_card hE
    rw [h3] at hs hEC
    omega
  · obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < B.card)
    have hpx : p x ∈ S := (mem_filter.mp hx).2
    have hsub : ¬ S ⊆ ({p x,x.val} : Finset V) := by
      intro hh
      have hh' := card_le_card hh
      simp [(hp x).ne,h3] at hh'
    obtain ⟨z,hz,hno⟩ := not_subset.mp hsub
    have hzx : p x ≠ z := by intro e; exact hno (by simp [← e])
    have hzt : z ≠ x.val := by intro e; exact hno (by simp [e])
    have hn : ¬ G.Adj (p x) z := fun e => hzt (hpriv x z hz e)
    have hmem : s(p x,z) ∈ Gᶜ.edgeFinset :=
      mem_edgeFinset.mpr ((compl_adj G _ _).mpr ⟨hzx,hn⟩)
    have hE' : insert s(p x,z) E ⊆ Gᶜ.edgeFinset := by
      intro e he
      rcases mem_insert.mp he with rfl | he
      · exact hmem
      · exact hE he
    have hcard := card_le_card hE'
    rw [card_insert_of_not_mem (hint _ hpx _ hz),hEC,h3] at hcard
    omega

#print axioms minimal_total_domination_not_three

private theorem missing_degree_from_private (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {x p : V} (_hx : x ∈ S)
    (hpriv : ∀ y ∈ S, G.Adj p y → y = x) :
    (S.erase x |>.erase p).card ≤ Gᶜ.degree p := by
  apply card_le_card
  intro y hy
  obtain ⟨hpy,hy'⟩ := mem_erase.mp hy
  obtain ⟨hxy,hyS⟩ := mem_erase.mp hy'
  exact (Gᶜ.mem_neighborFinset _ _).mpr ((compl_adj _ _ _).mpr
    ⟨hpy.symm,fun e => hxy (hpriv y hyS e)⟩)

theorem sharp_four_private_structure (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} (hS : TotalDominating G S)
    (hmin : ∀ T ⊆ S, TotalDominating G T → T = S)
    (h4 : Gᶜ.edgeFinset.card ≤ 4) (hs4 : S.card = 4) :
    Gᶜ.edgeFinset.card = 4 ∧
      (∀ x ∈ S, ∃ y ∈ S, G.Adj x y ∧ ∀ z ∈ S, G.Adj x z → z = y) ∧
      ∀ x ∉ S, ∀ z, x ≠ z → G.Adj x z := by
  classical
  choose p hp hpriv using
    (fun x : S => private_neighbor_of_minimal_total_domination hS hmin x.property)
  have hinj : Function.Injective p := by
    intro x y e
    apply Subtype.ext
    exact (hpriv x y.val y.property (e.symm ▸ hp y)).symm
  let R := univ.image p
  have hR : R.card = 4 := by
    rw [card_image_of_injective _ hinj,card_univ,Fintype.card_coe,hs4]
  have hdeg (x : S) : 2 ≤ Gᶜ.degree (p x) := by
    have h := missing_degree_from_private G x.property (hpriv x)
    have hj := pred_card_le_card_erase (s := S.erase x.val) (a := p x)
    rw [card_erase_of_mem x.property,hs4] at hj
    omega
  have hdegR (v : V) (hv : v ∈ R) : 2 ≤ Gᶜ.degree v := by
    obtain ⟨x,_,rfl⟩ := mem_image.mp hv
    exact hdeg x
  have hsum (A : Finset V) (hA : A ⊆ R) :
      A.card*2 ≤ ∑ v ∈ A, Gᶜ.degree v := by
    calc
      A.card*2 = ∑ _v ∈ A, (2 : ℕ) := by simp
      _ ≤ _ := sum_le_sum (fun v hv => hdegR v (hA hv))
  have hU : (∑ x : V, Gᶜ.degree x) = 2*Gᶜ.edgeFinset.card := Gᶜ.sum_degrees_eq_twice_card_edges
  have hupper (A : Finset V) : (∑ v ∈ A, Gᶜ.degree v) ≤ 8 := by
    have h : (∑ v ∈ A, Gᶜ.degree v) ≤ ∑ v : V, Gᶜ.degree v :=
      sum_le_sum_of_subset_of_nonneg (subset_univ A) (by simp)
    omega
  have heq (v : V) (hv : v ∈ R) : Gᶜ.degree v = 2 := by
    have h := hsum (R.erase v) (erase_subset _ _)
    have h' : (∑ x ∈ R.erase v, Gᶜ.degree x) + Gᶜ.degree v = ∑ x ∈ R, Gᶜ.degree x :=
      sum_erase_add (s := R) (f := fun x => Gᶜ.degree x) hv
    have h'' := hupper R
    rw [card_erase_of_mem hv,hR] at h
    have hd := hdegR v hv
    omega
  have hpS (x : S) : p x ∈ S := by
    by_cases hpS : p x ∈ S
    · exact hpS
    exfalso
    have h := missing_degree_from_private G x.property (hpriv x)
    have hne : p x ∉ S.erase x.val := fun h => hpS (mem_erase.mp h).2
    rw [erase_eq_of_not_mem hne,card_erase_of_mem x.property,hs4] at h
    have h' := heq (p x) (mem_image.mpr ⟨x,mem_univ _,rfl⟩)
    omega
  have hRS : R = S := by
    apply eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨x,_,rfl⟩ := mem_image.mp hv
      exact hpS x
    · omega
  have hsumS : (∑ v ∈ S, Gᶜ.degree v) = 8 := by
    have hh (v : V) (hv : v ∈ S) : Gᶜ.degree v = 2 := heq v (hRS.symm ▸ hv)
    rw [sum_congr rfl hh]
    simp [hs4]
  refine ⟨?_,?_,?_⟩
  · have h : (∑ v ∈ S, Gᶜ.degree v) ≤ ∑ v : V, Gᶜ.degree v :=
      sum_le_sum_of_subset_of_nonneg (subset_univ S) (by simp)
    omega
  · intro v hv
    have hrv : v ∈ R := hRS.symm ▸ hv
    obtain ⟨x,_,rfl⟩ := mem_image.mp hrv
    exact ⟨x.val,x.property,hp x,hpriv x⟩
  · intro v hv w hvw
    have hVS : S ⊆ (univ : Finset V).erase v := by simp [subset_iff,hv,ne_comm]
    have h : (∑ x ∈ S, Gᶜ.degree x) ≤ ∑ x ∈ (univ : Finset V).erase v, Gᶜ.degree x :=
      sum_le_sum_of_subset_of_nonneg hVS (by simp)
    have hb : (∑ x ∈ (univ : Finset V).erase v, Gᶜ.degree x) + Gᶜ.degree v =
        ∑ x : V, Gᶜ.degree x := sum_erase_add (s := (univ : Finset V)) (f := fun x => Gᶜ.degree x) (mem_univ v)
    have hzero : Gᶜ.degree v = 0 := by omega
    by_cases he : G.Adj v w
    · exact he
    exfalso
    have hw : w ∈ Gᶜ.neighborFinset v := (Gᶜ.mem_neighborFinset _ _).mpr
      ((compl_adj G _ _).mpr ⟨hvw,he⟩)
    have hp := card_pos.mpr ⟨w,hw⟩
    change 0 < Gᶜ.degree v at hp
    omega

#print axioms sharp_four_private_structure

omit [Fintype V] in
private theorem no_independent_three_in_sharp_four {G : SimpleGraph V}
    {S : Finset V} (hs : S.card = 4)
    (hu : ∀ x ∈ S, ∃ y ∈ S, G.Adj x y ∧ ∀ z ∈ S, G.Adj x z → z = y)
    (ho : ∀ x ∉ S, ∀ y, x ≠ y → G.Adj x y)
    {A : Finset V} (ha : A.card = 3)
    (hi : ∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b) : False := by
  classical
  have has : A ⊆ S := by
    intro x hx
    by_cases hxs : x ∈ S
    · exact hxs
    exfalso
    have hnot : ¬ A ⊆ ({x} : Finset V) := by
      intro h
      have hl := card_le_card h
      simp [ha] at hl
    obtain ⟨y,hy,hno⟩ := not_subset.mp hnot
    have hyx : x ≠ y := fun e => hno (by rw [← e]; simp)
    exact hi _ hx _ hy (ho _ hxs _ hyx)
  choose f hfS hfA hfU using (fun x : A => hu x.val (has x.property))
  have hfinj : Function.Injective f := by
    intro x y e
    have h1 := hfA x
    have h2 := hfA y
    rw [← e] at h2
    obtain ⟨z,hz,_hz,hzU⟩ := hu (f x) (hfS x)
    exact Subtype.ext
      ((hzU _ (has x.property) h1.symm).trans (hzU _ (has y.property) h2.symm).symm)
  let R := univ.image f
  have hRc : R.card = 3 := by
    rw [card_image_of_injective _ hfinj,card_univ,Fintype.card_coe,ha]
  have hRS : R ⊆ S \ A := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    exact mem_sdiff.mpr ⟨hfS y,fun hy => hi _ y.property _ hy (hfA y)⟩
  have h := card_le_card hRS
  rw [card_sdiff has,hs,ha,hRc] at h
  omega

omit [Fintype V] in
private theorem sharp_four_forbids_induced_tree {G : SimpleGraph V} [DecidableRel G.Adj]
    {S W : Finset V} (hs : S.card = 4) (hw : W.card = 4)
    (hu : ∀ x ∈ S, ∃ y ∈ S, G.Adj x y ∧ ∀ z ∈ S, G.Adj x z → z = y)
    (ho : ∀ x ∉ S, ∀ y, x ≠ y → G.Adj x y)
    (hTree : (G.induce (↑W : Set V)).IsTree) : False := by
  classical
  let H := G.induce (↑W : Set V)
  have hH : Fintype.card {x // x ∈ W} = 4 := by rw [Fintype.card_coe,hw]
  have hE := hTree.card_edgeFinset
  change H.edgeFinset.card+1 = Fintype.card {x // x ∈ W} at hE
  rw [hH] at hE
  by_cases hsub : W ⊆ S
  · have hWS : W = S := eq_of_subset_of_card_le hsub (by omega)
    have hSW : S ⊆ W := by rw [hWS]
    have hdeg : ∀ x : {x // x ∈ W}, H.degree x = 1 := by
      intro x
      obtain ⟨y,hy,ha,huni⟩ := hu x.val (hsub x.property)
      let y' : {x // x ∈ W} := ⟨y,hSW hy⟩
      have he : H.neighborFinset x = {y'} := by
        ext z
        rw [mem_singleton,mem_neighborFinset]
        constructor
        · intro hz
          exact Subtype.ext (huni z.val (hsub z.property) hz)
        · intro hz
          subst z
          exact ha
      rw [← card_neighborFinset_eq_degree,he,card_singleton]
    have hsum : (∑ x : {x // x ∈ W}, H.degree x) = 4 := by simp [hdeg,hH,hw]
    have hhand : (∑ x : {x // x ∈ W}, H.degree x) = 2*H.edgeFinset.card :=
      H.sum_degrees_eq_twice_card_edges
    omega
  · obtain ⟨v,hv,hvS⟩ := not_subset.mp hsub
    let v' : {x // x ∈ W} := ⟨v,hv⟩
    have hvdeg : H.degree v' = 3 := by
      have he : H.neighborFinset v' = (univ : Finset {x // x ∈ W}).erase v' := by
        ext x
        rw [mem_neighborFinset,mem_erase]
        constructor
        · intro h
          exact ⟨h.ne.symm,mem_univ _⟩
        · intro h
          exact ho _ hvS _ (fun e => h.1 (Subtype.ext e.symm))
      rw [← card_neighborFinset_eq_degree,he,card_erase_of_mem (mem_univ _),card_univ]
      change Fintype.card {x // x ∈ W}-1 = 3
      rw [hH]
    have hI : H.incidenceFinset v' = H.edgeFinset := by
      apply eq_of_subset_of_card_le
      · intro e he
        rw [incidenceFinset_eq_filter] at he
        exact (mem_filter.mp he).1
      · rw [card_incidenceFinset_eq_degree,hvdeg]
        omega
    apply no_independent_three_in_sharp_four hs hu ho (A := W.erase v)
      (by rw [card_erase_of_mem hv,hw])
    intro a ha b hb hab
    obtain ⟨hna,haW⟩ := mem_erase.mp ha
    obtain ⟨hnb,hbW⟩ := mem_erase.mp hb
    let a' : {x // x ∈ W} := ⟨a,haW⟩
    let b' : {x // x ∈ W} := ⟨b,hbW⟩
    have he : s(a',b') ∈ H.incidenceFinset v' := by
      rw [hI]
      exact mem_edgeFinset.mpr (show H.Adj a' b' from hab)
    rw [incidenceFinset_eq_filter] at he
    have hm := (mem_filter.mp he).2
    rcases Sym2.mem_iff.mp hm with h | h
    · exact hna (congrArg Subtype.val h).symm
    · exact hnb (congrArg Subtype.val h).symm

/-- Exact complement-bearing catalogued statement of Graffiti.pc #317. -/
theorem conjecture317 (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (_hn : 1 < Fintype.card V) (h : Gᶜ.edgeFinset.card ≤ treeNumber G) :
    WellTotalDominated G := by
  classical
  letI := hc.nonempty
  intro S hS hmin T hT
  have h2 := total_dom_card_ge_two hS
  have h4 := minimal_total_domination_at_most_four G h hS hmin
  have he4 := complement_at_most_four_of_treeNumber G h
  by_cases hS2 : S.card = 2
  · rw [hS2]
    exact total_dom_card_ge_two hT
  by_cases hS3 : S.card = 3
  · exact (minimal_total_domination_not_three G hS hmin he4 hS3).elim
  exfalso
  have hS4 : S.card = 4 := by omega
  obtain ⟨he,hu,ho⟩ := sharp_four_private_structure G hS hmin he4 hS4
  have ht : 4 ≤ treeNumber G := he ▸ h
  let F := (univ : Finset (Finset V)).filter
    (fun W : Finset V => (G.induce (↑W : Set V)).IsTree)
  have hF : F.Nonempty := by
    by_cases hh : F.Nonempty
    · exact hh
    exfalso
    have he := Finset.not_nonempty_iff_eq_empty.mp hh
    change 4 ≤ F.sup Finset.card at ht
    rw [he] at ht
    simp at ht
  obtain ⟨W,hWF,hmax⟩ := exists_max_image F Finset.card hF
  have hW : (G.induce (↑W : Set V)).IsTree := (mem_filter.mp hWF).2
  have hl : treeNumber G ≤ W.card := Finset.sup_le_iff.mpr hmax
  have hbound := induced_tree_lower_bounds_complement G W hW
  have hW4 : W.card = 4 := by
    by_cases hh : 5 ≤ W.card
    · have hu' : W.card*4 ≤ W.card*(W.card-1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hl' : 2*W.card ≤ W.card.choose 2 := by rw [Nat.choose_two_right]; omega
      omega
    · omega
  exact sharp_four_forbids_induced_tree hS4 hW4 hu ho hW

#print axioms conjecture317

end Graffiti317
