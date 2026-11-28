import SixSingletonQ1Inactive189
import SixSingletonQ1PortBoard189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset ArticulationPair PortCertificates
open private Cmp from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark Common strictA strictB from SixSingletonGeometry189
open private nearBal from SixSingletonFiveGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b s z : V} {D : Cmp G a b}
set_option linter.unusedSectionVars false

noncomputable def q1Active (J : Finset V) (x : V) : Bool :=
  @decide (∃ u∈J,G.Adj x u) (Classical.propDecidable _)

theorem q1Active_iff (J : Finset V) (x : V) :
    q1Active (G:=G) J x=true ↔ ∃ u∈J,G.Adj x u := by
  simp [q1Active]

theorem q1_ports_active (F : SixVisibleData G D s) (bal : nearBal D={z})
    {m : ℕ} (P : Q1PortBoard D s m) {J : Finset V} (Jmax : (Dark D).erase z⊆J)
    (left : (strictA D).Nonempty) (right : (strictB D).Nonempty) :
    (∃ i : Fin 6,i.val < m ∧ q1Active (G:=G) J (P.label (widenQ1 (by decide : 6≤9) i))=true) ∧
    (∃ i : Fin 6,m ≤ i.val ∧ i.val < m+2 ∧ q1Active (G:=G) J (P.label (widenQ1 (by decide : 6≤9) i))=true) := by
  classical
  let f (i : Fin 6) := P.label (widenQ1 (by decide : 6≤9) i)
  have fvis {x : V} (h : x∈Vis D) : ∃ i,f i=x := by
    rw [←P.portImage] at h
    obtain ⟨i,_,e⟩ := mem_image.mp h
    exact ⟨i,e⟩
  have visL {x : V} (hx : x∈EA D) : x∈Vis D := by rw [←F.visiblePart]; exact mem_union_left _ (mem_union_left _ hx)
  have visR {x : V} (hx : x∈EB D) : x∈Vis D := by rw [←F.visiblePart]; exact mem_union_left _ (mem_union_right _ hx)
  have zB : z∈nearBal D := by rw [bal]; simp
  have same := (mem_filter.mp (mem_filter.mp zB).1).2
  constructor
  · obtain ⟨u,ul⟩ := left
    obtain ⟨x,xl,xu⟩ := F.rootsA u ul
    obtain ⟨i,ei⟩ := fvis (visL xl)
    have near : u∈J := Jmax (mem_erase.mpr ⟨fun e=>by
      subst u
      exact Nat.ne_of_lt (mem_filter.mp ul).2 same,
      (q1_dark_parts_subsets F).1 ul⟩)
    refine ⟨i,?_,(q1Active_iff _ _).mpr ⟨u,near,(show G.Adj (f i) u by rw [ei]; exact xu)⟩⟩
    by_contra h
    have h' : m ≤ i.val := Nat.le_of_not_gt h
    have no := (F.eA x xl).2
    by_cases hi : i.val < m+2
    · have e : G.Adj b (f i) := (F.eB _ (P.right i h' hi)).1
      rw [ei] at e
      exact no e
    have e : G.Adj b (f i) := (F.common _ (P.common i (Nat.le_of_not_gt hi))).2
    rw [ei] at e
    exact no e
  obtain ⟨u,ur⟩ := right
  obtain ⟨y,yr,yu⟩ := F.rootsB u ur
  obtain ⟨i,ei⟩ := fvis (visR yr)
  have near : u∈J := Jmax (mem_erase.mpr ⟨fun e=>by
    subst u
    exact Nat.ne_of_lt (mem_filter.mp ur).2 same.symm,
    (q1_dark_parts_subsets F).2.1 ur⟩)
  have no := (F.eB y yr).2
  refine ⟨i,?_,?_,(q1Active_iff _ _).mpr ⟨u,near,(show G.Adj (f i) u by rw [ei]; exact yu)⟩⟩
  · by_contra h
    have e : G.Adj a (f i) := (F.eA _ (P.left i (Nat.lt_of_not_ge h))).1
    rw [ei] at e
    exact no e
  · by_contra h
    have e : G.Adj a (f i) := (F.common _ (P.common i (Nat.le_of_not_gt h))).1
    rw [ei] at e
    exact no e

theorem q1_isolated_balance_universal (F : SixVisibleData G D s) (bal : nearBal D={z})
    (v6 : (Vis D).card=6) (zero : (inside G (Dark D) z).card=0) :
    ∀ u∈Vis D,G.Adj z u := by
  have p := six_q1_balance_port_slots F bal
  rw [zero,Nat.sub_zero] at p
  have eq := eq_of_subset_of_card_le (filter_subset (G.Adj z) (Vis D)) (by simpa only [v6] using p)
  intro u hu
  exact (mem_filter.mp (eq.symm ▸ hu)).2

#print axioms q1_ports_active
#print axioms q1_isolated_balance_universal
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
