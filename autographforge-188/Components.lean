import ForcingBasis
import PowerBasis
import CographJoin

namespace CographForcing188
open Finset SimpleGraph Function ForcingDrop711 AutoGraphPowerBurning
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Each component of a fully forcing set has an initially eligible seed.
If every vertex in the component was initially colored its white count is zero. -/
theorem active_in_component {k : ℕ} {S : Finset V} (success : full G k S)
    (c : G.ConnectedComponent) : ∃ x ∈ S, x ∈ c.supp ∧ (G.neighborFinset x \ S).card ≤ k := by
  classical
  by_contra none
  let rounds := fun i : ℕ => (step G k)^[i] S
  have frozen (i : ℕ) : ∀ v ∈ c.supp, v ∈ rounds i → v ∈ S := by
    induction i with
    | zero => exact fun _ _ h => h
    | succ i ih =>
      intro v vc hv
      change v ∈ (step G k)^[i+1] S at hv
      rw [iterate_succ_apply'] at hv
      obtain hs | ⟨w,hw,wv,limit⟩ := (mem_step G).mp hv
      · exact ih v vc hs
      · have wc := (c.mem_supp_congr_adj wv).mpr vc
        have inside : G.neighborFinset w \ S ⊆ G.neighborFinset w \ rounds i := by
          intro z hz
          obtain ⟨zw,white⟩ := mem_sdiff.mp hz
          have zc := (c.mem_supp_congr_adj ((G.mem_neighborFinset w z).mp zw)).mp wc
          exact mem_sdiff.mpr ⟨zw,fun seen => white (ih z zc seen)⟩
        exact (none ⟨w,ih w wc hw,wc,(card_le_card inside).trans limit⟩).elim
  have allSeeds (v : V) (vc : v ∈ c.supp) : v ∈ S := by
    apply frozen (Fintype.card V) v vc
    change v ∈ (step G k)^[Fintype.card V] S
    rw [show (step G k)^[Fintype.card V] S = univ from success]
    exact mem_univ _
  have around : G.neighborFinset c.out ⊆ S := by
    intro v h
    exact allSeeds v ((c.mem_supp_congr_adj ((G.mem_neighborFinset _ _).mp h)).mp c.out_eq)
  exact none ⟨c.out,allSeeds _ c.out_eq,c.out_eq,by simp [sdiff_eq_empty_iff_subset.mpr around]⟩

/-- A shore opposite x in a join decomposition of its connected component. -/
structure Shore (c : G.ConnectedComponent) (x : V) (B : Finset V) : Prop where
  inside : ∀ v ∈ B, v ∈ c.supp
  inhabited : B.Nonempty
  opposite : x ∉ B
  cross : ∀ a ∈ c.supp, a ∉ B → ∀ b ∈ B, G.Adj a b

/-- Each nonsingleton component is a join, with no hereditary restriction on its shores. -/
def ComponentJoins : Prop := ∀ (c : G.ConnectedComponent) (x : V), x ∈ c.supp →
  (∀ v ∈ c.supp, v = x) ∨ ∃ B, Shore G c x B

/-- A join of two nonempty shores, with arbitrary induced graphs on both. -/
def ProperJoin {U : Type*} (H : SimpleGraph U) : Prop :=
  ∃ (A : U → Prop) (a b : U), A a ∧ ¬ A b ∧ ∀ u v, A u → ¬ A v → H.Adj u v

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem of_component_splits
    (splits : ∀ c : G.ConnectedComponent, Nontrivial c.supp → ProperJoin (G.induce c.supp)) :
    ComponentJoins G := by
  classical
  intro c x xc
  by_cases one : ∀ v ∈ c.supp, v = x
  · exact Or.inl one
  right
  push_neg at one
  obtain ⟨z,zc,ne⟩ := one
  have nontriv : Nontrivial c.supp := ⟨⟨z,zc⟩,⟨x,xc⟩,fun e => ne (congrArg Subtype.val e)⟩
  obtain ⟨P,a,d,pa,pd,edges⟩ := splits c nontriv
  obtain ⟨A,b,ha,hb,cross⟩ : ∃ (A : c.supp → Prop) (b : c.supp), A ⟨x,xc⟩ ∧ ¬ A b ∧
      ∀ u v, A u → ¬ A v → (G.induce c.supp).Adj u v := by
    by_cases h : P ⟨x,xc⟩
    · exact ⟨P,d,h,pd,edges⟩
    · exact ⟨fun v => ¬ P v,a,h,not_not_intro pa,fun u v hu hv => (edges v u (not_not.mp hv) hu).symm⟩
  let B := univ.filter (fun v : V => ∃ h : v ∈ c.supp, ¬ A ⟨v,h⟩)
  have mem {v : V} : v ∈ B ↔ ∃ h : v ∈ c.supp, ¬ A ⟨v,h⟩ := by simp [B]
  refine ⟨B,fun v hv => (mem.mp hv).choose,⟨b,mem.mpr ⟨b.property,hb⟩⟩,?_,?_⟩
  · rintro hx
    exact (mem.mp hx).choose_spec ha
  · intro u hu hn v hv
    have hA : A ⟨u,hu⟩ := by by_contra h; exact hn (mem.mpr ⟨hu,h⟩)
    obtain ⟨h,notA⟩ := mem.mp hv
    exact cross ⟨u,hu⟩ ⟨v,h⟩ hA notA

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem cograph_component_joins (hg : CographRadius.Cograph G) : ComponentJoins G := by
  classical
  apply of_component_splits
  intro c inst
  letI : Nontrivial c.supp := inst
  letI : Fintype c.supp := Fintype.ofFinite _
  have hereditary : CographRadius.Cograph (G.induce c.supp) := by
    rintro ⟨f,edges⟩
    exact hg ⟨f.trans (Function.Embedding.subtype _),edges⟩
  let x : c.supp := ⟨c.out,c.out_eq⟩
  obtain ⟨A,y,hx,hy,cross⟩ := CographRadius.join_at _ c.connected_induce_supp hereditary x
  exact ⟨A,x,y,hx,hy,cross⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem observed_mono {S T : Finset V} (h : S ⊆ T) {v : V} (see : Observed G S v) :
    Observed G T v := by
  induction see with
  | root hv => exact .root (h hv)
  | neighbor hw e => exact .neighbor (h hw) e
  | force adj _ _ ih ihs => exact .force adj ih ihs

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every vertex on a shore of order at most two is a single power seed for the component. -/
theorem small_shore {c : G.ConnectedComponent} {x : V} (xc : x ∈ c.supp)
    {B : Finset V} (shore : Shore G c x B) (bound : B.card ≤ 2)
    {y : V} (hy : y ∈ B) : ∀ v ∈ c.supp, Observed G {y} v := by
  classical
  have across (v : V) (vc : v ∈ c.supp) (hv : v ∉ B) : Observed G {y} v :=
    .neighbor (mem_singleton_self y) (shore.cross v vc hv y hy)
  intro v vc
  by_cases vb : v ∈ B
  · by_cases eq : v = y
    · exact .root (mem_singleton.mpr eq)
    apply Observed.force (shore.cross x xc shore.opposite v vb).symm (across x xc shore.opposite)
    intro w xw wv
    have wc := (c.mem_supp_congr_adj xw).mp xc
    by_cases wb : w ∈ B
    · have few : (B.erase v).card ≤ 1 := by rw [card_erase_of_mem vb]; omega
      have wy := card_le_one.mp few w (mem_erase.mpr ⟨wv,wb⟩) y (mem_erase.mpr ⟨Ne.symm eq,hy⟩)
      exact .root (mem_singleton.mpr wy)
    · exact across w wc wb
  · exact across v vc vb

end CographForcing188
