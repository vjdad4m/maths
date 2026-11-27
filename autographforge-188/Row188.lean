import Components
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace CographForcing188
open Finset SimpleGraph ForcingDrop711 AutoGraphPowerBurning
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance : DecidableEq G.ConnectedComponent := Classical.decEq _
noncomputable local instance : Fintype G.ConnectedComponent :=
  Fintype.ofSurjective G.connectedComponentMk (fun c => c.exists_rep)

/-- Replace a two-forcing seed set by a power-dominating set using at most two
vertices per component and never more than that component originally contained. -/
theorem convert_components (joins : ComponentJoins G) {S : Finset V} (hS : full G 2 S) :
    ∃ D : Finset V, (∀ v, Observed G D v) ∧
      ∀ c : G.ConnectedComponent, (D.filter (fun v => G.connectedComponentMk v = c)).card ≤
        min 2 (S.filter (fun v => G.connectedComponentMk v = c)).card := by
  classical
  let seed (c : G.ConnectedComponent) := S.filter (fun v => G.connectedComponentMk v = c)
  have localSeed (c : G.ConnectedComponent) : ∃ T : Finset V,
      (∀ v ∈ T, v ∈ c.supp) ∧ T.card ≤ min 2 (seed c).card ∧
      ∀ v ∈ c.supp, Observed G T v := by
    obtain ⟨x,hx,xc,cap⟩ := active_in_component G hS c
    have inSeed : x ∈ seed c := mem_filter.mpr ⟨hx,xc⟩
    have pos : 0 < (seed c).card := card_pos.mpr ⟨x,inSeed⟩
    have one : 1 ≤ min 2 (seed c).card := le_min (by decide) pos
    rcases joins c x xc with only|⟨B,shore⟩
    · refine ⟨{x},?_,by simpa using one,fun v hv => .root (mem_singleton.mpr (only v hv))⟩
      intro v h
      rwa [mem_singleton.mp h]
    obtain ⟨y,hy⟩ := shore.inhabited
    by_cases few : (seed c).card ≤ 1
    · have allWhite : B ⊆ G.neighborFinset x \ S := by
        intro z hz
        refine mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr (shore.cross x xc shore.opposite z hz),?_⟩
        intro hs
        have same := card_le_one.mp few z (mem_filter.mpr ⟨hs,shore.inside z hz⟩) x inSeed
        exact shore.opposite (same ▸ hz)
      refine ⟨{y},?_,by simpa using one,small_shore G xc shore ((card_le_card allWhite).trans cap) hy⟩
      intro v h
      exact mem_singleton.mp h ▸ shore.inside y hy
    · refine ⟨{x,y},?_,le_min card_le_two (card_le_two.trans (by omega)),?_⟩
      · intro v h
        rcases mem_insert.mp h with rfl|h
        · exact xc
        · exact mem_singleton.mp h ▸ shore.inside y hy
      · intro v vc
        by_cases vb : v ∈ B
        · exact .neighbor (mem_insert_self _ _) (shore.cross x xc shore.opposite v vb).symm
        · exact .neighbor (mem_insert_of_mem (mem_singleton_self y)) (shore.cross v vc vb y hy)
  choose T inside sizes good using localSeed
  let D := univ.biUnion T
  have sub (c : G.ConnectedComponent) : T c ⊆ D := subset_biUnion_of_mem T (mem_univ c)
  refine ⟨D,fun v => observed_mono G (sub _) (good (G.connectedComponentMk v) v rfl),?_⟩
  intro c
  refine (card_le_card ?_).trans (sizes c)
  intro v hv
  obtain ⟨mem,vc⟩ := mem_filter.mp hv
  obtain ⟨d,_,hd⟩ := mem_biUnion.mp mem
  have eq : d = c := (show G.connectedComponentMk v = d from inside d v hd).symm.trans vc
  exact eq ▸ hd

theorem comparison (joins : ComponentJoins G) : power G ≤ forcing G 2 := by
  classical
  obtain ⟨S,minimum,hs⟩ := attained G 2
  obtain ⟨D,see,parts⟩ := convert_components G joins hs
  have count (T : Finset V) : T.card =
      ∑ c : G.ConnectedComponent, (T.filter (fun v => G.connectedComponentMk v = c)).card :=
    card_eq_sum_card_fiberwise (s:=T) (t:=univ) (f:=G.connectedComponentMk) (fun _ _ => mem_univ _)
  have cost : D.card ≤ S.card := by
    rw [count D,count S]
    exact sum_le_sum (fun c _ => (parts c).trans (min_le_right _ _))
  exact (Nat.sInf_le (s := {r | ∃ T : Finset V, r = T.card ∧ ∀ v, Observed G T v})
    ⟨D,rfl,see⟩).trans (cost.trans_eq minimum)

theorem row188 (_hn : 2 ≤ Fintype.card V) (hg : CographRadius.Cograph G) :
    power G ≤ forcing G 2 := comparison G (cograph_component_joins G hg)

#print axioms active_in_component
#print axioms small_shore
#print axioms convert_components
#print axioms comparison
#print axioms row188
end CographForcing188
