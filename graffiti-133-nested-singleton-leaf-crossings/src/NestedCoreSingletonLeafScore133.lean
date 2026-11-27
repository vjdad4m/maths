import NestedCoreSingletonGate133
import NestedCoreGateScore133
import NestedCoreC7CrossBudget133

namespace Graffiti133NestedSingleGate
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133ExteriorSlack
  Graffiti133NestedCore Graffiti133MultiWeighted
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

private theorem induced_deg_at_most (T : Finset V) (x : (T : Set V)) :
    (G.induce (T : Set V)).degree x≤G.degree x.val := by
  classical
  rw [←(G.induce (T : Set V)).card_neighborFinset_eq_degree,←G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro y ym
    exact (G.mem_neighborFinset _ _).mpr
      ((G.induce (T : Set V)).mem_neighborFinset _ _ |>.mp ym)
  · exact Subtype.val_injective.injOn

theorem arbitrary_singleton_leaf_crossings_preserve_score
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    (K : Finset V) (u v : V) (leaf : V→Prop)
    (split : ∀ x∉K,leaf x ∨ Remote H x)
    (leaflow : ∀ z,leaf z → G.degree z≤2)
    (leafsite : ∀ z,leaf z → Outside H.c z ∧ ∃ i,∀ k,G.Adj z (H.c k)↔k=i)
    (leafunique : ∀ z,leaf z → ∀ r s,Remote H r → Remote H s →
      G.Adj r z → G.Adj s z → r=s)
    (touched : ∀ r∉K,Remote H r → ∃ z,leaf z ∧ G.Adj r z)
    (gated : ∀ r∉K,Remote H r → ∀ w∈K,G.Adj r w → w=u ∨ w=v) :
    (∑ w : V,localIndependence G w)+4*K.card≤
      (∑ w : (K : Set V),localIndependence (G.induce (K : Set V)) w)+4*Fintype.card V := by
  classical
  have noRemote (r : V) (rK : r∉K) (rr : Remote H r) (s : V) (sr : Remote H s) :
      ¬G.Adj r s := by
    intro e
    obtain ⟨z,zl,rz⟩ := touched r rK rr
    obtain ⟨zo,i,zi⟩ := leafsite z zl
    have sz := remote_neighbor_must_share_singleton_gate H h9 zo rr sr i zi rz e
    exact e.ne (leafunique z zl r s rr sr rz sz)
  apply peeling_preserves_ambient_score K h4
  intro T kt ne
  have tk : ¬T⊆K := fun rev=>ne (Finset.Subset.antisymm rev kt)
  obtain ⟨x,xt,xk⟩ := Finset.not_subset.mp tk
  let J := G.induce (T : Set V)
  by_cases has : ∃ z∈T,z∉K ∧ leaf z
  · obtain ⟨z,zt,zk,zl⟩ := has
    let zz : (T : Set V) := ⟨z,zt⟩
    refine ⟨zz,zk,?_⟩
    have bd := (induced_deg_at_most (G:=G) T zz).trans (leaflow z zl)
    omega
  · have xr : Remote H x := (split x xk).resolve_left (fun xl=>has ⟨x,xt,xk,xl⟩)
    let xx : (T : Set V) := ⟨x,xt⟩
    let N := J.neighborFinset xx
    have alt (w : (T : Set V)) (wm : w∈N) : w.val=u ∨ w.val=v := by
      have e : G.Adj x w.val := (J.mem_neighborFinset _ _).mp wm
      by_cases wk : w.val∈K
      · exact gated x xk xr _ wk e
      · have wr : Remote H w.val := (split w.val wk).resolve_left
          (fun wl=>has ⟨w.val,w.property,wk,wl⟩)
        exact (noRemote x xk xr w.val wr e).elim
    have sub : N.image Subtype.val⊆({u,v}:Finset V) := by
      intro w wm
      obtain ⟨z,zm,rfl⟩ := Finset.mem_image.mp wm
      simpa using alt z zm
    have cap := Finset.card_le_card sub
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at cap
    have up := Finset.card_insert_le (s:=({v}:Finset V)) (a:=u)
    rw [Finset.card_singleton] at up
    have bound : N.card≤2 := by omega
    refine ⟨xx,xk,?_⟩
    change 2*J.degree xx ≤ 4+3*triangleIncidence J xx
    have d : N.card=J.degree xx := J.card_neighborFinset_eq_degree xx
    omega

theorem C7_base_with_unlimited_singleton_leaf_crossings_mean_four
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    (K : Finset V) (cy : ∀ i,H.c i∈K)
    (dom : ∀ y : (K : Set V),Outside (restrictedHole H K cy).c y →
      ∃ i,(G.induce (K : Set V)).Adj y ((restrictedHole H K cy).c i))
    (baseMultis : (Graffiti133MultiC7.multiVertices (restrictedHole H K cy)).card≤4)
    (u v : V) (leaf : V→Prop)
    (split : ∀ x∉K,leaf x ∨ Remote H x)
    (leaflow : ∀ z,leaf z → G.degree z≤2)
    (leafsite : ∀ z,leaf z → Outside H.c z ∧ ∃ i,∀ k,G.Adj z (H.c k)↔k=i)
    (leafunique : ∀ z,leaf z → ∀ r s,Remote H r → Remote H s →
      G.Adj r z → G.Adj s z → r=s)
    (touched : ∀ r∉K,Remote H r → ∃ z,leaf z ∧ G.Adj r z)
    (gated : ∀ r∉K,Remote H r → ∀ w∈K,G.Adj r w → w=u ∨ w=v) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  have preserve := arbitrary_singleton_leaf_crossings_preserve_score H h4 h9 K u v leaf
    split leaflow leafsite leafunique touched gated
  have base := C7_dominating_slack_depending_on_multis (restrictedHole H K cy)
    (restricted_c4 h4 K) (retained_no_path h9 K) dom
  have card : Fintype.card (K : Set V)=K.card := Fintype.card_coe K
  rw [card] at base
  have aux {l b k n m : Nat} (bd : b+14≤4*k+3*m) (m4 : m≤4)
      (pr : l+4*k≤b+4*n) : l≤4*n := by omega
  exact aux base baseMultis preserve

#print axioms C7_base_with_unlimited_singleton_leaf_crossings_mean_four
#print axioms arbitrary_singleton_leaf_crossings_preserve_score
end Graffiti133NestedSingleGate
