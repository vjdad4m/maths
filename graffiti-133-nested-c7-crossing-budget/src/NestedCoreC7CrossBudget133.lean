import NestedCoreGateScore133
import C7MultiWeightedGlobal133
import C7MultiWeightedLocal133

namespace Graffiti133NestedCore
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133ExteriorSlack
  Graffiti133MultiWeighted Graffiti133BicycleCharge Graffiti133MultiC7
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
variable {V : Type*} [Fintype V] [LinearOrder V] {G : SimpleGraph V}

private theorem incidence_classical_eq {W : Type*} [Fintype W]
    (J : SimpleGraph W) [d : DecidableEq W] [a : DecidableRel J.Adj] (y : W) :
    @triangleIncidence W _ (fun u v=>Classical.propDecidable (u=v)) J
      (fun u v=>Classical.propDecidable (J.Adj u v)) y = triangleIncidence J y := by
  have hd : (fun u v : W=>Classical.propDecidable (u=v)) = d := Subsingleton.elim _ _
  have ha : (fun u v : W=>Classical.propDecidable (J.Adj u v)) = a := Subsingleton.elim _ _
  cases hd
  cases ha
  rfl

private theorem row_is_any_degree {W : Type*} [Fintype W]
    (J : SimpleGraph W) [a : DecidableRel J.Adj] (y : W) :
    row J y Finset.univ = J.degree y := by
  have ha : (fun u v : W=>Classical.propDecidable (J.Adj u v)) = a := Subsingleton.elim _ _
  cases ha
  exact row_is_degree y

private theorem uniform_multi_charge (H : Hole G 7) (h4 : FourCycleFree G)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i))
    (U : Finset V) (y : (U : Set V)) (cy : ∀ i,H.c i∈U)
    (md : y.val∈multiVertices H) :
    2*(G.induce (U : Set V)).degree y+0≤4+3*triangleIncidence (G.induce (U : Set V)) y+3 := by
  classical
  let J := G.induce (U : Set V)
  let HR := restrictedHole H U cy
  have eq : contactSet HR y=contactSet H y.val := restricted_contacts H U cy y
  have out : Outside HR.c y := fun i e=>(Finset.mem_filter.mp md).2.1 i (congrArg Subtype.val e)
  have localDom (z : (U : Set V)) (zo : Outside HR.c z) :
      ∃ i,J.Adj z (HR.c i) := dom z.val (fun i e=>zo i (Subtype.ext e))
  have two : 2≤(contactSet HR y).card := by rw [eq]; exact (Finset.mem_filter.mp md).2.2
  have loc := local_multi_weight HR (restricted_c4 h4 U) localDom y out two
  rw [row_is_any_degree (G.induce (U:Set V)) y,incidence_classical_eq (G.induce (U:Set V)) y] at loc
  have aux {d t : Nat} (a b : Prop) [Decidable a] [Decidable b]
      (h : 2*d+(if a then 1 else 0)≤4+3*t+(if a then 0 else if b then 3 else 2)) :
      2*d+0≤4+3*t+3 := by
    by_cases aa : a <;> by_cases bb : b <;> simp [aa,bb] at h <;> omega
  exact aux _ _ loc

theorem C7_dominating_slack_depending_on_multis (H : Hole G 7)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (dom : ∀ y,Outside H.c y→∃ i,G.Adj y (H.c i)) :
    (∑ v : V,localIndependence G v)+14 ≤ 4*Fintype.card V+3*(multiVertices H).card := by
  have h := sum_local_plus_custom_slack H h4 h9 dom (fun _=>0) (fun _=>3) (uniform_multi_charge H h4 dom)
  simpa [Nat.mul_comm] using h

theorem C7_nested_two_gate_crossing_budget_mean_four (K : Finset V) (u v : V)
    (uv : u≠v) (um : u∈K) (vm : v∈K) (h4 : FourCycleFree G)
    (H : Hole (G.induce (K : Set V)) 7)
    (h9 : ¬∃ p : Fin 9→(K : Set V),InducedPath (G.induce (K : Set V)) p)
    (dom : ∀ y,Outside H.c y→∃ i,(G.induce (K : Set V)).Adj y (H.c i))
    (sees : ∀ x∉K,G.Adj u x ∨ G.Adj v x)
    (budget : 3*(multiVertices H).card+2*(G.edgeFinset \ (gateTrim G K u v).edgeFinset).card≤14) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  have base := C7_dominating_slack_depending_on_multis H (restricted_c4 h4 K) h9 dom
  have card : Fintype.card (K : Set V)=K.card := Fintype.card_coe K
  rw [card] at base
  apply gate_trim_crossing_slack K u v uv um vm h4 sees
  have aux {l k m d : Nat} (b : l+14≤4*k+3*m) (c : 3*m+2*d≤14) :
      l+2*d≤4*k := by omega
  exact aux base budget

theorem C7_nested_two_multis_four_crossings_mean_four (K : Finset V) (u v : V)
    (uv : u≠v) (um : u∈K) (vm : v∈K) (h4 : FourCycleFree G)
    (H : Hole (G.induce (K : Set V)) 7)
    (h9 : ¬∃ p : Fin 9→(K : Set V),InducedPath (G.induce (K : Set V)) p)
    (dom : ∀ y,Outside H.c y→∃ i,(G.induce (K : Set V)).Adj y (H.c i))
    (sees : ∀ x∉K,G.Adj u x ∨ G.Adj v x)
    (mul : (multiVertices H).card≤2)
    (cr : (G.edgeFinset \ (gateTrim G K u v).edgeFinset).card≤4) :
    (∑ w : V,localIndependence G w)≤4*Fintype.card V := by
  apply C7_nested_two_gate_crossing_budget_mean_four K u v uv um vm h4 H h9 dom sees
  omega

#print axioms C7_nested_two_gate_crossing_budget_mean_four
#print axioms C7_nested_two_multis_four_crossings_mean_four
#print axioms C7_dominating_slack_depending_on_multis
end Graffiti133NestedCore
