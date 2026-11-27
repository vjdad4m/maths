import OuterForest
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Cast.Order

/-! AutoGraphForge normalized physical row 821, ID 961f5019.
The connected bound follows from Desormeaux, Haynes and Henning (2014).
We give a direct degree-sum proof and check both source diameter conventions. -/

namespace ForestSlater

open SimpleGraph Finset
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The two definitions used for AutoGraphForge row 33. -/
noncomputable def degreesDesc := (univ.val.map (fun v => G.degree v)).sort (· ≥ ·)

noncomputable def slater : ℕ :=
  sInf {s | Fintype.card V ≤ s + ((degreesDesc G).take s).sum}

private theorem prefix_bound (l : List ℕ) (s : ℕ) :
    (l.take s).sum ≤ 2*s + (l.map (· - 2)).sum := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    cases s with
    | zero => simp
    | succ s =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      have := ih s
      omega

private theorem slater_capacity :
    Fintype.card V ≤ 3 * slater G + ∑ v, (G.degree v - 2) := by
  have feasible : ({s | Fintype.card V ≤ s + ((degreesDesc G).take s).sum} : Set ℕ).Nonempty :=
    ⟨Fintype.card V, Nat.le_add_right _ _⟩
  have h : Fintype.card V ≤ slater G + ((degreesDesc G).take (slater G)).sum :=
    Nat.sInf_mem feasible
  have excess : ((degreesDesc G).map (· - 2)).sum = ∑ v, (G.degree v - 2) := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, degreesDesc, Multiset.sort_eq, Multiset.map_map]
    rfl
  have upper := prefix_bound (degreesDesc G) (slater G)
  rw [excess] at upper
  omega

private theorem tree_mass (ht : G.IsTree) (hn : 2 ≤ Fintype.card V) :
    (∑ v, (G.degree v - 1)) + 2 = Fintype.card V := by
  classical
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hn
  have pos (v : V) : 0 < G.degree v := by
    obtain ⟨u, hu⟩ := exists_ne v
    obtain ⟨p⟩ := ht.isConnected v u
    exact (G.degree_pos_iff_exists_adj v).mpr
      ⟨p.getVert 1, by simpa using p.adj_getVert_succ (i := 0) (by cases p <;> simp_all)⟩
  have sums := Finset.sum_congr (s₁ := (univ : Finset V)) rfl
    (f := fun v => (G.degree v - 1) + 1) (g := fun v => G.degree v)
    (fun v _ => Nat.sub_add_cancel (pos v))
  simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one] at sums
  have handshake := G.sum_degrees_eq_twice_card_edges
  have edges := ht.card_edgeFinset
  omega

/-- Each internal vertex of a simple path contributes one unit in addition
to its excess above degree two. -/
private theorem path_internal_budget {x y : V} (p : G.Walk x y) (hp : p.IsPath) :
    (∑ v, (G.degree v - 2)) + (p.length - 1) ≤ ∑ v, (G.degree v - 1) := by
  classical
  let S := (Ioo 0 p.length).image p.getVert
  have cardS : S.card = p.length - 1 := by
    rw [show S.card = _ from Finset.card_image_of_injOn (by
      intro i hi j hj
      exact hp.getVert_injOn (Finset.mem_Ioo.mp hi).2.le (Finset.mem_Ioo.mp hj).2.le)]
    simp
  have inner (v : V) (hv : v ∈ S) : 2 ≤ G.degree v := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hl, hr⟩ := Finset.mem_Ioo.mp hi
    have h := hp.ncard_neighborSet_toSubgraph_internal_eq_two (i := i) (by omega) hr
    have hsub : p.toSubgraph.neighborSet (p.getVert i) ⊆ G.neighborSet (p.getVert i) :=
      fun _ e => p.toSubgraph.adj_sub e
    have hle := Set.ncard_le_ncard hsub
    rw [h] at hle
    simpa [Set.ncard_eq_toFinset_card', SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter] using hle
  have budget := Finset.sum_le_sum (s := (univ : Finset V))
    (f := fun v => (G.degree v - 2) + (if v ∈ S then 1 else 0))
    (g := fun v => G.degree v - 1) (fun v _ => by
      dsimp only
      split
      · rename_i hv
        have := inner v hv
        omega
      · omega)
  simpa [sum_add_distrib, cardS] using budget

/-- A forest of order at least two has at most n−2 units of degree above one.
Each nonsingleton component contributes its order minus two. -/
private theorem forest_mass (ha : G.IsAcyclic) (hn : 2 ≤ Fintype.card V) :
    (∑ v, (G.degree v - 1)) + 2 ≤ Fintype.card V := by
  classical
  by_cases connected : G.Connected
  · exact (tree_mass G ⟨connected, ha⟩ hn).le
  letI : Fintype G.ConnectedComponent := Fintype.ofSurjective G.connectedComponentMk
    (fun c => ⟨c.out, c.out_eq⟩)
  haveI : Nontrivial G.ConnectedComponent := by
    apply not_subsingleton_iff_nontrivial.mp
    intro h
    haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    exact connected ⟨fun x y => ConnectedComponent.eq.mp (h.elim _ _)⟩
  have splitSum (f : V → ℕ) :
      (∑ v, f v) = ∑ c : G.ConnectedComponent, ∑ x : c.supp, f x := by
    let e : (Σ c : G.ConnectedComponent, c.supp) ≃ V := Equiv.sigmaFiberEquiv G.connectedComponentMk
    exact (e.sum_comp f).symm.trans (Fintype.sum_sigma _)
  have component (c : G.ConnectedComponent) :
      (∑ v : c.supp, (G.degree v.val - 1)) + 1 ≤ Fintype.card c.supp := by
    let T := G.induce c.supp
    let inc : T ↪g G := Embedding.induce c.supp
    have ht : T.IsTree := ⟨c.connected_induce_supp, fun _ p hp => ha (p.map inc.toHom) (hp.map inc.injective)⟩
    have degree (v : c.supp) : T.degree v = G.degree v.val :=
      degree_induce_of_neighborSet_subset <| fun _ e => (c.mem_supp_congr_adj e).mp v.property
    simp_rw [← degree]
    by_cases big : 2 ≤ Fintype.card c.supp
    · have := tree_mass T ht big
      omega
    · have zero (x : c.supp) : T.degree x - 1 = 0 := by
        have := T.degree_lt_card_verts x
        omega
      have := Fintype.card_pos_iff.mpr ht.isConnected.nonempty
      simpa [zero] using this
  have all := Finset.sum_le_sum (s := (univ : Finset G.ConnectedComponent))
    (fun c _ => component c)
  have cnt := splitSum (fun _ => 1)
  simp only [sum_const, card_univ, smul_eq_mul, mul_one] at cnt
  simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one] at all
  rw [← splitSum (fun v => G.degree v - 1), ← cnt] at all
  have := Fintype.one_lt_card (α := G.ConnectedComponent)
  omega

theorem forest_path_bound (ha : G.IsAcyclic) (hn : 2 ≤ Fintype.card V)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) :
    p.length + 1 ≤ 3 * slater G := by
  have := slater_capacity G
  have := forest_mass G ha hn
  have := path_internal_budget G p hp
  omega

theorem tree_path_bound (ht : G.IsTree) (hn : 2 ≤ Fintype.card V)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) :
    p.length + 1 ≤ 3 * slater G := by
  exact forest_path_bound G ht.IsAcyclic hn p hp

noncomputable def diameter (G : SimpleGraph V) := univ.sup (fun x => univ.sup (G.dist x))

theorem row821_connected (hn : 2 ≤ Fintype.card V) (hc : G.Connected)
    (hb : G.Colorable 2) (hh : AutoGraphForge370.Chordal G) :
    (diameter G : ℤ) ≤ 3 * (slater G : ℤ) - 1 := by
  have tree : G.IsTree := ⟨hc, AutoGraphForge370.forest_of_bipartite_chordal hb hh⟩
  have bound (x y : V) : G.dist x y + 1 ≤ 3 * slater G := by
    obtain ⟨p, hp⟩ := (hc x y).exists_isPath
    have := tree_path_bound G tree hn p hp
    have := SimpleGraph.dist_le p
    omega
  obtain ⟨x⟩ := hc.nonempty
  have := bound x x
  have upper : diameter G ≤ 3 * slater G - 1 := by
    apply Finset.sup_le
    intro u _
    apply Finset.sup_le
    intro v _
    have := bound u v
    omega
  omega

/-- On graphs of order at least two, GraphCalc exposes a numeric diameter
exactly when NetworkX finds the graph connected. -/
noncomputable def graphCalcDiameter (G : SimpleGraph V) : Option ℕ := by
  classical
  exact if G.Connected then some (diameter G) else none

theorem row821_graphcalc (hn : 2 ≤ Fintype.card V) (hb : G.Colorable 2)
    (hh : AutoGraphForge370.Chordal G) {d : ℕ} (hd : graphCalcDiameter G = some d) :
    (d : ℤ) ≤ 3 * (slater G : ℤ) - 1 := by
  classical
  unfold graphCalcDiameter at hd
  split at hd
  · rename_i hc
    cases hd
    exact row821_connected G hn hc hb hh
  · contradiction

/-- The separate AutoGraphForge Python wrapper returns positive infinity
for every disconnected graph. -/
noncomputable def sourceDiameter (G : SimpleGraph V) : WithTop ℚ := by
  classical
  exact if G.Connected then ((diameter G : ℚ) : WithTop ℚ) else ⊤

theorem two_isolates_slater : slater (⊥ : SimpleGraph (Fin 2)) = 2 := by
  let H : SimpleGraph (Fin 2) := ⊥
  have zero (i : ℕ) (hi : i ∈ degreesDesc H) : i = 0 := by
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp ((Multiset.mem_sort (· ≥ ·)).mp hi)
    exact SimpleGraph.bot_degree v
  have sumZero (l : List ℕ) (h : ∀ i ∈ l, i = 0) : l.sum = 0 := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp [h a (List.mem_cons_self ..), ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]
  have z (s : ℕ) : ((degreesDesc H).take s).sum = 0 :=
    sumZero _ (fun i hi => zero i (List.mem_of_mem_take hi))
  change sInf {s | Fintype.card (Fin 2) ≤ s + ((degreesDesc H).take s).sum} = 2
  simp only [z, add_zero, Fintype.card_fin]
  exact csInf_Ici

theorem row821_infinity_counterexample :
    let H : SimpleGraph (Fin 2) := ⊥
    2 ≤ Fintype.card (Fin 2) ∧ H.Colorable 2 ∧ AutoGraphForge370.Chordal H ∧
      ¬ sourceDiameter H ≤ ((3 * (slater H : ℚ) - 1 : ℚ) : WithTop ℚ) := by
  dsimp only
  refine ⟨by decide, ⟨⟨fun v => v, fun {a b} e => False.elim e⟩⟩,
    fun _ p hp _ => False.elim (SimpleGraph.isAcyclic_bot p hp), ?_⟩
  rw [sourceDiameter, if_neg SimpleGraph.bot_not_connected]
  exact WithTop.not_top_le_coe _

#print axioms forest_path_bound
#print axioms tree_path_bound
#print axioms row821_connected
#print axioms row821_graphcalc
#print axioms two_isolates_slater
#print axioms row821_infinity_counterexample

end ForestSlater
