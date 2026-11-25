/- Graffiti.pc #241. The closed neighborhood of the degree-two set has c components; total domination needs at least c+1 vertices. A tree's central-pair distance average is at most one. If there is only one center, the empty distinct-pair mean is taken to be zero.
Official catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/
AI-assisted work, no priority claim. -/

/- Reproduce with Lean 4.19.0 and Mathlib v4.19.0: run this source with lake env lean. -/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Rat.Floor

/- Proof module: Proof271 -/

open Finset
open scoped BigOperators

namespace Graffiti271

abbrev TotalDominates {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ u ∈ D, G.Adj v u

theorem sum_mono_nat {I : Type*} (s : Finset I) (f g : I → ℕ)
    (h : ∀ i ∈ s, f i ≤ g i) : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Nat.add_le_add (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

section General
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

omit [Fintype V] in
theorem dist_step (hc : G.Connected) {root u v : V} (h : G.Adj u v) :
    G.dist root v ≤ G.dist root u + 1 := by
  have hs : G.dist u v = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h
  simpa [hs] using (hc.dist_triangle (u := root) (v := u) (w := v))

omit [Fintype V] in
theorem walk_intermediate (hc : G.Connected) {root u v : V} (p : G.Walk u v)
    {k : ℕ} (h1 : G.dist root u ≤ k) (h2 : k ≤ G.dist root v) :
    ∃ z : V, G.dist root z = k := by
  induction p with
  | nil => exact ⟨_, Nat.le_antisymm h1 h2⟩
  | @cons u w v adj p ih =>
    by_cases hl : G.dist root w ≤ k
    · exact ih hl h2
    · have hs := dist_step G hc (root := root) adj
      exact ⟨u, by omega⟩

theorem card_le_of_spread (S : Finset ℕ) (l : ℕ)
    (h : ∀ x ∈ S, ∀ y ∈ S, y ≤ x+l) : S.card ≤ l+1 := by
  by_cases hn : S.Nonempty
  · have hm := h (S.min' hn) (S.min'_mem hn) (S.max' hn) (S.max'_mem hn)
    have hs : S ⊆ Finset.Icc (S.min' hn) (S.max' hn) := by
      intro x hx
      exact Finset.mem_Icc.mpr ⟨S.min'_le x hx, S.le_max' x hx⟩
    have hc := Finset.card_le_card hs
    rw [Nat.card_Icc] at hc
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

omit [Fintype V] in
theorem component_distance (D : Finset V)
    (c : (G.induce (D : Set V)).ConnectedComponent) [Fintype c.supp]
    (u v : c.supp) :
    G.dist u.1.1 v.1.1 < Fintype.card c.supp := by
  classical
  obtain ⟨p, hp, hdist⟩ := c.connected_induce_supp.exists_path_of_dist u v
  let f := (SimpleGraph.Embedding.induce (G := G.induce (D : Set V)) c.supp).toHom
  let g := (SimpleGraph.Embedding.induce (G := G) (D : Set V)).toHom
  have hd := SimpleGraph.dist_le (p.map (g.comp f))
  have hl := hp.length_lt
  simp only [SimpleGraph.Walk.length_map] at hd
  exact hd.trans_lt hl

/-- If every vertex of a connected graph has a neighbor in D, its distance
    layers can be covered by the distance intervals of the components of D. -/
theorem dist_of_totalDominates (hc : G.Connected) (D : Finset V)
    (hD : TotalDominates G D) (r s : V) :
    G.dist r s + 1 ≤ D.card + 2*(D.card/2) := by
  classical
  let H := G.induce (D : Set V)
  let Q := H.ConnectedComponent
  letI : Finite Q := Finite.of_surjective H.connectedComponentMk (fun c => c.exists_rep)
  letI : Fintype Q := Fintype.ofFinite Q
  let fs (c : Q) : Finset (↥(D : Set V)) :=
    (Finset.univ : Finset (↥(D : Set V))).filter (fun u => H.connectedComponentMk u = c)
  let S (c : Q) : Finset ℕ :=
    (Finset.univ.filter (fun z : V => ∃ u : c.supp, G.Adj z u.1.1)).image (G.dist r)
  have card_eq (c : Q) : Fintype.card c.supp = (fs c).card := by
    apply Fintype.card_of_subtype
    intro u
    simp [fs, SimpleGraph.ConnectedComponent.mem_supp_iff]
  have cap (c : Q) : (S c).card ≤ (fs c).card+2 := by
    apply card_le_of_spread (S c) ((fs c).card+1)
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨u, hu⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨v, hv⟩ := (Finset.mem_filter.mp hb).2
    have h1 := dist_step G hc (root := r) hu
    have h2 := dist_step G hc (root := r) hv.symm
    have h3 := hc.dist_triangle (u := r) (v := u.1.1) (w := v.1.1)
    have h4 := component_distance G D c u v
    rw [card_eq] at h4
    omega
  have card_fibers : ∑ c : Q, (fs c).card = D.card := by
    symm
    simpa [fs] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (↥(D : Set V)))) (t := (Finset.univ : Finset Q))
        (f := H.connectedComponentMk) (fun _ _ => Finset.mem_univ _))
  have min_fiber (c : Q) : 2 ≤ (fs c).card := by
    obtain ⟨u, hu⟩ := c.exists_rep
    obtain ⟨v, hv, huv⟩ := hD u.1
    let v' : ↥(D : Set V) := ⟨v,hv⟩
    have hc' : H.connectedComponentMk v' = c := by
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj (show H.Adj u v' from huv)).symm.trans hu
    have hu' : u ∈ fs c := by simpa [fs] using hu
    have hv' : v' ∈ fs c := by simpa [fs] using hc'
    exact Finset.one_lt_card.mpr ⟨u,hu',v',hv',fun h => huv.ne (congrArg Subtype.val h)⟩
  have qcap : 2 * Fintype.card Q ≤ D.card := by
    calc
      _ = ∑ _c : Q, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ c : Q, (fs c).card := sum_mono_nat _ _ _ (fun c _ => min_fiber c)
      _ = _ := card_fibers
  have cover : Finset.range (G.dist r s+1) ⊆ (Finset.univ : Finset Q).biUnion S := by
    intro d hd
    have hi : d ≤ G.dist r s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    obtain ⟨w, _⟩ := hc.exists_walk_length_eq_dist r s
    obtain ⟨z, hz⟩ := walk_intermediate G hc (root := r) w
      (by simp [SimpleGraph.dist_self]) hi
    obtain ⟨u, hu, hzu⟩ := hD z
    let u' : ↥(D : Set V) := ⟨u,hu⟩
    let c : Q := H.connectedComponentMk u'
    have hu' : u' ∈ c.supp := by simp [c, SimpleGraph.ConnectedComponent.mem_supp_iff]
    apply Finset.mem_biUnion.mpr
    refine ⟨c, Finset.mem_univ _, Finset.mem_image.mpr ⟨z, ?_, hz⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨u',hu'⟩,hzu⟩⟩
  calc
    G.dist r s+1 = (Finset.range (G.dist r s+1)).card := by simp
    _ ≤ ((Finset.univ : Finset Q).biUnion S).card := Finset.card_le_card cover
    _ ≤ ∑ c : Q, (S c).card := Finset.card_biUnion_le
    _ ≤ ∑ c : Q, ((fs c).card+2) := sum_mono_nat _ _ _ (fun c _ => cap c)
    _ = D.card+2*Fintype.card Q := by
      rw [Finset.sum_add_distrib, card_fibers]
      simp [Nat.mul_comm]
    _ ≤ _ := by omega

noncomputable def nbr (x : V) : Finset V := by
  classical
  exact Finset.univ.filter (G.Adj x)

@[simp] theorem mem_nbr {x y : V} : y ∈ nbr G x ↔ G.Adj x y := by
  classical
  simp [nbr]

def MaximumDegree (x : V) : Prop := ∀ y : V, (nbr G y).card ≤ (nbr G x).card

theorem max_degree_distance_pair (hc : G.Connected) (D : Finset V)
    (hD : TotalDominates G D) (h2 : D.card = 2)
    {x y : V} (hx : MaximumDegree G x) (hy : MaximumDegree G y) :
    G.dist x y ≤ 2 := by
  classical
  obtain ⟨u,v, _, rfl⟩ := Finset.card_eq_two.mp h2
  have hcover : nbr G u ∪ nbr G v = Finset.univ := by
    ext w
    simp only [Finset.mem_union, mem_nbr, Finset.mem_univ, iff_true]
    obtain ⟨z,hz,hwz⟩ := hD w
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Or.inl hwz.symm
    · exact Or.inr hwz.symm
  have hnm : Fintype.card V ≤ (nbr G x).card + (nbr G y).card := by
    have he := Finset.card_union_le (s := nbr G u) (t := nbr G v)
    rw [hcover, Finset.card_univ] at he
    have h1 := hx u
    have h2' := hy v
    omega
  by_contra! hf
  have hxy : ¬ G.Adj x y := fun hx => by
    have hh := SimpleGraph.dist_eq_one_iff_adj.mpr hx
    omega
  have hdis : Disjoint (nbr G x) (nbr G y) := by
    apply Finset.disjoint_left.mpr
    intro z hzx hzy
    have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr (mem_nbr G |>.mp hzx)
    have h2' := SimpleGraph.dist_eq_one_iff_adj.mpr (mem_nbr G |>.mp hzy).symm
    have ht := hc.dist_triangle (u := x) (v := z) (w := y)
    omega
  have hproper : nbr G x ∪ nbr G y ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
    intro he
    have hm : x ∈ nbr G x ∪ nbr G y := he ▸ Finset.mem_univ x
    have hn := Finset.mem_union.mp hm
    rcases hn with hn | hn
    · exact G.loopless x (mem_nbr G |>.mp hn)
    · exact hxy (mem_nbr G |>.mp hn).symm
  have hcd := Finset.card_lt_card hproper
  rw [Finset.card_union_of_disjoint hdis, Finset.card_univ] at hcd
  omega

theorem perDominatingSet (hc : G.Connected) (D : Finset V)
    (hD : TotalDominates G D) {x y : V} (hx : MaximumDegree G x)
    (hy : MaximumDegree G y) :
    2 * G.dist x y ≤ D.card^2 := by
  have ht : 2 ≤ D.card := by
    obtain ⟨u,hu,_⟩ := hD x
    obtain ⟨v,hv,huv⟩ := hD u
    exact Finset.one_lt_card.mpr ⟨u,hu,v,hv,huv.ne⟩
  have hd := dist_of_totalDominates G hc D hD x y
  by_cases h2 : D.card = 2
  · have h := max_degree_distance_pair G hc D hD h2 hx hy
    rw [h2]
    omega
  by_cases h3 : D.card = 3
  · rw [h3] at hd ⊢
    change 2 * G.dist x y ≤ 9
    omega
  let a := D.card-4
  have ha : D.card=a+4 := by dsimp [a]; omega
  calc
    2*G.dist x y ≤ 8*a+16 := by omega
    _ ≤ a*a+(8*a+16) := by omega
    _ = D.card^2 := by rw [ha, pow_two]; simp only [Nat.add_mul,Nat.mul_add]; omega

noncomputable def totalDominationNumber : ℕ :=
  sInf {k : ℕ | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}

/-- Graffiti.pc #271, in integer form, pointwise over all pairs of maximum-degree vertices.
    For a finite graph this is equivalent to the maximum-distance form of the catalogue. -/
theorem graffiti271 (hc : G.Connected) (hV : 2 ≤ Fintype.card V)
    {x y : V} (hx : MaximumDegree G x) (hy : MaximumDegree G y) :
    2 * G.dist x y ≤ (totalDominationNumber G)^2 := by
  classical
  have hall : TotalDominates G Finset.univ := by
    intro v
    obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v w
    have hz : 0 < p.length := by
      rw [hp]
      exact hc.pos_dist_of_ne hw.symm
    exact ⟨p.getVert 1, Finset.mem_univ _, by simpa using p.adj_getVert_succ (i := 0) hz⟩
  have hnon : {k : ℕ | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}.Nonempty :=
    ⟨Fintype.card V, Finset.univ, hall, Finset.card_univ⟩
  obtain ⟨D, hD, hcard⟩ := Nat.sInf_mem hnon
  rw [totalDominationNumber, ← hcard]
  exact perDominatingSet G hc D hD hx hy

/-- Maximum graph distance across the set of maximum-degree vertices. -/
noncomputable def maxDegreeDistance : ℕ := by
  classical
  let M := (Finset.univ : Finset V).filter (MaximumDegree G)
  exact (M.product M).sup (fun p => G.dist p.1 p.2)

theorem graffiti271_max_squared (hc : G.Connected) (hV : 2 ≤ Fintype.card V) :
    2 * maxDegreeDistance G ≤ (totalDominationNumber G)^2 := by
  classical
  have h : maxDegreeDistance G ≤ (totalDominationNumber G)^2 / 2 := by
    unfold maxDegreeDistance
    apply Finset.sup_le
    intro p hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    have ht := graffiti271 G hc hV (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
    omega
  omega

/-- The nonnegative integer ceiling of a square root, characterized by minimality. -/
noncomputable def ceilSqrt (n : ℕ) : ℕ :=
  Nat.find (show ∃ k : ℕ, n ≤ k^2 from ⟨n, by simpa [pow_two] using Nat.le_mul_self n⟩)

theorem ceilSqrt_spec (n : ℕ) : n ≤ (ceilSqrt n)^2 := by
  unfold ceilSqrt
  exact Nat.find_spec (p := fun k : ℕ => n ≤ k^2) _

theorem ceilSqrt_le {n k : ℕ} (h : n ≤ k^2) : ceilSqrt n ≤ k := Nat.find_le h

/-- The catalogue's exact maximum-and-ceiling form of Graffiti.pc #271. -/
theorem graffiti271_exact (hc : G.Connected) (hV : 2 ≤ Fintype.card V) :
    ceilSqrt (2 * maxDegreeDistance G) ≤ totalDominationNumber G :=
  ceilSqrt_le (graffiti271_max_squared G hc hV)

#print axioms dist_of_totalDominates
#print axioms graffiti271_exact

end General
end Graffiti271

/- Proof module: ConnectedCore -/

open Finset
open SimpleGraph
open Graffiti271

namespace GraffitiCore

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

private theorem finiteComponents {W : Type*} [Finite W] (H : SimpleGraph W) :
    Finite H.ConnectedComponent :=
  Finite.of_surjective H.connectedComponentMk (fun c => c.exists_rep)

noncomputable def componentCount (D : Finset V) : ℕ :=
  @Fintype.card _ (@Fintype.ofFinite _ (finiteComponents (G.induce (D : Set V))))

omit [Fintype V] in
theorem walk_has_change {K : Type*} (f : V → K) {x y : V}
    (p : G.Walk x y) (hxy : f x ≠ f y) :
    ∃ a b, G.Adj a b ∧ f a ≠ f b := by
  classical
  induction p with
  | nil => exact (hxy rfl).elim
  | @cons x z y hadj p ih =>
    by_cases h : f x = f z
    · exact ih (fun he => hxy (h.trans he))
    · exact ⟨x,z,hadj,h⟩

theorem components_le_half (D : Finset V) (hD : TotalDominates G D) :
    componentCount G D ≤ D.card / 2 := by
  classical
  let H := G.induce (D : Set V)
  letI := finiteComponents H
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let fs (c : H.ConnectedComponent) : Finset (↥(D : Set V)) :=
    Finset.univ.filter (fun u => H.connectedComponentMk u = c)
  have card_fibers : ∑ c : H.ConnectedComponent, (fs c).card = D.card := by
    symm
    simpa [fs] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (↥(D : Set V)))) (t := Finset.univ)
        (f := H.connectedComponentMk) (fun _ _ => Finset.mem_univ _))
  have min_fiber (c : H.ConnectedComponent) : 2 ≤ (fs c).card := by
    obtain ⟨u, hu⟩ := c.exists_rep
    obtain ⟨v, hv, huv⟩ := hD u.1
    let v' : ↥(D : Set V) := ⟨v,hv⟩
    have hc' : H.connectedComponentMk v' = c :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        (show H.Adj u v' from huv)).symm.trans hu
    have hu' : u ∈ fs c := by simpa [fs] using hu
    have hv' : v' ∈ fs c := by simpa [fs] using hc'
    exact Finset.one_lt_card.mpr ⟨u,hu',v',hv',fun h => huv.ne (congrArg Subtype.val h)⟩
  have h : 2 * Fintype.card H.ConnectedComponent ≤ D.card := by
    calc
      _ = ∑ _c : H.ConnectedComponent, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ c : H.ConnectedComponent, (fs c).card :=
        sum_mono_nat _ _ _ (fun c _ => min_fiber c)
      _ = _ := card_fibers
  change Fintype.card H.ConnectedComponent ≤ _
  omega

theorem extend_one (hc : G.Connected) (D : Finset V) (hD : TotalDominates G D)
    (hq : 1 < componentCount G D) :
    ∃ E : Finset V, D ⊆ E ∧ E.card ≤ D.card+2 ∧
      componentCount G E < componentCount G D := by
  classical
  let H := G.induce (D : Set V)
  letI := finiteComponents H
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  have hn : 1 < Fintype.card H.ConnectedComponent := by
    simpa [componentCount, H] using hq
  obtain ⟨c, c', hne⟩ := Fintype.one_lt_card_iff.mp hn
  obtain ⟨x, hx⟩ := c.exists_rep
  obtain ⟨y, hy⟩ := c'.exists_rep
  let dom (v : V) : ↥(D : Set V) :=
    if h : v ∈ D then ⟨v,h⟩ else ⟨(hD v).choose, (hD v).choose_spec.1⟩
  have dom_mem (u : ↥(D : Set V)) : dom u.1 = u := by simp [dom, u.2]
  let cl (v : V) := H.connectedComponentMk (dom v)
  have hcl : cl x.1 ≠ cl y.1 := by
    change H.connectedComponentMk (dom x.1) ≠ H.connectedComponentMk (dom y.1)
    rw [dom_mem, dom_mem]
    change H.connectedComponentMk x = c at hx
    change H.connectedComponentMk y = c' at hy
    rw [hx,hy]
    exact hne
  obtain ⟨p⟩ := hc x.1 y.1
  obtain ⟨a,b,hab,hneq⟩ := walk_has_change G cl p hcl
  let E := insert a (insert b D)
  have hsub : D ⊆ E := by intro z hz; simp [E,hz]
  let J := G.induce (E : Set V)
  letI := finiteComponents J
  letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
  let inc : H →g J := (G.induceHomOfLE (show (D : Set V) ≤ (E : Set V) from hsub)).toHom
  let f : H.ConnectedComponent → J.ConnectedComponent :=
    fun c0 => c0.map inc
  have hpath (v : ↥(E : Set V)) : J.Reachable (inc (dom v.1)) v := by
    by_cases hv : v.1 ∈ D
    · have he : inc (dom v.1) = v := by
        apply Subtype.ext
        change (dom v.1).1 = v.1
        simp [dom, hv]
      rw [he]
    · have hh : G.Adj (dom v.1).1 v.1 := by
        have h := (hD v.1).choose_spec.2.symm
        simpa [dom, hv] using h
      exact (show J.Adj (inc (dom v.1)) v from hh).reachable
  have hsurj : Function.Surjective f := by
    intro k
    obtain ⟨v, hv⟩ := k.exists_rep
    refine ⟨H.connectedComponentMk (dom v.1), ?_⟩
    change J.connectedComponentMk (inc (dom v.1)) = k
    exact (ConnectedComponent.sound (hpath v)).trans hv
  have ha : a ∈ E := by simp [E]
  have hb : b ∈ E := by simp [E]
  let ea : ↥(E : Set V) := ⟨a,ha⟩
  let eb : ↥(E : Set V) := ⟨b,hb⟩
  have hnoninj : ¬ Function.Injective f := by
    intro hi
    apply hneq
    apply hi
    change J.connectedComponentMk (inc (dom a)) = J.connectedComponentMk (inc (dom b))
    exact ConnectedComponent.sound ((hpath ea).trans
      ((show J.Adj ea eb from hab).reachable.trans (hpath eb).symm))
  have hlt := Fintype.card_lt_of_surjective_not_injective f hsurj hnoninj
  refine ⟨E, hsub, ?_, ?_⟩
  · have h1 := Finset.card_insert_le a (insert b D)
    have h2 := Finset.card_insert_le b D
    dsimp [E]
    omega
  · simpa [componentCount, J, H] using hlt

theorem induced_connected_of_componentCount_le_one (D : Finset V)
    (hn : D.Nonempty) (hq : componentCount G D ≤ 1) :
    (G.induce (D : Set V)).Connected := by
  classical
  let H := G.induce (D : Set V)
  letI := finiteComponents H
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  have h : Fintype.card H.ConnectedComponent ≤ 1 := by
    simpa [componentCount, H] using hq
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  obtain ⟨v, hv⟩ := hn
  refine ⟨⟨v,hv⟩, fun w => ConnectedComponent.exact ?_⟩
  exact (Fintype.card_le_one_iff.mp h) _ _

theorem exists_connected_core (hc : G.Connected) (D : Finset V)
    (hD : TotalDominates G D) :
    ∃ E : Finset V, D ⊆ E ∧ (G.induce (E : Set V)).Connected ∧
      E.card ≤ D.card + 2 * (componentCount G D - 1) := by
  classical
  generalize hq : componentCount G D = q
  induction q using Nat.strong_induction_on generalizing D with
  | h q ih =>
    have hn : D.Nonempty := by
      obtain ⟨v⟩ := hc.nonempty
      obtain ⟨u,hu,_⟩ := hD v
      exact ⟨u,hu⟩
    by_cases hsmall : q ≤ 1
    · exact ⟨D, Finset.Subset.refl _, induced_connected_of_componentCount_le_one
        G D hn (hq ▸ hsmall), by omega⟩
    · obtain ⟨E,hsub,hcard,hlt⟩ := extend_one G hc D hD (by omega)
      have hE : TotalDominates G E := by
        intro v
        obtain ⟨u,hu,hvu⟩ := hD v
        exact ⟨u,hsub hu,hvu⟩
      obtain ⟨F,hsubF,hcon,hcardF⟩ := ih _ (by omega) E hE rfl
      have hpos : 0 < componentCount G E := by
        let J := G.induce (E : Set V)
        letI := finiteComponents J
        obtain ⟨v,hv⟩ := hn
        letI : Nonempty J.ConnectedComponent := ⟨J.connectedComponentMk ⟨v,hsub hv⟩⟩
        letI : Fintype J.ConnectedComponent := Fintype.ofFinite _
        change 0 < Fintype.card J.ConnectedComponent
        exact Fintype.card_pos
      exact ⟨F, hsub.trans hsubF, hcon, by omega⟩

#print axioms exists_connected_core
end GraffitiCore

/- Proof module: LeavesCore -/

open Finset SimpleGraph Graffiti271 GraffitiCore
namespace GraffitiLeaves

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

noncomputable def leafSet (T : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => (nbr T v).card = 1)

noncomputable def maxLeaves : ℕ := by
  classical
  exact ((Finset.univ : Finset (SimpleGraph V)).filter
    (fun T => T ≤ G ∧ T.IsTree)).sup (fun T => (leafSet T).card)

theorem leaf_card_le_maxLeaves {T : SimpleGraph V} (hle : T ≤ G) (hT : T.IsTree) :
    (leafSet T).card ≤ maxLeaves G := by
  classical
  unfold maxLeaves
  exact Finset.le_sup (f := fun T => (leafSet T).card) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hle,hT⟩)

omit [Fintype V] in
theorem adj_exists_of_connected {x y : V} (h : G.Connected) (hne : x ≠ y) :
    ∃ w : V, G.Adj x w := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist x y
  have hz : 0 < p.length := by rw [hp]; exact h.pos_dist_of_ne hne
  exact ⟨p.getVert 1, by simpa using p.adj_getVert_succ (i := 0) hz⟩

/-- Every vertex outside a connected dominating set can simultaneously be a leaf
    of a single spanning tree. -/
theorem complement_card_le_maxLeaves (D : Finset V)
    (hd : TotalDominates G D) (hD : (G.induce (D : Set V)).Connected) :
    Fintype.card V - D.card ≤ maxLeaves G := by
  classical
  let par (v : V) := (hd v).choose
  have hpar (v : V) : par v ∈ D ∧ G.Adj v (par v) := (hd v).choose_spec
  let H : SimpleGraph V :=
    { Adj := fun u v => G.Adj u v ∧
        ((u ∈ D ∧ v ∈ D) ∨ (u ∉ D ∧ par u = v) ∨ (v ∉ D ∧ par v = u))
      symm := by
        intro u v h
        obtain ⟨huv, h | h | h⟩ := h
        · exact ⟨huv.symm, Or.inl h.symm⟩
        · exact ⟨huv.symm, Or.inr (Or.inr h)⟩
        · exact ⟨huv.symm, Or.inr (Or.inl h)⟩
      loopless := fun u h => G.loopless u h.1 }
  let inc : G.induce (D : Set V) →g H :=
    ⟨fun v => v.1, fun {a b} h => ⟨h,Or.inl ⟨a.2,b.2⟩⟩⟩
  let lift (v : V) : ↥(D : Set V) :=
    if h : v ∈ D then ⟨v,h⟩ else ⟨par v,(hpar v).1⟩
  have reach (v : V) : H.Reachable v (lift v).1 := by
    by_cases h : v ∈ D
    · have he : (lift v).1 = v := by simp [lift,h]
      rw [he]
    · have he : (lift v).1 = par v := by simp [lift,h]
      rw [he]
      exact (show H.Adj v (par v) from ⟨(hpar v).2, Or.inr (Or.inl ⟨h,rfl⟩)⟩).reachable
  have hH : H.Connected := by
    have : Nonempty V := ⟨(Classical.choice hD.nonempty).1⟩
    refine ⟨fun u v => ?_⟩
    exact (reach u).trans (((hD (lift u) (lift v)).map inc).trans (reach v).symm)
  obtain ⟨T, hT, ht⟩ := hH.exists_isTree_le
  have hTG : T ≤ G := fun _ _ h => (hT h).1
  have hleaf : (Finset.univ : Finset V) \ D ⊆ leafSet T := by
    intro v hv
    have hn : v ∉ D := (Finset.mem_sdiff.mp hv).2
    have hpne : v ≠ par v := fun h => hn (h ▸ (hpar v).1)
    obtain ⟨z,hz⟩ := adj_exists_of_connected T ht.isConnected hpne
    have single {w : V} (h : T.Adj v w) : w = par v := by
      have h' := (hT h).2
      rcases h' with h' | h' | h'
      · exact (hn h'.1).elim
      · exact h'.2.symm
      · exact (hn (h'.2 ▸ (hpar w).1)).elim
    have hs : nbr T v = {par v} := by
      ext w
      simp only [mem_nbr, Finset.mem_singleton]
      refine ⟨single, fun h => ?_⟩
      rwa [h, ← single hz]
    simp [leafSet, hs]
  have hcount := Finset.card_le_card hleaf
  rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ] at hcount
  exact hcount.trans (leaf_card_le_maxLeaves G hTG ht)

theorem domination_leaves_bound
    (hc : G.Connected) (D : Finset V) (hd : TotalDominates G D) :
    Fintype.card V ≤ maxLeaves G + D.card + 2 * (D.card / 2 - 1) := by
  obtain ⟨E,hsub,hcon,hcard⟩ := exists_connected_core G hc D hd
  have he : TotalDominates G E := by
    intro v
    obtain ⟨u,hu,ha⟩ := hd v
    exact ⟨u,hsub hu,ha⟩
  have ht := complement_card_le_maxLeaves G E he hcon
  have hcc := components_le_half G D hd
  omega

#print axioms domination_leaves_bound
end GraffitiLeaves

/- Proof module: BFS -/

open Finset SimpleGraph Graffiti271 GraffitiLeaves
namespace GraffitiBFS
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

omit [Fintype V] in
theorem one_step_toward (hc : G.Connected) (r v : V) (h : v ≠ r) :
    ∃ z, G.Adj v z ∧ G.dist r z + 1 = G.dist r v := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v r
  have hpos : 0 < p.length := by rw [hp]; exact hc.pos_dist_of_ne h
  have hn : ¬ p.Nil := SimpleGraph.Walk.not_nil_iff_lt_length.mpr hpos
  have h1 : G.Adj v (p.getVert 1) := by simpa using p.adj_getVert_succ (i := 0) hpos
  have h2 := SimpleGraph.dist_le p.tail
  rw [SimpleGraph.dist_comm] at h2
  change G.dist r (p.getVert 1) ≤ p.tail.length at h2
  have h3 := p.length_tail_add_one hn
  rw [hp, SimpleGraph.dist_comm] at h3
  have h4 := dist_step G hc (root := r) h1.symm
  exact ⟨_, h1, by omega⟩

/-- Rooted shortest-path parent relation, producing an actual spanning tree. -/
theorem exists_bfs_tree (hc : G.Connected) (r : V) :
    ∃ (par : V → V) (T : SimpleGraph V),
      T ≤ G ∧ T.IsTree ∧
      (∀ v, v ≠ r → G.dist r (par v) + 1 = G.dist r v) ∧
      (∀ u v, T.Adj u v ↔ (u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u)) ∧
      nbr G r = nbr T r := by
  classical
  let par (v : V) : V :=
    if h : v = r then r else (one_step_toward G hc r v h).choose
  have props (v : V) (h : v ≠ r) :
      G.Adj v (par v) ∧ G.dist r (par v) + 1 = G.dist r v := by
    simpa [par, h] using (one_step_toward G hc r v h).choose_spec
  let T : SimpleGraph V :=
    { Adj := fun u v => (u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u)
      symm := fun _ _ => Or.symm
      loopless := by
        intro v h
        have h := h.elim id id
        have e := (props v h.1).2
        rw [h.2] at e
        omega }
  have hsub : T ≤ G := by
    intro u v h
    change (u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u) at h
    rcases h with ⟨h,e⟩ | ⟨h,e⟩
    · rw [← e]
      exact (props u h).1
    · rw [← e]
      exact (props v h).1.symm
  have treeReach : ∀ v, T.Reachable v r := by
    intro v
    generalize h : G.dist r v = d
    induction d using Nat.strong_induction_on generalizing v with
    | h d ih =>
      by_cases he : v = r
      · rw [he]
      · have hlt : G.dist r (par v) < d := by
          have hp := (props v he).2
          omega
        have had : T.Adj v (par v) := Or.inl ⟨he,rfl⟩
        exact had.reachable.trans (ih _ hlt _ rfl)
  have hconn : T.Connected := (connected_iff_exists_forall_reachable _).mpr
      ⟨r,fun v => (treeReach v).symm⟩
  have edgeImage : T.edgeFinset =
      ((Finset.univ : Finset V).erase r).image (fun v => s(v,par v)) := by
    ext e
    refine Sym2.inductionOn e (fun u v => ?_)
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    change ((u ≠ r ∧ par u = v) ∨ (v ≠ r ∧ par v = u)) ↔ _
    constructor
    · rintro (⟨hu,e⟩ | ⟨hv,e⟩)
      · exact Finset.mem_image.mpr ⟨u, by simp [hu], by rw [e]⟩
      · exact Finset.mem_image.mpr ⟨v, by simp [hv], by rw [e,Sym2.eq_swap]⟩
    · intro h
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp h
      have hne := (Finset.mem_erase.mp hw).1
      rcases Sym2.eq_iff.mp he with ⟨hu,hparEq⟩ | ⟨hv,hparEq⟩
      · exact Or.inl ⟨by simpa [hu] using hne, by simpa [hu] using hparEq⟩
      · exact Or.inr ⟨by simpa [hv] using hne, by simpa [hv] using hparEq⟩
  have edgeInj : Set.InjOn (fun v => s(v,par v)) (↑((Finset.univ : Finset V).erase r) : Set V) := by
    intro u hu v hv e
    have hu' := (Finset.mem_erase.mp hu).1
    have hv' := (Finset.mem_erase.mp hv).1
    rcases Sym2.eq_iff.mp e with ⟨h,_⟩ | ⟨h,j⟩
    · exact h
    · have p := (props u hu').2
      have q := (props v hv').2
      rw [← h] at q
      rw [j] at p
      omega
  have htree : T.IsTree := by
    apply isTree_iff_connected_and_card.mpr
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
      edgeImage, Finset.card_image_of_injOn edgeInj]
    have he := Finset.card_erase_add_one (Finset.mem_univ r)
    simpa using he
  have hnbr : nbr G r = nbr T r := by
    ext v
    simp only [mem_nbr]
    refine ⟨fun ha => ?_,fun h => hsub h⟩
    have hd : G.dist r v = 1 := dist_eq_one_iff_adj.mpr ha
    have he := (props v ha.ne.symm).2
    have hz : G.dist r (par v) = 0 := by omega
    exact Or.inr ⟨ha.ne.symm, (hc.dist_eq_zero_iff.mp hz).symm⟩
  exact ⟨par,T,hsub,htree,fun v h => (props v h).2,fun _ _ => Iff.rfl,hnbr⟩

#print axioms exists_bfs_tree
end GraffitiBFS

/- Proof module: DegreesLeaves -/

open Finset SimpleGraph Graffiti271 GraffitiLeaves GraffitiBFS
open scoped BigOperators
namespace GraffitiDegrees
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem deg_pos (hc : G.Connected) (hn : 2 ≤ Fintype.card V) (v : V) :
    0 < (nbr G v).card := by
  obtain ⟨w,hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
  obtain ⟨z,hz⟩ := adj_exists_of_connected G hc hw.symm
  exact Finset.card_pos.mpr ⟨z, (mem_nbr G).mpr hz⟩

theorem handshaking_nbr [DecidableRel G.Adj] :
    (∑ v : V, (nbr G v).card) = 2 * G.edgeFinset.card := by
  classical
  have he (v : V) : (nbr G v).card = G.degree v := by
    change (nbr G v).card = (G.neighborFinset v).card
    rw [SimpleGraph.neighborFinset_eq_filter]
    congr 1
    ext w
    simp
  simp_rw [he]
  exact SimpleGraph.sum_degrees_eq_twice_card_edges G

theorem tree_count (hT : G.IsTree) (hn : 2 ≤ Fintype.card V) (r : V) :
    2 ≤ (leafSet G).card ∧ (nbr G r).card ≤ (leafSet G).card := by
  classical
  let extra (v : V) : ℕ := if v = r then (nbr G r).card-2 else 0
  let base (v : V) : ℕ := if (nbr G v).card = 1 then 1 else 2
  have hbase (v : V) : base v + extra v ≤ (nbr G v).card := by
    have hv := deg_pos G hT.isConnected hn v
    by_cases he : v = r
    · subst v
      by_cases hh : (nbr G r).card = 1
      · simp [base,extra,hh]
      · simp [base,extra,hh]
        omega
    · by_cases hh : (nbr G v).card = 1
      · simp [base,extra,he,hh]
      · simp [base,extra,he,hh]
        omega
  have extr : (∑ v : V, extra v) = (nbr G r).card-2 := by simp [extra]
  have bs (v : V) : base v = 1 + (if (nbr G v).card ≠ 1 then 1 else 0) := by
    by_cases h : (nbr G v).card = 1 <;> simp [base,h]
  have bfs : (∑ v : V, base v) =
      Fintype.card V + (Fintype.card V - (leafSet G).card) := by
    simp_rw [bs, Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul, mul_one,
      Finset.card_univ, ← Finset.sum_filter]
    have hf : (Finset.univ.filter (fun v => (nbr G v).card ≠ 1)) =
        ((Finset.univ : Finset V) \ leafSet G) := by
      ext v
      simp [leafSet]
    rw [hf, Finset.sum_const, Nat.nsmul_eq_mul, mul_one,
      Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ]
  have hsum : Fintype.card V + (Fintype.card V - (leafSet G).card)
      + ((nbr G r).card-2) ≤ 2 * G.edgeFinset.card := by
    rw [← bfs, ← extr, ← Finset.sum_add_distrib, ← handshaking_nbr G]
    exact sum_mono_nat _ _ _ (fun v _ => hbase v)
  have he := hT.card_edgeFinset
  have hls : (leafSet G).card ≤ Fintype.card V := Finset.card_le_univ _
  omega

theorem maxLeaves_ge_degree (hc : G.Connected) (hn : 2 ≤ Fintype.card V) (v : V) :
    (nbr G v).card ≤ maxLeaves G := by
  obtain ⟨par,T,hT,ht,_,_,hnbr⟩ := exists_bfs_tree G hc v
  rw [hnbr]
  exact (tree_count T ht hn v).2.trans (leaf_card_le_maxLeaves G hT ht)

theorem maxLeaves_ge_two (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    2 ≤ maxLeaves G := by
  obtain ⟨v⟩ := hc.nonempty
  obtain ⟨T,hT,ht⟩ := hc.exists_isTree_le
  exact (tree_count T ht hn v).1.trans (leaf_card_le_maxLeaves G hT ht)

#print axioms maxLeaves_ge_degree
end GraffitiDegrees

/- Proof module: Periphery -/

open Finset SimpleGraph Graffiti271 GraffitiLeaves GraffitiDegrees
open scoped BigOperators
namespace GraffitiPeriphery

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

noncomputable def eccentricity (v : V) : ℕ :=
  (Finset.univ : Finset V).sup (G.dist v)

noncomputable def diameter : ℕ := (Finset.univ : Finset V).sup (eccentricity G)

noncomputable def peripheral : Finset V := by
  classical
  exact Finset.univ.filter (fun v => eccentricity G v = diameter G)

noncomputable def peripheralBoundary : Finset V := by
  classical
  exact ((peripheral G).biUnion (nbr G)) \ peripheral G

theorem ecc_bound (x y : V) : G.dist x y ≤ eccentricity G x :=
  Finset.le_sup (f := G.dist x) (Finset.mem_univ y)

theorem diam_bound (x : V) : eccentricity G x ≤ diameter G :=
  Finset.le_sup (f := eccentricity G) (Finset.mem_univ x)

@[simp] theorem mem_peripheral (v : V) :
    v ∈ peripheral G ↔ eccentricity G v = diameter G := by
  classical
  simp [peripheral]

theorem peripheral_card_ge_two (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    2 ≤ (peripheral G).card := by
  classical
  obtain ⟨v⟩ := hc.nonempty
  have he : (Finset.univ : Finset V).Nonempty := ⟨v,Finset.mem_univ v⟩
  obtain ⟨x,_,hx⟩ := Finset.exists_mem_eq_sup _ he (eccentricity G)
  obtain ⟨y,_,hy⟩ := Finset.exists_mem_eq_sup _ he (G.dist x)
  have hx' : diameter G = eccentricity G x := hx
  have hy' : eccentricity G x = G.dist x y := hy
  have hxy : x ≠ y := by
    obtain ⟨w,hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) x
    have h1 := hc.pos_dist_of_ne hw.symm
    have h2 := ecc_bound G x w
    intro he
    have hs : G.dist x y = 0 := by rw [he,SimpleGraph.dist_self]
    omega
  have hD : diameter G ≤ eccentricity G y := by
    rw [hx',hy',SimpleGraph.dist_comm]
    exact ecc_bound G y x
  exact Finset.one_lt_card.mpr ⟨x,(mem_peripheral G x).mpr hx'.symm,
    y,(mem_peripheral G y).mpr (Nat.le_antisymm (diam_bound G y) hD),hxy⟩

theorem boundary_cap (d : ℕ) (hd : ∀ v, (nbr G v).card ≤ d) :
    (peripheralBoundary G).card ≤ d * (peripheral G).card := by
  classical
  have hsub : peripheralBoundary G ⊆ (peripheral G).biUnion (nbr G) := by
    exact Finset.sdiff_subset
  calc
    _ ≤ ((peripheral G).biUnion (nbr G)).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ peripheral G, (nbr G v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ peripheral G, d := sum_mono_nat _ _ _ (fun v _ => hd v)
    _ = _ := by simp [Nat.mul_comm]

theorem boundary_disjoint_cap :
    (peripheralBoundary G).card + (peripheral G).card ≤ Fintype.card V := by
  classical
  have hsub : peripheralBoundary G ⊆ (Finset.univ : Finset V) \ peripheral G := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ] at hcard
  have hc : (peripheral G).card ≤ Fintype.card V := Finset.card_le_univ _
  omega

omit [Fintype V] in
theorem tdcard_ge_two (D : Finset V) (hD : TotalDominates G D) (v : V) :
    2 ≤ D.card := by
  obtain ⟨u,hu,_⟩ := hD v
  obtain ⟨w,hw,huw⟩ := hD u
  exact Finset.one_lt_card.mpr ⟨u,hu,w,hw,huw.ne⟩

theorem periphery_for_D (hc : G.Connected) (hn : 2 ≤ Fintype.card V)
    (D : Finset V) (hD : TotalDominates G D)
    (smallDegreeCase : (∀ v, (nbr G v).card ≤ 2) → (peripheralBoundary G).card ≤ D.card) :
    2 * (peripheralBoundary G).card ≤ D.card * maxLeaves G := by
  obtain ⟨v⟩ := hc.nonempty
  have hcard := tdcard_ge_two G D hD v
  have hL := maxLeaves_ge_two G hc hn
  have hN := domination_leaves_bound G hc D hD
  have hB := peripheral_card_ge_two G hc hn
  have hX := boundary_disjoint_cap G
  by_cases he2 : maxLeaves G = 2
  · have hl : ∀ v, (nbr G v).card ≤ 2 := by
      intro v
      simpa [he2] using maxLeaves_ge_degree G hc hn v
    have := smallDegreeCase hl
    rw [he2]
    omega
  by_cases he3 : maxLeaves G = 3
  · have hl : ∀ v, (nbr G v).card ≤ 3 := by
      intro v
      simpa [he3] using maxLeaves_ge_degree G hc hn v
    have := boundary_cap G 3 hl
    rw [he3] at hN ⊢
    by_cases h : D.card % 2 = 0
    · have : D.card = 2*(D.card/2) := by omega
      omega
    · omega
  · let a := D.card-2
    let b := maxLeaves G-4
    have ha : D.card = a+2 := by dsimp [a]; omega
    have hb : maxLeaves G = b+4 := by dsimp [b]; omega
    calc
      2*(peripheralBoundary G).card ≤ 4*a+2*b+8 := by omega
      _ ≤ a*b + (4*a+2*b+8) := by omega
      _ = D.card * maxLeaves G := by rw [ha,hb]; simp only [Nat.add_mul,Nat.mul_add]; omega

theorem exists_min_td (hc : G.Connected) (hn : 2 ≤ Fintype.card V) :
    ∃ D : Finset V, TotalDominates G D ∧ D.card = totalDominationNumber G := by
  have hall : TotalDominates G Finset.univ := by
    intro v
    obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
    obtain ⟨p, hp⟩ := adj_exists_of_connected G hc hw.symm
    exact ⟨p,Finset.mem_univ _,hp⟩
  have hnon : {k : ℕ | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}.Nonempty :=
    ⟨Fintype.card V, Finset.univ, hall, Finset.card_univ⟩
  exact Nat.sInf_mem hnon

#print axioms periphery_for_D
end GraffitiPeriphery

/- Proof module: Tree232 -/
set_option warningAsError true
set_option linter.unusedSectionVars false
namespace Graffiti232Tree
universe u

variable {V : Type u} [DecidableEq V]

structure Graph (V : Type u) where
  verts : List V
  nodup : verts.Nodup
  complete : ∀ v, v ∈ verts
  edge : V → V → Bool
  symm : ∀ v w, edge v w = true → edge w v = true
  loopless : ∀ v, edge v v = false

def Adj (G : Graph V) (v w : V) : Prop := G.edge v w = true

inductive Walk (G : Graph V) : V → V → Prop
  | nil {v} : Walk G v v
  | cons {u v w} : Adj G u v → Walk G v w → Walk G u w

def Connected (G : Graph V) : Prop := ∀ v w, Walk G v w

def cardinal (G : Graph V) (P : V → Bool) : Nat := (G.verts.filter P).length
def nbrs (G : Graph V) (P : V → Bool) (v : V) : List V :=
  G.verts.filter (fun w => G.edge v w && P w)
def degree (G : Graph V) (v : V) : Nat := (nbrs G (fun _ => true) v).length
def minimumDegreeSet (G : Graph V) (v : V) : Bool :=
  G.verts.all (fun w => decide (degree G v ≤ degree G w))
def leaf (G : Graph V) (v : V) : Bool := decide (degree G v = 1)
def leafNeighbors (G : Graph V) (v : V) : List V := nbrs G (leaf G) v
def support (G : Graph V) (v : V) : Bool := decide (0 < (leafNeighbors G v).length)
def privateNeighbor (G : Graph V) (A : V → Bool) (v : V) : Bool :=
  decide ((nbrs G A v).length = 1)
def TwoIndependent (G : Graph V) (I : V → Bool) : Prop :=
  ∀ v, I v = true → (nbrs G I v).length ≤ 1

theorem choose_le_length (xs ys : List V) (R : V → V → Prop)
    (hnx : xs.Nodup) (hny : ys.Nodup)
    (h : ∀ x ∈ xs, ∃ y ∈ ys, R x y)
    (hu : ∀ x x' y, R x y → R x' y → x = x') : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons a as ih =>
    obtain ⟨y,hy,hay⟩ := h a (List.mem_cons_self ..)
    have htail := (List.nodup_cons.mp hnx)
    have next : ∀ x ∈ as, ∃ z ∈ ys.erase y, R x z := by
      intro x hx
      obtain ⟨z,hz,hxz⟩ := h x (List.mem_cons_of_mem _ hx)
      have hzy : z ≠ y := by
        intro e; subst z
        have e' := hu a x y hay hxz
        exact htail.1 (e' ▸ hx)
      exact ⟨z,(hny.mem_erase_iff).2 ⟨hzy,hz⟩,hxz⟩
    have ih' := ih (ys.erase y) htail.2 (hny.erase y) next
    rw [List.length_erase_of_mem hy] at ih'
    have hpos : 0 < ys.length := by
      cases ys with
      | nil => simp at hy
      | cons _ _ => simp
    simp only [List.length_cons]
    omega

theorem subset_le_length {xs ys : List V}
    (hnx : xs.Nodup) (hny : ys.Nodup) (h : xs ⊆ ys) : xs.length ≤ ys.length := by
  exact choose_le_length xs ys Eq hnx hny
    (fun x hx => ⟨x,h hx,rfl⟩) (fun _ _ _ u v => u.trans v.symm)

theorem count_filter_split (l : List V) (P Q : V → Bool) :
    (l.filter P).length = (l.filter (fun v => P v && Q v)).length
      + (l.filter (fun v => P v && !Q v)).length := by
  simpa only [List.countP_eq_length_filter, List.filter_filter] using
    List.countP_eq_countP_filter_add l P Q

theorem count_filter_comm (l : List V) (P Q : V → Bool) :
    (l.filter (fun v => P v && Q v)).length = (l.filter (fun v => Q v && P v)).length := by
  simp [Bool.and_comm]

theorem filter_nodup {xs : List V} (h : xs.Nodup) (P : V → Bool) :
    (xs.filter P).Nodup := List.filter_sublist.nodup h

theorem two_members {xs : List V} (hd : xs.Nodup) (h : 2 ≤ xs.length) :
    ∃ x ∈ xs, ∃ y ∈ xs, x ≠ y := by
  cases xs with
  | nil => simp at h
  | cons x tail =>
    cases tail with
    | nil => simp at h
    | cons y ys =>
      refine ⟨x,by simp,y,by simp,?_⟩
      intro e; subst y
      exact (List.nodup_cons.mp hd).1 (by simp)

theorem singleton_unique {xs : List V}
    (h : xs.length ≤ 1) {u v} (hu : u ∈ xs) (hv : v ∈ xs) : u = v := by
  cases xs with
  | nil => simp at hu
  | cons a tail =>
    cases tail with
    | nil =>
      have hu' : u = a := by simpa using hu
      have hv' : v = a := by simpa using hv
      exact hu'.trans hv'.symm
    | cons b bs => simp at h

theorem positive_member {xs : List V} (h : 0 < xs.length) : ∃ x, x ∈ xs := by
  cases xs with
  | nil => simp at h
  | cons a tail => exact ⟨a,by simp⟩

theorem member_positive {xs : List V} {x : V} (h : x ∈ xs) : 0 < xs.length := by
  cases xs with
  | nil => simp at h
  | cons a tail => simp

theorem mem_nbrs {G : Graph V} {P : V → Bool} {v w} :
    w ∈ nbrs G P v ↔ Adj G v w ∧ P w = true := by
  simp [nbrs, Adj, G.complete]

theorem leaf_degree {G : Graph V} {v} : leaf G v = true ↔ degree G v = 1 := by
  simp [leaf]

theorem support_has_leaf {G : Graph V} {v} (h : support G v = true) :
    ∃ w, Adj G v w ∧ leaf G w = true := by
  obtain ⟨w,hw⟩ := positive_member (of_decide_eq_true h)
  exact ⟨w,mem_nbrs.mp hw⟩

theorem leaf_unique_neighbor {G : Graph V} {v w z}
    (h : leaf G v = true) (hw : Adj G v w) (hz : Adj G v z) : w = z := by
  have hv : (nbrs G (fun _ => true) v).length = 1 := leaf_degree.mp h
  have hle : (nbrs G (fun _ => true) v).length ≤ 1 := by omega
  exact singleton_unique hle
    (mem_nbrs.mpr ⟨hw,rfl⟩) (mem_nbrs.mpr ⟨hz,rfl⟩)

theorem walk_has_first {G : Graph V} {v w} (h : Walk G v w) (hne : v ≠ w) :
    ∃ z, Adj G v z := by
  cases h with
  | nil => exact False.elim (hne rfl)
  | cons e _ => exact ⟨_,e⟩

theorem degree_pos {G : Graph V} (hcon : Connected G) (hn : 2 < G.verts.length) (v : V) :
    0 < degree G v := by
  obtain ⟨x,_,y,_,hxy⟩ := two_members G.nodup (by omega)
  have hother : ∃ w, v ≠ w := by
    by_cases e : v=x
    · exact ⟨y,e ▸ hxy⟩
    · exact ⟨x,e⟩
  obtain ⟨w,hw⟩ := hother
  obtain ⟨z,hz⟩ := walk_has_first (hcon v w) hw
  exact member_positive (mem_nbrs.mpr ⟨hz,rfl⟩)

theorem leaf_pair_traps_walk {G : Graph V} {x y v w}
    (hx : leaf G x = true) (hy : leaf G y = true) (hxy : Adj G x y)
    (hw : Walk G v w) (hv : v=x ∨ v=y) : w=x ∨ w=y := by
  induction hw with
  | nil => exact hv
  | cons e _ ih =>
    apply ih
    rcases hv with rfl|rfl
    · exact Or.inr (leaf_unique_neighbor hx e hxy)
    · exact Or.inl (leaf_unique_neighbor hy e (G.symm _ _ hxy))

theorem leaf_not_support {G : Graph V} (hcon : Connected G)
    (hn : 2 < G.verts.length) {v} (hl : leaf G v = true) : support G v = false := by
  apply Bool.eq_false_iff.mpr
  intro hs
  obtain ⟨w,hvw,hw⟩ := support_has_leaf hs
  have hne : v ≠ w := by
    intro e; subst w
    have he := G.loopless v
    simp [Adj,he] at hvw
  have hall : G.verts ⊆ [v,w] := by
    intro z _
    have hh := leaf_pair_traps_walk hl hw hvw (hcon v z) (Or.inl rfl)
    simpa using hh
  have hsmall := subset_le_length G.nodup (by simp [List.nodup_cons,hne]) hall
  simp at hsmall
  omega


/-- A simple path recorded by the successive vertices after its start. -/
inductive PathTo (G : Graph V) : V → List V → V → Prop
  | nil {u} : PathTo G u [] u
  | cons {u x v p} : Adj G u x → u ∉ x :: p →
      PathTo G x p v → PathTo G u (x :: p) v

theorem path_single {G : Graph V} {u v} (h : Adj G u v) : PathTo G u [v] v := by
  apply PathTo.cons h _ PathTo.nil
  intro hd
  have he : u = v := by simpa using hd
  subst v
  have hh := G.loopless u
  simp [Adj,hh] at h

theorem path_nodup {G : Graph V} {u p v} (h : PathTo G u p v) :
    (u::p).Nodup := by
  induction h with
  | nil => simp
  | cons _ h _ ih => exact List.nodup_cons.mpr ⟨h,ih⟩

theorem path_endpoint {G : Graph V} {u p v} (h : PathTo G u p v) : v ∈ u::p := by
  induction h with
  | nil => simp
  | cons _ _ _ ih => exact List.mem_cons_of_mem _ ih

theorem path_endpoint_tail {G : Graph V} {u p v} (h : PathTo G u p v) (hne : u≠v) :
    v ∈ p := by
  have hm := path_endpoint h
  exact (List.mem_cons.mp hm).resolve_left (fun he => hne he.symm)

theorem path_empty_endpoint {G : Graph V} {u v} (h : PathTo G u [] v) : u=v := by
  cases h
  rfl

theorem path_to_walk {G : Graph V} {u p v} (h : PathTo G u p v) : Walk G u v := by
  induction h with
  | nil => exact .nil
  | cons e _ _ ih => exact .cons e ih

theorem path_append {G : Graph V} {u p v q w}
    (h : PathTo G u p v) (h' : PathTo G v q w)
    (hd : ∀ t ∈ u::p, t ∉ q) : PathTo G u (p++q) w := by
  induction h with
  | nil => exact h'
  | @cons a x b ps he hu hps ih =>
    apply PathTo.cons he
    · intro hh
      have hh' : a ∈ (x::ps) ++ q := hh
      rcases List.mem_append.mp hh' with hpre|hpost
      · exact hu hpre
      · exact hd a (List.mem_cons_self ..) hpost
    · exact ih h' (fun t ht => hd t (List.mem_cons_of_mem _ ht))

theorem path_reverse {G : Graph V} {u p v} (h : PathTo G u p v) :
    ∃ q, PathTo G v q u ∧ q.length = p.length ∧ ∀ a∈v::q, a∈u::p := by
  induction h with
  | nil => exact ⟨[],.nil,rfl,fun _ h => h⟩
  | @cons a x b ps he hu hps ih =>
    obtain ⟨q,hq,hlen,hsub⟩ := ih
    refine ⟨q++[a],path_append hq (path_single (G.symm _ _ he)) ?_, ?_, ?_⟩
    · intro z hz hm
      have heq : z=a := by simpa using hm
      subst z
      exact hu (hsub _ hz)
    · simp [hlen]
    · intro t ht
      have hmem : t∈(b::q) ++ [a] := ht
      rcases List.mem_append.mp hmem with hmem|hmem
      · exact List.mem_cons_of_mem _ (hsub t hmem)
      · have heq : t=a := by simpa using hmem
        subst t
        simp

theorem path_prefix {G : Graph V} {u p v} (h : PathTo G u p v) {w}
    (hw : w ∈ u::p) : ∃ pre suf, p = pre ++ suf ∧ PathTo G u pre w := by
  induction h with
  | @nil a =>
    have heq : w=a := by simpa using hw
    subst w
    exact ⟨[],[],rfl,.nil⟩
  | @cons a x b ps he hu hps ih =>
    rcases List.mem_cons.mp hw with e|hw'
    · subst w; exact ⟨[],x::ps,rfl,.nil⟩
    · obtain ⟨pre,suf,hcat,hroute⟩ := ih hw'
      refine ⟨x::pre,suf,by simp [hcat],PathTo.cons he ?_ hroute⟩
      intro hmem
      apply hu
      rw [hcat]
      exact List.mem_append_left suf hmem

/-- The classical unique-simple-path presentation of a finite tree. This is
equivalent to a connected undirected simple graph with no cycle. -/
structure Tree (V : Type u) where
  graph : Graph V
  existsPath : ∀ a b : V, ∃ p, PathTo graph a p b
  uniquePath : ∀ a b p q, PathTo graph a p b → PathTo graph a q b → p=q

def TPath (T : Tree V) := PathTo T.graph

noncomputable def chosen (T : Tree V) (a b : V) : List V :=
  Classical.choose (T.existsPath a b)

theorem chosen_path (T : Tree V) (a b : V) : TPath T a (chosen T a b) b :=
  Classical.choose_spec (T.existsPath a b)

theorem tree_connected (T : Tree V) : Connected T.graph := fun a b =>
  path_to_walk (chosen_path T a b)

noncomputable def dist (T : Tree V) (a b : V) : Nat := (chosen T a b).length

theorem dist_eq {T : Tree V} {a p b} (h : TPath T a p b) : dist T a b = p.length := by
  unfold dist
  rw [T.uniquePath _ _ _ _ (chosen_path T _ _) h]

theorem dist_self (T : Tree V) (a : V) : dist T a a = 0 :=
  dist_eq (PathTo.nil : TPath T a [] a)

theorem dist_adj {T : Tree V} {a b} (h : Adj T.graph a b) : dist T a b = 1 :=
  dist_eq (path_single h)

theorem dist_pos {T : Tree V} {a b} (h : a≠b) : 0 < dist T a b := by
  unfold dist
  cases he : chosen T a b with
  | nil =>
    have hi := chosen_path T a b
    rw [he] at hi
    exact False.elim (h (path_empty_endpoint hi))
  | cons x xs => simp

theorem path_different_branches_disjoint {T : Tree V} {u z z' p q a b}
    (hp : TPath T u (z::p) a) (hq : TPath T u (z'::q) b) (hd : z≠z') :
    ∀ w ∈ z::p, w ∉ z'::q := by
  intro w hw hw'
  obtain ⟨pre,suf,hcat,hroute⟩ := path_prefix hp (List.mem_cons_of_mem _ hw)
  obtain ⟨pre',suf',hcat',hroute'⟩ := path_prefix hq (List.mem_cons_of_mem _ hw')
  have he := T.uniquePath _ _ _ _ hroute hroute'
  have hn := (List.nodup_cons.mp (path_nodup hp)).1
  cases hne : pre with
  | nil =>
    rw [hne] at hroute
    have heq := path_empty_endpoint hroute
    subst w
    exact hn hw
  | cons x xs =>
    have heq : z=x := by
      rw [hne] at hcat
      exact (List.cons.inj hcat).1
    rw [← he,hne] at hcat'
    have heq' : z'=x := (List.cons.inj hcat').1
    exact hd (heq.trans heq'.symm)

theorem path_starts_iff_contains_neighbor {T : Tree V} {u z p v}
    (e : Adj T.graph u z) (h : TPath T u p v) (hz : z ∈ p) :
    ∃ q, p = z::q := by
  obtain ⟨pre,suf,hp,hroute⟩ := path_prefix h (List.mem_cons_of_mem _ hz)
  have he := T.uniquePath _ _ _ _ hroute (path_single e)
  rw [he] at hp
  exact ⟨suf,hp⟩

theorem dist_other_branch {T : Tree V} {u z p v x}
    (h : TPath T u (z::p) v)
    (hx : z ∉ chosen T u x) : dist T v x = dist T v u + dist T u x := by
  obtain ⟨q,hq,_,hsub⟩ := path_reverse h
  have hux := chosen_path T u x
  have hdis : ∀ a∈v::q, a∉chosen T u x := by
    intro a ha ham
    have has := hsub a ha
    rcases List.mem_cons.mp has with he|hahas
    · subst a
      exact (List.nodup_cons.mp (path_nodup hux)).1 ham
    · cases hcomp : chosen T u x with
      | nil => rw [hcomp] at ham; contradiction
      | cons w ws =>
        have hh := hux
        rw [hcomp] at hh
        have hzw : z≠w := by
          intro e; subst w
          apply hx; rw [hcomp]; simp
        exact path_different_branches_disjoint h hh hzw _ hahas (hcomp ▸ ham)
  have he := dist_eq (path_append hq hux hdis)
  rw [List.length_append, ← dist_eq hq] at he
  exact he

def maxList (xs : List Nat) : Nat := xs.foldr max 0

theorem maxList_upper {xs : List Nat} {x : Nat} (h : x∈xs) : x≤maxList xs := by
  induction xs with
  | nil => contradiction
  | cons a as ih =>
    rcases List.mem_cons.mp h with e|h
    · subst x; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem maxList_attains {xs : List Nat} (h : xs≠[]) : maxList xs ∈ xs := by
  induction xs with
  | nil => contradiction
  | cons a as ih =>
    cases as with
    | nil => simp [maxList]
    | cons b bs =>
      have hf := ih (by simp)
      change max a (maxList (b::bs)) ∈ a::b::bs
      by_cases he : a ≤ maxList (b::bs)
      · rw [Nat.max_eq_right he]
        exact List.mem_cons_of_mem _ hf
      · rw [Nat.max_eq_left (by omega)]
        simp

noncomputable def eccentricity (T : Tree V) (v : V) : Nat :=
  maxList (T.graph.verts.map (dist T v))

noncomputable def center (T : Tree V) (v : V) : Bool :=
  T.graph.verts.all (fun w => decide (eccentricity T v ≤ eccentricity T w))

theorem ecc_upper (T : Tree V) (v w : V) : dist T v w ≤ eccentricity T v := by
  unfold eccentricity
  exact maxList_upper (List.mem_map.mpr ⟨w,T.graph.complete _,rfl⟩)

theorem ecc_attains (T : Tree V) (v : V) : ∃ w, dist T v w = eccentricity T v := by
  have hn : T.graph.verts.map (dist T v) ≠ [] := by
    intro he
    have he' : dist T v v ∈ T.graph.verts.map (dist T v) :=
      List.mem_map.mpr ⟨v,T.graph.complete _,rfl⟩
    rw [he] at he'; contradiction
  obtain ⟨w,_,hw⟩ := List.mem_map.mp (maxList_attains hn)
  exact ⟨w,hw⟩

theorem center_char {T : Tree V} {v} : center T v = true ↔
    ∀ w, eccentricity T v ≤ eccentricity T w := by
  unfold center
  simp [List.all_eq_true,T.graph.complete]

theorem dist_symm (T : Tree V) (a b : V) : dist T a b = dist T b a := by
  obtain ⟨q,hq,hqLen,_⟩ := path_reverse (chosen_path T a b)
  rw [dist_eq hq,hqLen]
  rfl

theorem distStep {T : Tree V} {u v w} (e : Adj T.graph u v) :
    dist T u w ≤ 1 + dist T v w := by
  by_cases hv : v ∈ chosen T u w
  · obtain ⟨q,hq⟩ := path_starts_iff_contains_neighbor e (chosen_path T u w) hv
    have hp := chosen_path T u w
    rw [hq] at hp
    have htail : TPath T v q w := by cases hp with | cons _ _ h => exact h
    rw [dist_eq hp, dist_eq htail]
    simp [Nat.add_comm]
  · have he := dist_other_branch (path_single e) hv
    rw [dist_adj (T.graph.symm _ _ e)] at he
    omega

theorem distPathTriangle {T : Tree V} {u v p} (hp : TPath T u p v) (w : V) :
    dist T u w ≤ p.length + dist T v w := by
  induction hp with
  | nil => simp
  | @cons u z v p he _ h ih =>
    have hs := distStep (w:=w) he
    simp only [List.length_cons]
    omega

theorem distTriangle (T : Tree V) (u v w : V) :
    dist T u w ≤ dist T u v + dist T v w :=
  distPathTriangle (chosen_path T u v) w

noncomputable def radius (T : Tree V) : Nat :=
  T.graph.verts.foldr (fun u r => min (eccentricity T u) r)
    (maxList (T.graph.verts.map (eccentricity T)))

theorem radiusAttains (T : Tree V) (h : 0 < T.graph.verts.length) :
    (∃ u, eccentricity T u = radius T) ∧ ∀ u, radius T ≤ eccentricity T u := by
  let m := maxList (T.graph.verts.map (eccentricity T))
  have allLe : ∀ u, eccentricity T u ≤ m :=
    fun u => maxList_upper (List.mem_map.mpr ⟨u,T.graph.complete _,rfl⟩)
  have aux : ∀ l : List V, ∀ {a : Nat} (ha : ∃ u, eccentricity T u = a),
      (∃ u, eccentricity T u = l.foldr (fun u r => min (eccentricity T u) r) a) ∧
      (∀ u ∈ l, l.foldr (fun u r => min (eccentricity T u) r) a ≤ eccentricity T u) := by
    intro l
    induction l with
    | nil => intro a ha; exact ⟨ha, by simp⟩
    | cons v l ih =>
      intro a ha
      obtain ⟨⟨w,hw⟩,hb⟩ := ih ha
      constructor
      · by_cases hv : eccentricity T v ≤ l.foldr (fun u r => min (eccentricity T u) r) a
        · exact ⟨v,(Nat.min_eq_left hv).symm⟩
        · exact ⟨w,hw.trans (Nat.min_eq_right (by omega)).symm⟩
      · intro u hu
        cases List.mem_cons.mp hu with
        | inl e => subst u; exact Nat.min_le_left _ _
        | inr e => exact Nat.le_trans (Nat.min_le_right _ _) (hb _ e)
  have hv : T.graph.verts.map (eccentricity T) ≠ [] := by
    obtain ⟨u,hu⟩ := positive_member h
    have hx : eccentricity T u ∈ T.graph.verts.map (eccentricity T) := List.mem_map.mpr ⟨u,hu,rfl⟩
    intro e
    rw [e] at hx
    exact List.not_mem_nil hx
  obtain ⟨u,_,hu⟩ := List.mem_map.mp (maxList_attains hv)
  obtain ⟨he,hp⟩ := aux T.graph.verts ⟨u,hu⟩
  exact ⟨he,fun u => hp u (T.graph.complete u)⟩

theorem longPath (T : Tree V) (h : 0 < T.graph.verts.length) (hr : 0 < radius T) :
    ∃ a b p, TPath T a p b ∧ 2*radius T ≤ p.length+1 := by
  obtain ⟨⟨u,hu⟩,hmin⟩ := radiusAttains T h
  obtain ⟨a,ha⟩ := ecc_attains T u
  have hp := chosen_path T u a
  cases hpa : chosen T u a with
  | nil =>
    have he : dist T u a = 0 := by simp [dist,hpa]
    omega
  | cons z p =>
    rw [hpa] at hp
    have hz : Adj T.graph u z := by cases hp with | cons e _ _ => exact e
    obtain ⟨b,hb⟩ := ecc_attains T z
    have hbase := hmin z
    have haway : z ∉ chosen T u b := by
      intro hzmem
      obtain ⟨q,hq⟩ := path_starts_iff_contains_neighbor hz (chosen_path T u b) hzmem
      have hw := chosen_path T u b
      rw [hq] at hw
      have htail : TPath T z q b := by cases hw with | cons _ _ hh => exact hh
      have h1 := dist_eq hw
      have h2 := dist_eq htail
      have h3 := ecc_upper T u b
      simp only [List.length_cons] at h1
      omega
    have hfar := dist_other_branch hp haway
    have e0 := distStep (w:=b) (T.graph.symm _ _ hz)
    have e1 := dist_symm T a u
    have e2 : dist T a b = (chosen T a b).length := rfl
    exact ⟨a,b,chosen T a b,chosen_path T a b,by omega⟩



open SimpleGraph

noncomputable def fromSimple [Fintype V] (G : SimpleGraph V) : Graph V := by
  classical
  exact {
    verts := Finset.univ.toList,
    nodup := Finset.nodup_toList _,
    complete := by simp,
    edge := fun a b => decide (G.Adj a b),
    symm := by intro a b h; exact decide_eq_true (G.symm (of_decide_eq_true h)),
    loopless := by intro a; simp
  }

theorem adj_iff_simple {G : SimpleGraph V} [Fintype V] {a b} :
    Adj (fromSimple G) a b ↔ G.Adj a b := by
  classical
  simp [Adj,fromSimple]

theorem mapWalk {G : SimpleGraph V} [Fintype V] {a b} (p : G.Walk a b) (h : p.IsPath) :
    PathTo (fromSimple G) a p.support.tail b := by
  induction p with
  | nil => exact .nil
  | @cons a x b e p ih =>
    have hn := (List.nodup_cons.mp h.support_nodup).1
    have ht := h.of_cons
    have he := adj_iff_simple.mpr e
    have htail := ih ht
    have eq : p.support = x :: p.support.tail := by cases p <;> rfl
    change PathTo (fromSimple G) a p.support b
    rw [eq] at hn ⊢
    exact .cons he hn htail

theorem liftWalk {G : SimpleGraph V} [Fintype V] {a p b} (h : PathTo (fromSimple G) a p b) :
    ∃ w : G.Walk a b, w.support = a::p ∧ w.length = p.length ∧ w.IsPath := by
  induction h with
  | nil => exact ⟨.nil,rfl,rfl,by simp⟩
  | @cons a x b p e hn hroute ih =>
    obtain ⟨w,hs,hlen,hp⟩ := ih
    refine ⟨.cons (adj_iff_simple.mp e) w, ?_, ?_, ?_⟩
    · simp [hs]
    · simp [hlen]
    · apply (SimpleGraph.Walk.isPath_def _).mpr
      simp only [Walk.support_cons,hs]
      exact List.nodup_cons.mpr ⟨hn,path_nodup hroute⟩

noncomputable def fromSimpleTree [Fintype V] (G : SimpleGraph V) (h : G.IsTree) : Tree V where
  graph := fromSimple G
  existsPath := fun a b => by
    obtain ⟨w,hw,_⟩ := h.existsUnique_path a b
    exact ⟨w.support.tail,mapWalk w hw⟩
  uniquePath := fun a b p q hp hq => by
    obtain ⟨wp,hwp,_,hpathp⟩ := liftWalk hp
    obtain ⟨wq,hwq,_,hpathq⟩ := liftWalk hq
    obtain ⟨w,_,hw⟩ := h.existsUnique_path a b
    have he := (hw wp hpathp).trans (hw wq hpathq).symm
    rw [he,hwq] at hwp
    exact (List.cons.inj hwp).2.symm

theorem dist_compat [Fintype V] {G : SimpleGraph V} (h : G.IsTree) (a b : V) :
    dist (fromSimpleTree G h) a b = G.dist a b := by
  obtain ⟨p,hp,hl⟩ := h.isConnected.exists_path_of_dist a b
  have hw : TPath (fromSimpleTree G h) a p.support.tail b := mapWalk p hp
  rw [dist_eq hw, List.length_tail, Walk.length_support]
  omega

theorem path_union_support [Fintype V] {G : SimpleGraph V} (h : G.IsTree)
    (r a b : V) :
    ∀ x ∈ a :: chosen (fromSimpleTree G h) a b,
      x ∈ r :: chosen (fromSimpleTree G h) r a ∨
      x ∈ r :: chosen (fromSimpleTree G h) r b := by
  classical
  let T := fromSimpleTree G h
  obtain ⟨wa,hwa,_,_⟩ := liftWalk (chosen_path T r a)
  obtain ⟨wb,hwb,_,_⟩ := liftWalk (chosen_path T r b)
  obtain ⟨wc,hwc,_,hpc⟩ := liftWalk (chosen_path T a b)
  let many := wa.reverse.append wb
  obtain ⟨w,_,hw⟩ := h.existsUnique_path a b
  have he := (hw wc hpc).trans (hw many.bypass many.bypass_isPath).symm
  intro x hx
  change x∈a::chosen T a b at hx
  rw [← hwc,he] at hx
  have hm := many.support_bypass_subset hx
  dsimp [many] at hm
  rw [Walk.support_append, Walk.support_reverse] at hm
  rcases List.mem_append.mp hm with hm|hm
  · left
    rw [← hwa,← List.mem_reverse]
    exact hm
  · right
    rw [← hwb]
    exact List.mem_of_mem_tail hm


theorem path_split {G : Graph V} {a p b} (hp : PathTo G a p b)
    (i : Nat) (hi : i ≤ p.length) :
    ∃ c l r, PathTo G a l c ∧ PathTo G c r b ∧ p=l++r ∧ l.length=i := by
  induction hp generalizing i with
  | @nil a =>
    have h0 : i=0 := by simpa using hi
    exact ⟨a,[],[],.nil,.nil,rfl,h0.symm⟩
  | @cons a x b p e hn hpath ih =>
    cases i with
    | zero => exact ⟨a,[],x::p,.nil,.cons e hn hpath,rfl,rfl⟩
    | succ i =>
      have hi' : i ≤ p.length := by simpa using hi
      obtain ⟨c,l,r,hL,hR,e',hl⟩ := ih i hi'
      have hna : a∉x::l := by
        intro h
        apply hn
        rw [e']
        exact List.mem_append_left r h
      exact ⟨c,x::l,r,.cons e hna hL,hR,by simp [e'],by simp [hl]⟩

theorem reverse_full {G : Graph V} {a p b} (h : PathTo G a p b) :
    ∃ q, PathTo G b q a ∧ b::q = (a::p).reverse := by
  induction h with
  | nil => exact ⟨[],.nil,rfl⟩
  | @cons a x b p e hn hpath ih =>
    obtain ⟨q,hq,hrev⟩ := ih
    have hna : a ∉ b::q := by rw [hrev,List.mem_reverse]; exact hn
    have hs : ∀ w∈b::q, w∉[a] := by
      intro w hw hwa
      have e : w=a := by simpa using hwa
      subst w
      exact hna hw
    refine ⟨q++[a],path_append hq (path_single (G.symm _ _ e)) hs,?_⟩
    change (b::q)++[a] = (a::x::p).reverse
    rw [hrev]
    simp

theorem avoid_opposite_branch {T : Tree V} {r z b p x}
    (h : TPath T r (z::p) b) (hx : z ∉ chosen T r x) :
    ∀ w ∈ r :: chosen T r x, w ∉ z::p := by
  intro w hw
  rcases List.mem_cons.mp hw with e|hmem
  · subst w
    exact (List.nodup_cons.mp (path_nodup h)).1
  · have hP := chosen_path T r x
    cases hQ : chosen T r x with
    | nil =>
      rw [hQ] at hmem
      contradiction
    | cons z' p' =>
      rw [hQ] at hP hmem
      have hne : z' ≠ z := by
        intro e
        subst z'
        exact hx (hQ ▸ List.mem_cons_self ..)
      exact path_different_branches_disjoint hP h hne _ hmem

theorem disjoint_nodup_length_le_card [Fintype V] {xs ys : List V}
    (hx : xs.Nodup) (hy : ys.Nodup) (hd : xs.Disjoint ys) :
    xs.length + ys.length ≤ Fintype.card V := by
  have hh : Disjoint xs.toFinset ys.toFinset := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact hd (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb)
  have h := Finset.card_le_univ (xs.toFinset ∪ ys.toFinset)
  rwa [Finset.card_union_of_disjoint hh,List.toFinset_card_of_nodup hx,
    List.toFinset_card_of_nodup hy] at h

theorem opposite_block_bound [Fintype V] {G : SimpleGraph V} (hG : G.IsTree)
    {r z b : V} {p : List V} {x y : V}
    (h : TPath (fromSimpleTree G hG) r (z::p) b)
    (hx : z ∉ chosen (fromSimpleTree G hG) r x)
    (hy : z ∉ chosen (fromSimpleTree G hG) r y) :
    G.dist x y + (z::p).length + 1 ≤ Fintype.card V := by
  let T := fromSimpleTree G hG
  have hex : (z::p).Nodup := (List.nodup_cons.mp (path_nodup h)).2
  have hpath := path_nodup (chosen_path T x y)
  have hdis : (x::chosen T x y).Disjoint (z::p) := by
    intro w hw
    rcases path_union_support hG r x y w hw with hh|hh
    · exact avoid_opposite_branch h hx _ hh
    · exact avoid_opposite_branch h hy _ hh
  have hsum := disjoint_nodup_length_le_card hpath hex hdis
  have hd : (chosen T x y).length = G.dist x y := dist_compat hG x y
  simp only [List.length_cons] at hsum ⊢
  omega

theorem three_two_same (A B C : Prop) :
    (A ∧ B) ∨ (¬ A ∧ ¬ B) ∨ (A ∧ C) ∨ (¬ A ∧ ¬ C) ∨
    (B ∧ C) ∨ (¬B ∧ ¬C) := by
  classical
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;>
    simp [hA,hB,hC]

/-- Packing lemma for trees: choose a radius minimizer and among three
marked vertices find a pair whose distance plus the radius is at most
the order minus one. Uses a path with at least 2r−1 edges and the two sides
of its central cut. -/
theorem treePacking {W : Type*} [Fintype W] (G : SimpleGraph W) (hG : G.IsTree)
    (a b z : W) : ∃ c : W, ∃ M : Nat, (∀ x, G.dist c x ≤ M) ∧
      M + min (G.dist a b) (min (G.dist a z) (G.dist b z)) + 1 ≤ Fintype.card W := by
  classical
  let T := fromSimpleTree G hG
  have hCard : T.graph.verts.length = Fintype.card W := by
    change (Finset.univ : Finset W).toList.length = Fintype.card W
    simp
  have hN : 0 < T.graph.verts.length := by
    letI : Nonempty W := ⟨a⟩
    rw [hCard]
    exact Fintype.card_pos
  obtain ⟨⟨c,hc⟩,_⟩ := radiusAttains T hN
  refine ⟨c,radius T,?_,?_⟩
  · intro w
    have hd := ecc_upper T c w
    rw [hc,dist_compat hG c w] at hd
    exact hd
  · by_cases hr : 0 < radius T
    · obtain ⟨l,r,p,hp,hq⟩ := longPath T hN hr
      obtain ⟨v,L,R,hL,hR,hLR,hLen⟩ := path_split hp (p.length/2) (by omega)
      have hp1 : 1 ≤ p.length := by omega
      have hLength := congrArg List.length hLR
      rw [List.length_append] at hLength
      cases hhR : R with
      | nil =>
        rw [hhR] at hLength
        simp at hLength
        omega
      | cons w Q =>
        rw [hhR] at hR hLR hLength
        have evw : Adj T.graph v w := by cases hR with | cons e _ _ => exact e
        obtain ⟨L',hL',hRev⟩ := reverse_full hL
        have hBoth : ((l::L)++w::Q).Nodup := by
          have h := path_nodup hp
          rw [hLR] at h
          exact h
        have hwNot : w ∉ v::L' := by
          rw [hRev,List.mem_reverse]
          intro h
          exact (List.nodup_append.mp hBoth).2.2 h (List.mem_cons_self ..)
        have hBack : TPath T w (v::L') l := PathTo.cons (T.graph.symm _ _ evw) hwNot hL'
        have hLL : (v::L').length = L.length+1 := by
          rw [hRev,List.length_reverse]
          rfl
        have right_excludes_left (x : W) (hx : w∈chosen T v x) : v∉chosen T w x := by
          obtain ⟨q,hq⟩ := path_starts_iff_contains_neighbor evw (chosen_path T v x) hx
          have hvx := chosen_path T v x
          rw [hq] at hvx
          have tail : TPath T w q x := by cases hvx with | cons _ _ h => exact h
          have he := T.uniquePath _ _ _ _ (chosen_path T w x) tail
          rw [he]
          intro hv
          exact (List.nodup_cons.mp (path_nodup hvx)).1 (List.mem_cons_of_mem _ hv)
        have bound (x y : W) (he : (w∈chosen T v x ∧ w∈chosen T v y) ∨
                                 (w∉chosen T v x ∧ w∉chosen T v y)) :
            radius T + G.dist x y + 1 ≤ Fintype.card W := by
          rcases he with ht|ht
          · have hd := opposite_block_bound hG hBack
                (right_excludes_left x ht.1) (right_excludes_left y ht.2)
            rw [hLL] at hd
            omega
          · have hd := opposite_block_bound hG hR ht.1 ht.2
            simp only [List.length_cons] at hLength hd
            omega
        rcases three_two_same (w∈chosen T v a) (w∈chosen T v b) (w∈chosen T v z) with
          h|h|h|h|h|h
        · have hb := bound a b (Or.inl h)
          have hm := Nat.min_le_left (G.dist a b) (min (G.dist a z) (G.dist b z))
          omega
        · have hb := bound a b (Or.inr h)
          have hm := Nat.min_le_left (G.dist a b) (min (G.dist a z) (G.dist b z))
          omega
        · have hb := bound a z (Or.inl h)
          have hm := Nat.le_trans (Nat.min_le_right (G.dist a b) (min (G.dist a z) (G.dist b z)))
            (Nat.min_le_left (G.dist a z) (G.dist b z))
          omega
        · have hb := bound a z (Or.inr h)
          have hm := Nat.le_trans (Nat.min_le_right (G.dist a b) (min (G.dist a z) (G.dist b z)))
            (Nat.min_le_left (G.dist a z) (G.dist b z))
          omega
        · have hb := bound b z (Or.inl h)
          have hm := Nat.le_trans (Nat.min_le_right (G.dist a b) (min (G.dist a z) (G.dist b z)))
            (Nat.min_le_right (G.dist a z) (G.dist b z))
          omega
        · have hb := bound b z (Or.inr h)
          have hm := Nat.le_trans (Nat.min_le_right (G.dist a b) (min (G.dist a z) (G.dist b z)))
            (Nat.min_le_right (G.dist a z) (G.dist b z))
          omega
    · have hr0 : radius T = 0 := by omega
      have hb := ecc_upper T c b
      have ha := ecc_upper T c a
      have ht := distTriangle T a c b
      rw [dist_symm T a c] at ht
      rw [hc,hr0] at ha hb
      have hd := dist_compat hG a b
      change dist T a b = G.dist a b at hd
      have hb0 : G.dist a b = 0 := by omega
      rw [hr0,hb0,Nat.zero_min]
      omega

#print axioms treePacking
end Graffiti232Tree

/- Proof module: Formal241 -/

set_option warningAsError true
set_option linter.unusedSectionVars false
noncomputable section
open Finset SimpleGraph Graffiti271
open scoped BigOperators
namespace Graffiti241
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def S (v : V) : Prop := (nbr G v).card = 2

noncomputable def closedDegreeTwo : Finset V := by
  classical
  exact univ.filter (fun v => S G v ∨ ∃ s, S G s ∧ G.Adj v s)

@[simp] theorem mem_closed (v : V) :
    v ∈ closedDegreeTwo G ↔ S G v ∨ ∃ s, S G s ∧ G.Adj v s := by
  classical
  simp [closedDegreeTwo]

noncomputable def countComponents : ℕ :=
  GraffitiCore.componentCount G (closedDegreeTwo G)

theorem component_charging (hc : G.Connected) (D : Finset V)
    (hD : TotalDominates G D) : countComponents G + 1 ≤ D.card := by
  classical
  let C := closedDegreeTwo G
  let H := G.induce (C : Set V)
  haveI : Finite H.ConnectedComponent :=
    Finite.of_surjective H.connectedComponentMk (fun c => c.exists_rep)
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  change Fintype.card H.ConnectedComponent + 1 ≤ D.card
  have hW (c : H.ConnectedComponent) :
      ∃ d, d ∈ D ∧ ∃ hd : d ∈ C, H.connectedComponentMk ⟨d,hd⟩ = c := by
    obtain ⟨x,hx⟩ := c.exists_rep
    have hC : x.1 ∈ closedDegreeTwo G := x.2
    have hS : ∃ s : ↑(C : Set V), S G s.1 ∧ H.connectedComponentMk s = c := by
      rcases (mem_closed G x.1).mp hC with h | ⟨s,hs,had⟩
      · exact ⟨x,h,hx⟩
      · let s' : ↑(C : Set V) := ⟨s,(mem_closed G s).mpr (Or.inl hs)⟩
        have hxs : H.Adj x s' := had
        exact ⟨s',hs,(SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxs).symm.trans hx⟩
    obtain ⟨s,hs,he⟩ := hS
    obtain ⟨d,hd,had⟩ := hD s.1
    have hdC : d ∈ C := (mem_closed G d).mpr (Or.inr ⟨s.1,hs,had.symm⟩)
    have hsd : H.Adj s ⟨d,hdC⟩ := had
    exact ⟨d,hd,hdC,(SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hsd).symm.trans he⟩
  let f (c : H.ConnectedComponent) : V := Classical.choose (hW c)
  have hmem (c : H.ConnectedComponent) : f c ∈ D := (Classical.choose_spec (hW c)).1
  have hrep (c : H.ConnectedComponent) :
      ∃ hd : f c ∈ C, H.connectedComponentMk ⟨f c,hd⟩ = c :=
    (Classical.choose_spec (hW c)).2
  have hinj : Function.Injective f := by
    intro a b h
    obtain ⟨ha,hea⟩ := hrep a
    obtain ⟨hb,heb⟩ := hrep b
    have hs : (⟨f a,ha⟩ : ↑(C : Set V)) = ⟨f b,hb⟩ := Subtype.ext h
    exact hea.symm.trans ((congrArg H.connectedComponentMk hs).trans heb)
  let R : Finset V := Finset.univ.image f
  have hRD : R ⊆ D := by
    intro d hd
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hd
    exact hmem c
  have hR : R.card = Fintype.card H.ConnectedComponent := by
    dsimp [R]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hle := Finset.card_le_card hRD
  by_cases hstrict : Fintype.card H.ConnectedComponent < D.card
  · omega
  have heq : D = R := (Finset.eq_of_subset_of_card_le hRD (by omega)).symm
  obtain ⟨x⟩ := hc.nonempty
  obtain ⟨u,hu,_⟩ := hD x
  obtain ⟨v,hv,huv⟩ := hD u
  rw [heq] at hu hv
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨ha,hea⟩ := hrep a
  obtain ⟨hb,heb⟩ := hrep b
  have hadd : H.Adj ⟨f a,ha⟩ ⟨f b,hb⟩ := huv
  have hab := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadd
  rw [hea,heb] at hab
  exact False.elim (huv.ne (congrArg f hab))

end Graffiti241

namespace Graffiti232Tree
variable {V : Type*} [DecidableEq V]

theorem centers_adjacent {T : Tree V} {u v} (hu : center T u = true)
    (hv : center T v = true) (hneq : u≠v) : Adj T.graph u v := by
  have huv := chosen_path T u v
  cases hcc : chosen T u v with
  | nil =>
    rw [hcc] at huv
    exact False.elim (hneq (path_empty_endpoint huv))
  | cons z p =>
    rw [hcc] at huv
    have he : Adj T.graph u z := by cases huv with | cons e _ _ => exact e
    have hp : TPath T z p v := by cases huv with | cons _ _ hp => exact hp
    cases pp : p with
    | nil =>
      rw [pp] at hp
      rw [path_empty_endpoint hp] at he
      exact he
    | cons z' ps =>
      have hzu : z≠u := by
        intro ee; subst z
        have hh := T.graph.loopless u
        simp [Adj,hh] at he
      obtain ⟨x,hx⟩ := ecc_attains T z
      by_cases hz : z ∈ chosen T u x
      · obtain ⟨q,hq⟩ := path_starts_iff_contains_neighbor he (chosen_path T u x) hz
        have hxroute := chosen_path T u x
        rw [hq] at hxroute
        have htail : TPath T z q x := by cases hxroute with | cons _ _ hh => exact hh
        have d1 := dist_eq hxroute
        have d2 := dist_eq htail
        have h1 := ecc_upper T u x
        have h2 := center_char.mp hu z
        simp at d1
        omega
      · have d1 := dist_other_branch huv hz
        have hxroute := chosen_path T u x
        have hnew : TPath T z (u :: chosen T u x) x := by
          apply PathTo.cons (T.graph.symm _ _ he) _ hxroute
          intro hh
          exact (List.mem_cons.mp hh).elim hzu hz
        have d2 := dist_eq hnew
        have d3 := dist_eq huv
        have d4 : dist T v u = dist T u v := by
          obtain ⟨q,hq,hl,_⟩ := path_reverse huv
          rw [dist_eq hq,d3,hl]
        rw [pp] at d3
        have h1 := ecc_upper T v x
        have h2 := center_char.mp hv z
        simp at d2 d3
        have d5 : (chosen T u x).length = dist T u x := rfl
        omega


end Graffiti232Tree

namespace Graffiti241
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def ecc (v : V) : ℕ := univ.sup (G.dist v)

def IsCenter (v : V) : Prop := ∀ w, ecc G v ≤ ecc G w

theorem ecc_compat [DecidableEq V] (hT : G.IsTree) (v : V) :
    Graffiti232Tree.eccentricity (Graffiti232Tree.fromSimpleTree G hT) v = ecc G v := by
  apply Nat.le_antisymm
  · obtain ⟨w,hw⟩ := Graffiti232Tree.ecc_attains (Graffiti232Tree.fromSimpleTree G hT) v
    rw [← hw, Graffiti232Tree.dist_compat hT]
    exact Finset.le_sup (f:=G.dist v) (Finset.mem_univ w)
  · apply Finset.sup_le
    intro w _
    rw [← Graffiti232Tree.dist_compat hT]
    exact Graffiti232Tree.ecc_upper (Graffiti232Tree.fromSimpleTree G hT) v w

theorem distinct_centers_distance (hT : G.IsTree) {a b : V}
    (ha : IsCenter G a) (hb : IsCenter G b) (hne : a ≠ b) : G.dist a b = 1 := by
  classical
  let T := Graffiti232Tree.fromSimpleTree G hT
  have hcA : Graffiti232Tree.center T a = true := by
    apply Graffiti232Tree.center_char.mpr
    intro w
    simp only [T, ecc_compat G hT]
    exact ha w
  have hcB : Graffiti232Tree.center T b = true := by
    apply Graffiti232Tree.center_char.mpr
    intro w
    simp only [T, ecc_compat G hT]
    exact hb w
  have hh := Graffiti232Tree.centers_adjacent hcA hcB hne
  exact SimpleGraph.dist_eq_one_iff_adj.mpr (Graffiti232Tree.adj_iff_simple.mp hh)

noncomputable def centerPairs : Finset (V × V) := by
  classical
  exact univ.filter (fun p => IsCenter G p.1 ∧ IsCenter G p.2 ∧ 0 < G.dist p.1 p.2)

/-- The closed-neighborhood component count is separate from this mean.
The empty mean is zero, following the standard totalized division in Lean. -/
noncomputable def avgCenterDist : ℚ :=
  (↑(∑ p ∈ centerPairs G, G.dist p.1 p.2) : ℚ) / ↑(centerPairs G).card

theorem avgCenterDist_le_one (hT : G.IsTree) : avgCenterDist G ≤ 1 := by
  classical
  have hsum : (∑ p ∈ centerPairs G, G.dist p.1 p.2) = (centerPairs G).card := by
    calc
      _ = ∑ _p ∈ centerPairs G, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro p hp
        have h := (Finset.mem_filter.mp hp).2
        have hne : p.1 ≠ p.2 := by
          intro he
          rw [he,SimpleGraph.dist_self] at h
          exact Nat.not_lt_zero _ h.2.2
        exact distinct_centers_distance G hT h.1 h.2.1 hne
      _ = _ := by simp
  unfold avgCenterDist
  rw [hsum]
  by_cases hh : (centerPairs G).card = 0
  · simp [hh]
  · have hh' : ((centerPairs G).card : ℚ) ≠ 0 := by exact_mod_cast hh
    rw [div_self hh']

/-- Exact #241, with the standard zero extension when the center is unique.
The order lower bound excludes the tree with no total dominating set. -/
theorem conjecture241 (hT : G.IsTree) (hn : 2 ≤ Fintype.card V) :
    ⌊(countComponents G : ℚ) + avgCenterDist G⌋ ≤ (totalDominationNumber G : ℤ) := by
  obtain ⟨D,hD,heq⟩ := GraffitiPeriphery.exists_min_td G hT.isConnected hn
  have hcount := component_charging G hT.isConnected D hD
  rw [heq] at hcount
  have hc : ((countComponents G + 1 : ℕ) : ℚ) ≤ (totalDominationNumber G : ℚ) :=
    Nat.cast_le.mpr hcount
  have hle : (countComponents G : ℚ) + avgCenterDist G ≤ (totalDominationNumber G : ℚ) := by
    have ha := add_le_add_left (avgCenterDist_le_one G hT) (countComponents G : ℚ)
    apply ha.trans
    simpa only [Nat.cast_add,Nat.cast_one] using hc
  simpa using Int.floor_mono hle

#print axioms conjecture241
end Graffiti241
