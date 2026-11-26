import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Tactic.FinCases
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Written on the Wall II, conjecture 305

The precise ceiling bound holds whenever the complement has an edge, so
the maximum in the published statement exists. With the alternative
convention that the empty maximum is zero, all complete graphs of order
at least three are counterexamples to that convention.

If the maximum complement edge-neighborhood size M is smaller than n,
every nonadjacent pair has at least t=n-M common neighbors. A minimum-degree
vertex and a sufficiently large subset of its neighbors totally dominate.
Combining this with the plain degree bound gives the desired inequality.
The largest possible M=n is covered by the classical two-thirds bound,
formalized here using Bickle's distance-modulo-three exchange argument.

Official catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
Classical bound: Cockayne, Dawes and Hedetniemi (1980), doi:10.1002/net.3230100304.
Bickle, Theorem 7.52: https://www.ams.org/bookstore/pspdf/amstext-43-prev.pdf
Lean 4.19.0 and Mathlib v4.19.0.
-/

/-! Formalization of the color-class exchange step from Bickle's short
proof of the classical two-thirds total-domination bound. -/
namespace Graffiti305Colors
open Finset SimpleGraph
open scoped BigOperators
noncomputable section
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
local instance : DecidableEq V := Classical.decEq V

def LeafNear (x y : V) : Prop := G.Adj x y ∧ ∀ w, G.Adj x w → w=y

def IsLeaf (x : V) : Prop := ∃ y, LeafNear (G:=G) x y

theorem class_exchange (color : V → Fin 3)
    (proper : ∀ x y, G.Adj x y → color x ≠ color y)
    (outsidePair : ∀ {x y}, LeafNear (G:=G) x y → ¬IsLeaf (G:=G) y)
    (rich : ∀ x, ¬IsLeaf (G:=G) x → ∃ u v, G.Adj x u ∧ G.Adj x v ∧ color u ≠ color v)
    (q : Fin 3) :
    ∃ D : Finset V, (∀ x, ∃ y ∈ D, G.Adj x y) ∧
      D.card ≤ (univ.filter fun x => color x ≠ q).card := by
  classical
  let S : Finset V := univ.filter (fun x => color x ≠ q)
  let P : Finset V := univ.filter (fun y => color y = q ∧ ∃ x, LeafNear (G:=G) x y)
  have hP (y : V) (hy : y ∈ P) : ∃ x, LeafNear (G:=G) x y := (mem_filter.mp hy).2.2
  let f (y : P) : V := Classical.choose (hP y y.2)
  have hf (y : P) : LeafNear (G:=G) (f y) y := Classical.choose_spec (hP y y.2)
  let L : Finset V := P.attach.image f
  let D := (S \ L) ∪ P
  have hLS : L ⊆ S := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := mem_image.mp hx
    have hc := (mem_filter.mp y.2).2.1
    exact mem_filter.mpr ⟨mem_univ _, hc ▸ proper _ _ (hf y).1⟩
  have hfInj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact ((hf a).2 _ (h.symm ▸ (hf b).1)).symm
  have hL : L.card = P.card := by
    rw [show L.card = (P.attach.image f).card from rfl, card_image_of_injective _ hfInj,card_attach]
  have hsize : D.card ≤ S.card := by
    have h := card_union_le (S \ L) P
    rw [card_sdiff hLS,hL] at h
    have hle := card_le_card hLS
    rw [hL] at hle
    change D.card ≤ S.card - P.card + P.card at h
    change D.card ≤ S.card
    omega
  refine ⟨D, ?_,hsize⟩
  intro x
  by_cases hx : IsLeaf (G:=G) x
  · obtain ⟨y,hy⟩ := hx
    refine ⟨y, ?_,hy.1⟩
    by_cases h : color y = q
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _,h,x,hy⟩))
    · apply mem_union.mpr
      left
      refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,h⟩,?_⟩
      intro he
      obtain ⟨z,_,hz⟩ := mem_image.mp he
      exact outsidePair hy ⟨z,hz ▸ hf z⟩
  · obtain ⟨a,b,ha,hb,hd⟩ := rich x hx
    have retain (a : V) (ha : G.Adj x a) (hs : color a ≠ q)
        (hnot : a ∉ L) : ∃ y ∈ D, G.Adj x y := by
      exact ⟨a,mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,hs⟩,hnot⟩)),ha⟩
    have hOwner (a : V) (ha : G.Adj x a) (haL : a ∈ L) :
        ∃ y : P, x = y ∧ a = f y := by
      obtain ⟨y,_,hy⟩ := mem_image.mp haL
      exact ⟨y,(hf y).2 x (hy.symm ▸ ha.symm),hy.symm⟩
    by_cases hq : color x = q
    · have hsa : color a ≠ q := hq ▸ (Ne.symm (proper _ _ ha))
      have hsb : color b ≠ q := hq ▸ (Ne.symm (proper _ _ hb))
      by_cases h₁ : a ∈ L
      · apply retain b hb hsb
        intro h₂
        obtain ⟨y,hy,hy'⟩ := hOwner a ha h₁
        obtain ⟨z,hz,hz'⟩ := hOwner b hb h₂
        have hye : y=z := Subtype.ext (hy.symm.trans hz)
        exact hd (congrArg color (hy'.trans (hye ▸ hz'.symm)))
      · exact retain a ha hsa h₁
    · have noRemoval (u : V) (hu : G.Adj x u) : u ∉ L := by
        intro h
        obtain ⟨y,hy,_⟩ := hOwner u hu h
        exact hq (hy.symm ▸ (mem_filter.mp y.2).2.1)
      by_cases ha' : color a = q
      · exact retain b hb (fun h => hd (ha'.trans h.symm)) (noRemoval b hb)
      · exact retain a ha ha' (noRemoval a ha)

theorem colored_total_domination (color : V → Fin 3)
    (proper : ∀ x y, G.Adj x y → color x ≠ color y)
    (outsidePair : ∀ {x y}, LeafNear (G:=G) x y → ¬IsLeaf (G:=G) y)
    (rich : ∀ x, ¬IsLeaf (G:=G) x → ∃ u v, G.Adj x u ∧ G.Adj x v ∧ color u ≠ color v) :
    ∃ D : Finset V, (∀ x, ∃ y ∈ D, G.Adj x y) ∧ 3*D.card ≤ 2*Fintype.card V := by
  classical
  let sz (q : Fin 3) := (univ.filter fun x => color x = q).card
  obtain ⟨q,_,hq⟩ := exists_max_image (univ : Finset (Fin 3)) sz univ_nonempty
  have sumSz : (∑ q, sz q) = Fintype.card V := by
    simp only [sz, Finset.card_filter]
    rw [Finset.sum_comm]
    have hs : (∑ x : V, ∑ i : Fin 3, if color x = i then (1 : ℕ) else 0) =
        ∑ _x : V, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro x _
      simp [eq_comm]
    exact hs.trans (by simp)
  have hz : Fintype.card V ≤ 3 * sz q := by
    have h := Finset.sum_le_sum (s := (univ : Finset (Fin 3))) (fun q' hq' => hq q' hq')
    simpa [sumSz,Nat.mul_comm] using h
  obtain ⟨D,hd,hc⟩ := class_exchange color proper outsidePair rich q
  have hp := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset V))
    (p := fun x => color x = q)
  change sz q + ((univ : Finset V).filter fun x => color x ≠ q).card = (univ : Finset V).card at hp
  rw [card_univ] at hp
  exact ⟨D,hd,by omega⟩


private theorem neighbor_exists {H : SimpleGraph V} (hc : H.Connected)
    (hn : 2 ≤ Fintype.card V) (v : V) : ∃ w, H.Adj v w := by
  obtain ⟨w,hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
  obtain ⟨p⟩ := hc v w
  cases p with
  | nil => exact (hw rfl).elim
  | cons ha _ => exact ⟨_,ha⟩

private theorem tree_has_leaf (T : SimpleGraph V) (hT : T.IsTree)
    (hn : 2 ≤ Fintype.card V) : ∃ r, IsLeaf (G := T) r := by
  classical
  by_contra h
  have hd (v : V) : 2 ≤ T.degree v := by
    have hpos := (T.degree_pos_iff_exists_adj v).mpr (neighbor_exists hT.isConnected hn v)
    by_contra! hh
    have hOne : T.degree v = 1 := by omega
    rw [← T.card_neighborFinset_eq_degree] at hOne
    obtain ⟨w,hw⟩ := card_eq_one.mp hOne
    apply h
    refine ⟨v,w, ?_, ?_⟩
    · apply (T.mem_neighborFinset _ _).mp
      rw [hw]
      simp
    · intro u hu
      have he := (T.mem_neighborFinset _ _).mpr hu
      rw [hw] at he
      exact mem_singleton.mp he
  have hs := Finset.sum_le_sum (s := (univ : Finset V)) (fun v _ => hd v)
  rw [T.sum_degrees_eq_twice_card_edges] at hs
  have ht := hT.card_edgeFinset
  simp only [Finset.sum_const,Nat.nsmul_eq_mul,Finset.card_univ] at hs
  omega

private theorem connected_no_pair_of_leaves {H : SimpleGraph V} (hc : H.Connected)
    (hn : 3 ≤ Fintype.card V) {x y : V} (hx : LeafNear (G:=H) x y) :
    ¬ IsLeaf (G:=H) y := by
  intro hy
  obtain ⟨z,hz⟩ := hy
  have he : x=z := hz.2 _ hx.1.symm
  subst z
  let S : Finset V := {x,y}
  have hClosed (u : V) (hu : u ∈ S) (v : V) (hv : H.Adj u v) : v ∈ S := by
    simp only [S,mem_insert,mem_singleton] at hu ⊢
    rcases hu with rfl | rfl
    · exact Or.inr (hx.2 _ hv)
    · exact Or.inl (hz.2 _ hv)
  have help {a b : V} (p : H.Walk a b) (ha : a ∈ S) : b ∈ S := by
    induction p with
    | nil => exact ha
    | cons ha' q ih => exact ih (hClosed _ ha _ ha')
  have hAll : (univ : Finset V) ⊆ S := by
    intro v _
    obtain ⟨w⟩ := hc x v
    exact help w (by simp [S])
  have hS : S.card = 2 := by simp [S,hx.1.ne]
  have hN := card_le_card hAll
  rw [hS,card_univ] at hN
  omega

omit [Fintype V] in
private theorem toward_root {H : SimpleGraph V} (hc : H.Connected) {r v : V} (h : v ≠ r) :
    ∃ z, H.Adj v z ∧ H.dist r z + 1 = H.dist r v := by
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist v r
  have hpos : 0 < p.length := by rw [hp]; exact hc.pos_dist_of_ne h
  have hn : ¬ p.Nil := Walk.not_nil_iff_lt_length.mpr hpos
  have h1 : H.Adj v (p.getVert 1) := by simpa using p.adj_getVert_succ (i:=0) hpos
  have h2 := H.dist_le p.tail
  rw [SimpleGraph.dist_comm] at h2
  change H.dist r (p.getVert 1) ≤ p.tail.length at h2
  have h3 := p.length_tail_add_one hn
  rw [hp, SimpleGraph.dist_comm] at h3
  have h4 : H.dist r v ≤ H.dist r (p.getVert 1) + H.dist (p.getVert 1) v :=
    hc.dist_triangle
  rw [dist_eq_one_iff_adj.mpr h1.symm] at h4
  exact ⟨_,h1,by omega⟩

/-- The Cockayne–Dawes–Hedetniemi bound via distance mod three from a spanning-tree leaf. -/
theorem total_dominating_set_order_bound (G : SimpleGraph V) (hc : G.Connected)
    (hn : 3 ≤ Fintype.card V) :
    ∃ D : Finset V, (∀ x, ∃ y ∈ D, G.Adj x y) ∧ 3*D.card ≤ 2*Fintype.card V := by
  classical
  obtain ⟨T,hTG,hT⟩ := hc.exists_isTree_le
  obtain ⟨r,s,hs⟩ := tree_has_leaf T hT (by omega)
  let p (v : V) := if h : v = r then r else Classical.choose (toward_root hT.isConnected h)
  have pp (v : V) (h : v ≠ r) : T.Adj v (p v) ∧ T.dist r (p v)+1 = T.dist r v := by
    simpa [p,h] using Classical.choose_spec (toward_root hT.isConnected h)
  let H : SimpleGraph V :=
    { Adj := fun u v => (u ≠ r ∧ p u = v) ∨ (v ≠ r ∧ p v = u)
      symm := fun _ _ => Or.symm
      loopless := by
        intro v h
        have hd := (pp v (h.elim id id).1).2
        rw [(h.elim id id).2] at hd
        omega }
  have hHT : H ≤ T := by
    intro u v h
    rcases h with ⟨h,e⟩ | ⟨h,e⟩
    · rw [← e]; exact (pp u h).1
    · rw [← e]; exact (pp v h).1.symm
  have hReach : ∀ v, H.Reachable v r := by
    intro v
    generalize he : T.dist r v = n
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v=r
      · rw [hv]
      · have hlt : T.dist r (p v) < n := by have h := (pp v hv).2; omega
        have ha : H.Adj v (p v) := Or.inl ⟨hv,rfl⟩
        exact ha.reachable.trans (ih _ hlt _ rfl)
  have hH : H.Connected :=
    (connected_iff_exists_forall_reachable H).mpr ⟨r,fun v => (hReach v).symm⟩
  have rootLeaf : IsLeaf (G:=H) r := by
    obtain ⟨w,hw⟩ := neighbor_exists hH (by omega) r
    refine ⟨w,hw,?_⟩
    intro v hv
    exact (hs.2 _ (hHT hv)).trans (hs.2 _ (hHT hw)).symm
  let color (v : V) : Fin 3 := ⟨T.dist r v % 3, Nat.mod_lt _ (by decide)⟩
  have proper (u v : V) (h : H.Adj u v) : color u ≠ color v := by
    intro eq
    have hcol := congrArg Fin.val eq
    change T.dist r u % 3 = T.dist r v % 3 at hcol
    rcases h with ⟨hu,he⟩ | ⟨hv,he⟩
    · have hh := (pp u hu).2
      rw [he] at hh
      omega
    · have hh := (pp v hv).2
      rw [he] at hh
      omega
  have rich (x : V) (hne : ¬IsLeaf (G:=H) x) :
      ∃ u v, H.Adj x u ∧ H.Adj x v ∧ color u ≠ color v := by
    have hx : x ≠ r := fun eq => hne (eq.symm ▸ rootLeaf)
    have hpu : H.Adj x (p x) := Or.inl ⟨hx,rfl⟩
    have hh : ∃ v, H.Adj x v ∧ v ≠ p x := by
      by_contra! hh
      exact hne ⟨p x,hpu,hh⟩
    obtain ⟨v,hv,hvp⟩ := hh
    refine ⟨p x,v,hpu,hv,?_⟩
    have hd := (pp x hx).2
    have hvd : T.dist r x+1 = T.dist r v := by
      rcases hv with ⟨_,e⟩ | ⟨hvr,e⟩
      · exact (hvp e.symm).elim
      · have h := (pp v hvr).2
        rwa [e] at h
    intro e
    have hh := congrArg Fin.val e
    change T.dist r (p x) % 3 = T.dist r v % 3 at hh
    omega
  obtain ⟨D,hD,hcard⟩ := colored_total_domination (G:=H) color proper
    (fun hx => connected_no_pair_of_leaves hH hn hx) rich
  exact ⟨D,fun x => (hD x).imp fun y h => ⟨h.1,hTG (hHT h.2)⟩,hcard⟩

#print axioms total_dominating_set_order_bound
#print axioms colored_total_domination
end
end Graffiti305Colors

/-! Complement edge neighborhoods and the exact #305 bound. -/
namespace Graffiti305
open SimpleGraph Finset
noncomputable section
variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel H.Adj

def edgeNeighborhood (H : SimpleGraph V) (u v : V) : Finset V :=
  H.neighborFinset u ∪ H.neighborFinset v

def maxEdgeNeighborhood (H : SimpleGraph V) : ℕ :=
  univ.sup (fun u => (univ.filter (H.Adj u)).sup fun v => (edgeNeighborhood H u v).card)

theorem edgeNeighborhood_le_max (H : SimpleGraph V) {u v : V} (h : H.Adj u v) :
    (edgeNeighborhood H u v).card ≤ maxEdgeNeighborhood H :=
  (le_sup (f := fun v => (edgeNeighborhood H u v).card) (mem_filter.mpr ⟨mem_univ _,h⟩)).trans
    (le_sup (f := fun u => (univ.filter (H.Adj u)).sup fun v => (edgeNeighborhood H u v).card) (mem_univ u))

private theorem edgeNeighborhood_spec {H : SimpleGraph V} {u v w : V} :
    w ∈ edgeNeighborhood H u v ↔ H.Adj u w ∨ H.Adj v w := by
  simp [edgeNeighborhood]

private theorem at_least_two {H : SimpleGraph V} {u v : V} (h : H.Adj u v) :
    2 ≤ maxEdgeNeighborhood H := by
  have hS : ({u,v} : Finset V) ⊆ edgeNeighborhood H u v := by
    intro w hw
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact edgeNeighborhood_spec.mpr (Or.inr h.symm)
    · exact edgeNeighborhood_spec.mpr (Or.inl h)
  have hcard := (card_le_card hS).trans (edgeNeighborhood_le_max H h)
  simpa [h.ne] using hcard

private theorem at_least_four_of_four {H : SimpleGraph V} {a b c d : V} {u v : V}
    (ha : a ∈ edgeNeighborhood H u v) (hb : b ∈ edgeNeighborhood H u v)
    (hc : c ∈ edgeNeighborhood H u v) (hd : d ∈ edgeNeighborhood H u v)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    4 ≤ (edgeNeighborhood H u v).card := by
  have hS : ({a,b,c,d} : Finset V) ⊆ edgeNeighborhood H u v := by
    intro w hw
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  simpa [hab,hac,had,hbc,hbd,hcd] using card_le_card hS

def TotalDominatingPair (G : SimpleGraph V) (u v : V) : Prop :=
  G.Adj u v ∧ ∀ w, G.Adj w u ∨ G.Adj w v

omit [Fintype V] in
private theorem exists_compl_common_when_no_pair {G : SimpleGraph V}
    (hn : ¬∃ u v, TotalDominatingPair G u v) {u v : V} (huv : G.Adj u v) :
    ∃ w, Gᶜ.Adj u w ∧ Gᶜ.Adj v w := by
  by_contra! h
  apply hn
  refine ⟨u,v,huv,?_⟩
  intro w
  by_cases hwu : w = u
  · subst w
    exact Or.inr huv
  by_cases hwv : w = v
  · subst w
    exact Or.inl huv.symm
  by_cases h₁ : G.Adj w u
  · exact Or.inl h₁
  by_cases h₂ : G.Adj w v
  · exact Or.inr h₂
  exact (h w ⟨Ne.symm hwu, fun had => h₁ had.symm⟩ ⟨Ne.symm hwv, fun had => h₂ had.symm⟩).elim

theorem dominating_pair_when_max_at_most_three {G : SimpleGraph V} (hc : G.Connected)
    (hn : 3 ≤ Fintype.card V) (hmax : maxEdgeNeighborhood Gᶜ ≤ 3)
    (he : ∃ u v, Gᶜ.Adj u v) :
    ∃ u v, TotalDominatingPair G u v := by
  by_contra hh
  let H := Gᶜ
  obtain ⟨a,b,hab⟩ := he
  change H.Adj a b at hab
  have coverage (w : V) : w ∈ edgeNeighborhood H a b := by
    by_contra h
    have haw : ¬H.Adj a w := fun hz => h (edgeNeighborhood_spec.mpr (Or.inl hz))
    have hbw : ¬H.Adj b w := fun hz => h (edgeNeighborhood_spec.mpr (Or.inr hz))
    have hne₁ : a ≠ w := fun he => hbw (he ▸ hab.symm)
    have hne₂ : b ≠ w := fun he => haw (he ▸ hab)
    have ga : G.Adj a w := Classical.byContradiction (fun hz => haw ⟨hne₁,hz⟩)
    have gb : G.Adj b w := Classical.byContradiction (fun hz => hbw ⟨hne₂,hz⟩)
    obtain ⟨z,haz,hwz⟩ := exists_compl_common_when_no_pair hh ga
    obtain ⟨t,hbt,hwt⟩ := exists_compl_common_when_no_pair hh gb
    change H.Adj a z at haz
    change H.Adj w z at hwz
    change H.Adj b t at hbt
    change H.Adj w t at hwt
    have hza : z ≠ a := haz.ne.symm
    have hzb : z ≠ b := fun he => hbw (he ▸ hwz.symm)
    have hta : t ≠ a := fun he => haw (he ▸ hwt.symm)
    have htb : t ≠ b := hbt.ne.symm
    have haN : a ∈ edgeNeighborhood H a b := edgeNeighborhood_spec.mpr (Or.inr hab.symm)
    have hbN : b ∈ edgeNeighborhood H a b := edgeNeighborhood_spec.mpr (Or.inl hab)
    have hzt : z=t := by
      by_contra hne
      have h₁ := at_least_four_of_four haN hbN (edgeNeighborhood_spec.mpr (Or.inl haz))
        (edgeNeighborhood_spec.mpr (Or.inr hbt)) hab.ne hza.symm hta.symm hzb.symm htb.symm hne
      have h₂ := edgeNeighborhood_le_max H hab
      change maxEdgeNeighborhood H ≤ 3 at hmax
      omega
    have hbz : H.Adj b z := hzt.symm ▸ hbt
    have h₁ := at_least_four_of_four (H:=H) (u:=a) (v:=z)
      (edgeNeighborhood_spec.mpr (Or.inr haz.symm))
      (edgeNeighborhood_spec.mpr (Or.inl hab))
      (edgeNeighborhood_spec.mpr (Or.inl haz))
      (edgeNeighborhood_spec.mpr (Or.inr hwz.symm))
      hab.ne haz.ne hne₁ hbz.ne hne₂ hwz.ne.symm
    have h₂ := edgeNeighborhood_le_max H haz
    change maxEdgeNeighborhood H ≤ 3 at hmax
    omega
  have hcard : Fintype.card V ≤ 3 := by
    have h₁ := card_le_card (show (univ : Finset V) ⊆ edgeNeighborhood H a b from fun v _ => coverage v)
    rw [card_univ] at h₁
    have h₂ := edgeNeighborhood_le_max H hab
    change maxEdgeNeighborhood H ≤ 3 at hmax
    omega
  haveI : Nonempty V := hc.nonempty
  let x : V := Classical.choice ‹Nonempty V›
  obtain ⟨y,hy⟩ := Fintype.exists_ne_of_one_lt_card (by omega) x
  have had : ∃ y, G.Adj x y := by
    obtain ⟨p⟩ := hc x y
    cases p with
    | nil => exact (hy rfl).elim
    | cons h _ => exact ⟨_,h⟩
  obtain ⟨y,hxy⟩ := had
  obtain ⟨z,hxz,hyz⟩ := exists_compl_common_when_no_pair hh hxy
  have triple : ({x,y,z} : Finset V).card = 3 := by simp [hxy.ne,hxz.1,hyz.1]
  have all : ({x,y,z} : Finset V) = univ :=
    eq_of_subset_of_card_le (subset_univ _) (by rw [triple,card_univ]; exact hcard)
  obtain ⟨p⟩ := hc z x
  cases p with
  | nil => exact (hxz.1 rfl).elim
  | @cons _ w _ h _ =>
    have hw : w ∈ ({x,y,z} : Finset V) := by rw [all]; exact mem_univ _
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hxz.2 h.symm
    · exact hyz.2 h.symm
    · exact h.ne rfl

def TotalDominates (G : SimpleGraph V) (D : Finset V) : Prop := ∀ v, ∃ w ∈ D, G.Adj v w

def totalDominationNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}

theorem conjecture305_small_complement_neighborhood {G : SimpleGraph V}
    (hc : G.Connected) (hn : 3 ≤ Fintype.card V) (he : ∃ u v, Gᶜ.Adj u v)
    (hmax : maxEdgeNeighborhood Gᶜ ≤ 3) :
    totalDominationNumber G ≤ (2*maxEdgeNeighborhood Gᶜ + 2)/3 := by
  obtain ⟨u,v,huv,hD⟩ := dominating_pair_when_max_at_most_three hc hn hmax he
  have hdom : TotalDominates G {u,v} := by
    intro w
    rcases hD w with h₁ | h₂
    · exact ⟨u,by simp,h₁⟩
    · exact ⟨v,by simp,h₂⟩
  have h₂ : totalDominationNumber G ≤ 2 := Nat.sInf_le ⟨{u,v},hdom,by simp [huv.ne]⟩
  obtain ⟨a,b,hab⟩ := he
  have h₃ := at_least_two hab
  omega

theorem degree_add_one_le_max_if_nonisolated (H : SimpleGraph V) (u : V)
    (h : ∃ v, H.Adj u v) : H.degree u + 1 ≤ maxEdgeNeighborhood H := by
  obtain ⟨v,hv⟩ := h
  have hs : insert u (H.neighborFinset u) ⊆ edgeNeighborhood H u v := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact edgeNeighborhood_spec.mpr (Or.inr hv.symm)
    · exact edgeNeighborhood_spec.mpr (Or.inl ((H.mem_neighborFinset _ _).mp hw))
  have hn : u ∉ H.neighborFinset u := by simp
  have hcard := (card_le_card hs).trans (edgeNeighborhood_le_max H hv)
  simpa [card_insert_of_not_mem hn] using hcard

theorem complement_edge_neighborhood_lower (G : SimpleGraph V)
    (he : ∃ u v, Gᶜ.Adj u v) : Fintype.card V - G.minDegree ≤ maxEdgeNeighborhood Gᶜ := by
  obtain ⟨a,b,hab⟩ := he
  haveI : Nonempty V := ⟨a⟩
  obtain ⟨u,hu⟩ := G.exists_minimal_degree_vertex
  have hd := G.degree_compl (v := u)
  have ha := G.degree_compl (v := a)
  have hp := (Gᶜ.degree_pos_iff_exists_adj a).mpr ⟨b,hab⟩
  have hm := G.minDegree_le_degree a
  have hpos : 0 < Gᶜ.degree u := by omega
  have h := degree_add_one_le_max_if_nonisolated Gᶜ u ((Gᶜ.degree_pos_iff_exists_adj u).mp hpos)
  have eq : Gᶜ.degree u + 1 = Fintype.card V - G.minDegree := by
    rw [hd, ← hu]
    have hmu : G.minDegree ≤ Fintype.card V - 1 := by omega
    omega
  have hh : Gᶜ.degree u + 1 ≤ maxEdgeNeighborhood Gᶜ := by
    convert h using 2
    congr 1
    apply Subsingleton.elim
  exact eq.ge.trans hh


private theorem compl_edge_neighborhood_complement {G : SimpleGraph V}
    {u v : V} (h : Gᶜ.Adj u v) :
    (univ : Finset V) \ edgeNeighborhood Gᶜ u v = G.neighborFinset u ∩ G.neighborFinset v := by
  ext w
  simp only [mem_sdiff,mem_univ,true_and,edgeNeighborhood_spec,mem_inter,mem_neighborFinset]
  constructor
  · intro hw
    have hwu : u ≠ w := fun e => hw (Or.inr (e ▸ h.symm))
    have hwv : v ≠ w := fun e => hw (Or.inl (e ▸ h))
    exact ⟨Classical.byContradiction (fun e => hw (Or.inl ⟨hwu,e⟩)),
      Classical.byContradiction (fun e => hw (Or.inr ⟨hwv,e⟩))⟩
  · rintro ⟨ha,hb⟩ (h₁ | h₂)
    · exact h₁.2 ha
    · exact h₂.2 hb

private theorem nonadj_common_cap {G : SimpleGraph V} {u v : V}
    (h : Gᶜ.Adj u v) :
    Fintype.card V - maxEdgeNeighborhood Gᶜ ≤
      (G.neighborFinset u ∩ G.neighborFinset v).card := by
  rw [← compl_edge_neighborhood_complement h, card_sdiff (subset_univ _),card_univ]
  exact Nat.sub_le_sub_left (edgeNeighborhood_le_max Gᶜ h) _

private theorem gamma_le_of_minDegree {G : SimpleGraph V} [Nonempty V] (hd : 0 < G.minDegree) :
    totalDominationNumber G ≤ Fintype.card V - G.minDegree + 1 := by
  have hnpos : 0 < Fintype.card V := Fintype.card_pos
  obtain ⟨D,_,hD⟩ := exists_subset_card_eq (s := (univ : Finset V))
    (n := Fintype.card V - G.minDegree + 1) (by rw [card_univ]; omega)
  apply Nat.sInf_le
  refine ⟨D, ?_, hD⟩
  intro w
  by_contra h
  have hs : G.neighborFinset w ⊆ univ \ D := by
    intro v hv
    exact mem_sdiff.mpr ⟨mem_univ _,fun hmem => h ⟨v,hmem,(G.mem_neighborFinset _ _).mp hv⟩⟩
  have hcard := card_le_card hs
  rw [card_sdiff (subset_univ _),card_univ,card_neighborFinset_eq_degree,hD] at hcard
  have hw := G.minDegree_le_degree w
  omega

private theorem gamma_le_of_common {G : SimpleGraph V} [Nonempty V]
    (he : ∃ u v, Gᶜ.Adj u v)
    (ht : 0 < Fintype.card V - maxEdgeNeighborhood Gᶜ) :
    totalDominationNumber G ≤ G.minDegree -
      (Fintype.card V - maxEdgeNeighborhood Gᶜ) + 2 := by
  let t := Fintype.card V - maxEdgeNeighborhood Gᶜ
  change 0 < t at ht
  obtain ⟨u,hu⟩ := G.exists_minimal_degree_vertex
  let N := G.neighborFinset u
  have hCard : N.card = G.minDegree := (G.card_neighborFinset_eq_degree u).trans hu.symm
  have hN : t ≤ N.card := by
    have h := complement_edge_neighborhood_lower G he
    change t ≤ N.card
    rw [hCard]
    omega
  obtain ⟨D,hsub,hD⟩ := exists_subset_card_eq (s := N) (n := N.card-t+1) (by omega)
  have hdpos : 0 < D.card := by omega
  obtain ⟨v,hv⟩ := Finset.card_pos.mp hdpos
  let R := insert u D
  have hTD : TotalDominates G R := by
    intro w
    by_cases hwu : w=u
    · subst w
      exact ⟨v,mem_insert_of_mem hv,(G.mem_neighborFinset _ _).mp (hsub hv)⟩
    by_cases hwa : G.Adj w u
    · exact ⟨u,mem_insert_self _ _,hwa⟩
    have hcom : Gᶜ.Adj u w := ⟨Ne.symm hwu,fun h => hwa h.symm⟩
    have hb : t ≤ (N ∩ G.neighborFinset w).card := nonadj_common_cap hcom
    by_contra h
    have hS : N ∩ G.neighborFinset w ⊆ N \ D := by
      intro x hx
      obtain ⟨hx,hxw⟩ := mem_inter.mp hx
      exact mem_sdiff.mpr ⟨hx,fun hmem => h ⟨x,mem_insert_of_mem hmem,
        (G.mem_neighborFinset _ _).mp hxw⟩⟩
    have hcard := card_le_card hS
    rw [card_sdiff hsub,hD] at hcard
    omega
  have hr : totalDominationNumber G ≤ R.card := Nat.sInf_le ⟨R,hTD,rfl⟩
  have hcap : R.card ≤ D.card+1 := card_insert_le _ _
  rw [hCard] at hD
  change totalDominationNumber G ≤ G.minDegree - t + 2
  omega

/-- The conjecture when all nonadjacent pairs have a common neighbor.
The hypothesis here is equivalent to the original graph having diameter at
most two (assuming connectedness and a nonempty complement edge set). -/
theorem conjecture305_when_max_lt_order {G : SimpleGraph V}
    (hc : G.Connected) (hn : 3 ≤ Fintype.card V) (he : ∃ u v, Gᶜ.Adj u v)
    (hM : maxEdgeNeighborhood Gᶜ < Fintype.card V) :
    totalDominationNumber G ≤ (2*maxEdgeNeighborhood Gᶜ+2)/3 := by
  haveI : Nonempty V := hc.nonempty
  by_cases ht : maxEdgeNeighborhood Gᶜ ≤ 3
  · exact conjecture305_small_complement_neighborhood hc hn he ht
  have hdeg : 0 < G.minDegree := by
    have hb := complement_edge_neighborhood_lower G he
    omega
  have h₁ := gamma_le_of_minDegree (G := G) hdeg
  have h₂ := gamma_le_of_common he (by omega)
  have h₃ := complement_edge_neighborhood_lower G he
  omega

theorem conjecture305_of_classical_order_bound {G : SimpleGraph V}
    (hc : G.Connected) (hn : 3 ≤ Fintype.card V) (he : ∃ u v, Gᶜ.Adj u v)
    (hb : totalDominationNumber G ≤ (2*Fintype.card V)/3) :
    totalDominationNumber G ≤ (2*maxEdgeNeighborhood Gᶜ+2)/3 := by
  by_cases hh : maxEdgeNeighborhood Gᶜ < Fintype.card V
  · exact conjecture305_when_max_lt_order hc hn he hh
  · omega


theorem max_attained (H : SimpleGraph V) (he : ∃ u v, H.Adj u v) :
    ∃ u v, H.Adj u v ∧ (edgeNeighborhood H u v).card = maxEdgeNeighborhood H := by
  obtain ⟨a,b,hab⟩ := he
  haveI : Nonempty V := ⟨a⟩
  have hpos := at_least_two hab
  obtain ⟨u,_,hu⟩ := exists_mem_eq_sup (univ : Finset V) univ_nonempty
    (fun u => (univ.filter (H.Adj u)).sup fun v => (edgeNeighborhood H u v).card)
  change maxEdgeNeighborhood H = _ at hu
  have hun : (univ.filter (H.Adj u)).Nonempty := by
    by_contra! hn
    rw [not_nonempty_iff_eq_empty.mp hn, Finset.sup_empty] at hu
    change maxEdgeNeighborhood H = 0 at hu
    omega
  obtain ⟨v,hv,hd⟩ := exists_mem_eq_sup (univ.filter (H.Adj u)) hun
    (fun v => (edgeNeighborhood H u v).card)
  exact ⟨u,v,(mem_filter.mp hv).2,(hu.trans hd).symm⟩

theorem conjecture305_integer {G : SimpleGraph V} (hc : G.Connected)
    (hn : 3 ≤ Fintype.card V) (he : ∃ u v, Gᶜ.Adj u v) :
    totalDominationNumber G ≤ (2*maxEdgeNeighborhood Gᶜ+2)/3 := by
  obtain ⟨D,hD,hcard⟩ := Graffiti305Colors.total_dominating_set_order_bound G hc hn
  have hd : totalDominationNumber G ≤ D.card := Nat.sInf_le ⟨D,hD,rfl⟩
  exact conjecture305_of_classical_order_bound hc hn he (by omega)

theorem ceil_two_thirds (m : ℕ) : ⌈(2*(m : ℚ))/3⌉ = (((2*m+2)/3 : ℕ) : ℤ) := by
  rw [Int.ceil_eq_iff]
  let k := (2*m+2)/3
  have hi : 3*k ≤ 2*m+2 := by dsimp [k]; omega
  have hj : 2*m ≤ 3*k := by dsimp [k]; omega
  have h₁ : (3 : ℚ)*(k : ℚ) ≤ 2*(m : ℚ)+2 := by exact_mod_cast hi
  have h₂ : (2 : ℚ)*(m : ℚ) ≤ 3*(k : ℚ) := by exact_mod_cast hj
  simp only [Int.cast_natCast]
  change (k : ℚ) - 1 < 2 * (m : ℚ) / 3 ∧
    2 * (m : ℚ) / 3 ≤ (k : ℚ)
  constructor <;> linarith

/-- Exact ceiling statement on its natural domain: the complement has an edge,
so there is a largest edge neighborhood. -/
theorem conjecture305 {G : SimpleGraph V} (hc : G.Connected)
    (hn : 3 ≤ Fintype.card V) (he : ∃ u v, Gᶜ.Adj u v) :
    (totalDominationNumber G : ℤ) ≤ ⌈(2*(maxEdgeNeighborhood Gᶜ : ℚ))/3⌉ := by
  rw [ceil_two_thirds]
  exact_mod_cast conjecture305_integer hc hn he

theorem empty_edge_max (H : SimpleGraph V) (he : ¬ ∃ u v, H.Adj u v) :
    maxEdgeNeighborhood H = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le_iff.mpr
  intro u _
  apply Finset.sup_le_iff.mpr
  intro v hv
  exact (he ⟨u,v,(mem_filter.mp hv).2⟩).elim

/-- If the undefined empty maximum is instead assigned zero, the proposed
inequality is false on all complete graphs on at least three vertices. -/
theorem fails_if_empty_max_totalized_to_zero {G : SimpleGraph V}
    (hc : G.Connected) (hn : 3 ≤ Fintype.card V) (he : ¬ ∃ u v, Gᶜ.Adj u v) :
    ¬ (totalDominationNumber G : ℤ) ≤ ⌈(2*(maxEdgeNeighborhood Gᶜ : ℚ))/3⌉ := by
  rw [empty_edge_max Gᶜ he, ceil_two_thirds]
  have bound : 2 ≤ totalDominationNumber G := by
    obtain ⟨D,hD,_⟩ := Graffiti305Colors.total_dominating_set_order_bound G hc hn
    have hex : {k : ℕ | ∃ D, TotalDominates G D ∧ D.card = k}.Nonempty := ⟨D.card,D,hD,rfl⟩
    obtain ⟨S,hS,hs⟩ := Nat.sInf_mem hex
    change S.card = totalDominationNumber G at hs
    haveI : Nonempty V := hc.nonempty
    let x : V := Classical.choice ‹Nonempty V›
    obtain ⟨u,hu,_⟩ := hS x
    obtain ⟨v,hv,had⟩ := hS u
    have hcS := Finset.one_lt_card.mpr ⟨u,hu,v,hv,had.ne⟩
    omega
  omega

#print axioms conjecture305
#print axioms fails_if_empty_max_totalized_to_zero
#print axioms conjecture305_of_classical_order_bound
#print axioms conjecture305_when_max_lt_order
#print axioms complement_edge_neighborhood_lower
#print axioms degree_add_one_le_max_if_nonisolated
#print axioms conjecture305_small_complement_neighborhood
end
end Graffiti305
