/-
# A proof of Graffiti.pc #356

[Written on the Wall II #356](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json), marked open in the November 25 snapshot, asks whether, for a tree \(T\) with more than two vertices,
\[
\gamma_t(T) \ge |C(T)|\,\operatorname{dist}_{\rm avg}(L(T)).
\]
Here \(C(T)\) is the vertex center, and \(L(T)\) the leaves. Linked definition 109 averages the nearest-leaf distances over vertices where that distance is positive, namely the nonleaves.

Let the diameter be \(d\) and \(h=\lfloor d/2\rfloor\). These standard tree-center facts follow by taking the midpoint of any diameter path: the center is a vertex for even \(d\), an edge's two endpoints for odd \(d\); every vertex is within distance \(h\) of the center set. To see this, take a longest path \(P\) and attach any off-path vertex \(v\) at its unique branch point \(w\) on \(P\). If \(v\) is at distance \(t\) from \(w\), both \(t+\operatorname{dist}(w,a)\) and \(t+\operatorname{dist}(w,b)\) are at most \(d\), where \(a,b\) are the endpoints of \(P\). Thus \(t\) is at most the smaller of the two distances. It follows that each midpoint vertex has eccentricity \(\lceil d/2\rceil\), and only midpoint vertices can be centers, since distances to \(a,b\) force greater eccentricity elsewhere. The same inequalities put every vertex within distance \(h\) of a midpoint (including the odd case's nearer midpoint).

Root at the center if it is unique, or delete the center edge and root the two resulting trees at its endpoints. Every rooted vertex has depth at most \(h\). Every nonleaf has a child: for a nonroot this follows from having one parent, and each root has a child since a diameter path of length at least two reaches outward from it. Choose one child of each nonleaf. The chosen edges partition all vertices into disjoint downward chains ending at leaves (there is at most one incoming chosen edge, and one outgoing chosen edge except at leaves). A chain with \(k\) nonleaves has \(k\le h\) because depth increases with every edge. Those nonleaves have nearest-leaf distances at most \(1,\ldots,k\) by using the leaf at the chain's end. They contribute at most \(k(h+1)/2\) to the sum of the distances. Consequently
\[
\operatorname{dist}_{\rm avg}(L(T))\le(h+1)/2.
\]

Finally \(\gamma_t(T)\ge\lceil(d+1)/2\rceil\ge h+1\). The first inequality is classical (cited, e.g., in [DeLaViña–Larson–Pepper–Waller](https://math1um.github.io/Research/r05.pdf), §3), and for a tree it follows immediately by covering the \(d+1\) vertices of a diameter path: a vertex on the path has at most two path neighbors, and a vertex outside the path has at most one (otherwise there is a cycle). Since \(|C(T)|\le2\), the desired bound follows.

The [public computational audit](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa), §9a, lists #356 as surviving through order 18. No prior proof of the exact inequality was located.

Replay with Lean and Mathlib v4.19.0. Main theorem: Graffiti356.conjecture356.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega


import Mathlib.Combinatorics.SimpleGraph.Metric

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Finset SimpleGraph
namespace GraffitiPeriphery
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
noncomputable def eccentricity (v : V) : ℕ :=
  (Finset.univ : Finset V).sup (G.dist v)

noncomputable def diameter : ℕ := (Finset.univ : Finset V).sup (eccentricity G)

theorem ecc_bound (x y : V) : G.dist x y ≤ eccentricity G x :=
  Finset.le_sup (f := G.dist x) (Finset.mem_univ y)

theorem diam_bound (x : V) : eccentricity G x ≤ diameter G :=
  Finset.le_sup (f := eccentricity G) (Finset.mem_univ x)


end GraffitiPeriphery
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
  have h4 : G.dist r v ≤ G.dist r (p.getVert 1) + 1 := by
    simpa only [dist_eq_one_iff_adj.mpr h1.symm] using
      (hc.dist_triangle (u := r) (v := p.getVert 1) (w := v))
  exact ⟨_, h1, by omega⟩


end GraffitiBFS


open Finset SimpleGraph GraffitiBFS GraffitiPeriphery
namespace GraffitiTreeRadius

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

abbrev cut (x y : V) : SimpleGraph V := G \ SimpleGraph.fromEdgeSet {s(x,y)}

omit [Fintype V] in
theorem cut_adj {x y u v : V} (h : G.Adj u v) :
    (cut G x y).Adj u v ↔ s(u,v) ≠ s(x,y) := by
  simp [cut,SimpleGraph.sdiff_adj,SimpleGraph.fromEdgeSet_adj,h,h.ne]

omit [Fintype V] in
theorem cut_surround (hG : G.Connected) (x y z : V) :
    (cut G x y).Reachable x z ∨ (cut G x y).Reachable y z := by
  let H := cut G x y
  let side (u : V) := H.Reachable x u ∨ H.Reachable y u
  have step {u v : V} (h : G.Adj u v) (hu : side u) : side v := by
    by_cases hh : s(u,v)=s(x,y)
    · rcases Sym2.eq_iff.mp hh with ⟨_,rfl⟩ | ⟨_,rfl⟩
      · exact Or.inr (SimpleGraph.Reachable.refl _)
      · exact Or.inl (SimpleGraph.Reachable.refl _)
    · have he : H.Adj u v := (cut_adj G h).mpr hh
      exact hu.elim (fun hr => Or.inl (hr.trans he.reachable))
        (fun hr => Or.inr (hr.trans he.reachable))
  have aux {a b : V} (p : G.Walk a b) : side a → side b := by
    induction p with
    | nil => exact id
    | cons ha _ ih => exact fun h => ih (step ha h)
  obtain ⟨p⟩ := hG x z
  exact aux p (Or.inl (SimpleGraph.Reachable.refl _))

omit [Fintype V] in
theorem cross_dist (hT : G.IsTree) {x y a b : V} (hxy : G.Adj x y)
    (ha : (cut G x y).Reachable x a) (hb : (cut G x y).Reachable y b) :
    G.dist a b = G.dist a x + 1 + G.dist y b := by
  let H := cut G x y
  have hdis : ¬ H.Reachable x y :=
    (SimpleGraph.isBridge_iff.mp ((isAcyclic_iff_forall_adj_isBridge.mp hT.IsAcyclic) hxy)).2
  have aux {c d : V} (p : G.Walk c d) (hc : H.Reachable x c) (hd : H.Reachable y d) :
      G.dist c x+1+G.dist y d ≤ p.length := by
    induction p with
    | nil => exact (hdis (hc.trans hd.symm)).elim
    | @cons c v d hv p ih =>
      by_cases he : s(c,v)=s(x,y)
      · rcases Sym2.eq_iff.mp he with ⟨hc',hv'⟩ | ⟨hc',hv'⟩
        · subst c; subst v
          rw [SimpleGraph.dist_self, SimpleGraph.Walk.length_cons]
          have hd := SimpleGraph.dist_le p
          omega
        · exact (hdis (hc' ▸ hc)).elim
      · have hav : H.Adj c v := (cut_adj G hv).mpr he
        have hz := ih (hc.trans hav.reachable) hd
        have ht := hT.isConnected.dist_triangle (u := c) (v := v) (w := x)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hv] at ht
        rw [SimpleGraph.Walk.length_cons]
        omega
  obtain ⟨p,hp⟩ := hT.isConnected.exists_walk_length_eq_dist a b
  apply Nat.le_antisymm
  · have h1 := hT.isConnected.dist_triangle (u := a) (v := x) (w := b)
    have h2 := hT.isConnected.dist_triangle (u := x) (v := y) (w := b)
    have h3 := SimpleGraph.dist_eq_one_iff_adj.mpr hxy
    omega
  · exact hp ▸ aux p ha hb

def IsCenter (x : V) : Prop := ∀ v, eccentricity G x ≤ eccentricity G v

theorem exists_center (h : Nonempty V) : ∃ x, IsCenter G x := by
  obtain ⟨v⟩ := h
  have he : (Finset.univ : Finset V).Nonempty := ⟨v,Finset.mem_univ v⟩
  obtain ⟨x,_,hx⟩ := Finset.exists_mem_eq_inf' he (eccentricity G)
  exact ⟨x,fun w => hx ▸ Finset.inf'_le (eccentricity G) (Finset.mem_univ w)⟩

/-- A finite tree of diameter at most 2k−1 has a center of eccentricity at
    most k. If a center has eccentricity exactly k, there is an adjacent center. -/
theorem center_bound_and_adjacent (hT : G.IsTree) (k : ℕ)
    (hDiam : diameter G ≤ 2*k-1) (x : V) (hx : IsCenter G x) :
    eccentricity G x ≤ k ∧
      (eccentricity G x = k → 0 < k → ∃ y, G.Adj x y ∧ IsCenter G y) := by
  classical
  let r := eccentricity G x
  by_cases hr : r = 0
  · exact ⟨by change r ≤ k; omega, fun he hpos => False.elim (by change r=k at he; omega)⟩
  have hn : (Finset.univ : Finset V).Nonempty := ⟨x,Finset.mem_univ x⟩
  obtain ⟨u,_,hu⟩ := Finset.exists_mem_eq_sup _ hn (G.dist x)
  change r = G.dist x u at hu
  have hxu : x ≠ u := by
    intro he
    have hd : G.dist x u = 0 := by rw [← he,SimpleGraph.dist_self]
    omega
  obtain ⟨y,hxy,hy⟩ := one_step_toward G hT.isConnected u x hxu
  have hdy : G.dist y u+1=r := by
    calc
      G.dist y u+1 = G.dist u y+1 := by rw [SimpleGraph.dist_comm (u:=y)]
      _ = G.dist u x := hy
      _ = G.dist x u := SimpleGraph.dist_comm
      _ = r := hu.symm
  let H := cut G x y
  have huR : H.Reachable y u := by
    rcases cut_surround G hT.isConnected x y u with h | h
    · have hh := cross_dist G hT hxy h (SimpleGraph.Reachable.refl (G := H) y)
      rw [SimpleGraph.dist_self,SimpleGraph.dist_comm (u:=u) (v:=x),
        SimpleGraph.dist_comm (u:=u) (v:=y)] at hh
      omega
    · exact h
  have ybound (k' : ℕ) (hrk : r ≤ k'+1) (hdk : diameter G ≤ r+k'-1)
      (hle : 0 < r+k') :
      eccentricity G y ≤ k' := by
    apply Finset.sup_le
    intro z _
    rcases cut_surround G hT.isConnected x y z with hz | hz
    · have h1 := cross_dist G hT hxy hz huR
      have h2 := cross_dist G hT hxy hz (SimpleGraph.Reachable.refl (G := H) y)
      rw [SimpleGraph.dist_self, Nat.add_zero,
        SimpleGraph.dist_comm (u:=z) (v:=y)] at h2
      have hs := (ecc_bound G z u).trans (diam_bound G z)
      omega
    · have h1 := cross_dist G hT hxy (SimpleGraph.Reachable.refl (G := H) x) hz
      rw [SimpleGraph.dist_self] at h1
      have h2 := ecc_bound G x z
      change G.dist x z ≤ r at h2
      omega
  constructor
  · change r ≤ k
    by_contra! hh
    have hrs : 0 < r := by omega
    have hk : k+1 ≤ r := by omega
    have hd : diameter G ≤ r+(r-1)-1 := by omega
    have h := ybound (r-1) (by omega) hd (by omega)
    have hmin := hx y
    change r ≤ _ at hmin
    omega
  · intro he hk
    change r = k at he
    have h := ybound k (by omega) (by omega) (by omega)
    exact ⟨y,hxy,fun w => h.trans (he ▸ hx w)⟩

#print axioms center_bound_and_adjacent
end GraffitiTreeRadius

open Finset SimpleGraph GraffitiPeriphery GraffitiTreeRadius GraffitiBFS
set_option linter.unusedSectionVars false
set_option warningAsError true
namespace Graffiti380
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

noncomputable def sideVerts (u v : V) : Finset V := by
  classical exact univ.filter (fun x => (cut G u v).Reachable u x)

noncomputable def height (u v : V) := (sideVerts G u v).sup (G.dist u)

lemma side (u v x : V) : x ∈ sideVerts G u v ↔ (cut G u v).Reachable u x := by
  classical simp [sideVerts]

lemma cutSwap (u v : V) : cut G u v = cut G v u := by
  simp only [cut, Sym2.eq_swap (a:=u) (b:=v)]

lemma sideBound {u v x : V} (hx : (cut G u v).Reachable u x) :
    G.dist u x ≤ height G u v :=
  Finset.le_sup (f:=G.dist u) ((side G u v x).mpr hx)

lemma sideHeight (u v : V) :
    ∃ x, (cut G u v).Reachable u x ∧ G.dist u x = height G u v := by
  have hh : (sideVerts G u v).Nonempty :=
    ⟨u,(side G u v u).mpr (Reachable.refl _)⟩
  obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_sup _ hh (G.dist u)
  exact ⟨x,(side G u v x).mp hx,he.symm⟩

lemma eccHeight (ht : G.IsTree) {u v : V} (e : G.Adj u v) :
    eccentricity G u = max (height G u v) (height G v u + 1) := by
  obtain ⟨x,hx,hxe⟩ := sideHeight G u v
  obtain ⟨y,hy,hye⟩ := sideHeight G v u
  have hc := cross_dist G ht e (Reachable.refl (G:=cut G u v) u)
    (by simpa only [← cutSwap G u v] using hy)
  rw [dist_self,Nat.zero_add,hye] at hc
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro z _
    rcases cut_surround G ht.isConnected u v z with h | h
    · exact (sideBound G h).trans (Nat.le_max_left _ _)
    · have he := cross_dist G ht e (Reachable.refl (G:=cut G u v) u) h
      rw [dist_self,Nat.zero_add] at he
      have hm := sideBound G (show (cut G v u).Reachable v z from by
        simpa only [← cutSwap G u v] using h)
      have hmax := Nat.le_max_right (height G u v) (height G v u + 1)
      omega
  · have h1 := ecc_bound G u x
    have h2 := ecc_bound G u y
    rw [hxe] at h1; rw [hc, Nat.add_comm] at h2
    exact Nat.max_le.mpr ⟨h1,h2⟩

lemma centerPair (ht : G.IsTree) {u v : V} (e : G.Adj u v)
    (hu : IsCenter G u) (hv : IsCenter G v) :
    height G u v = height G v u ∧ ∀ x, IsCenter G x ↔ x = u ∨ x = v := by
  have h1 := eccHeight G ht e
  have h2 := eccHeight G ht e.symm
  have q := (hu v).antisymm (hv u)
  rw [h1,h2] at q
  have eH : height G u v = height G v u := by omega
  refine ⟨eH,fun x => ⟨fun hx => ?_,by rintro (rfl|rfl); exact hu; exact hv⟩⟩
  have he := (hx u).antisymm (hu x)
  rw [h1,eH, Nat.max_eq_right (by omega)] at he
  rcases cut_surround G ht.isConnected u v x with hx' | hx'
  · left
    obtain ⟨y,hy,hye⟩ := sideHeight G v u
    have hd := cross_dist G ht e hx' (by simpa only [← cutSwap G u v] using hy)
    have hb := ecc_bound G x y
    rw [hye] at hd
    have hzero : G.dist x u = 0 := by omega
    exact ht.isConnected.dist_eq_zero_iff.mp hzero
  · right
    obtain ⟨y,hy,hye⟩ := sideHeight G u v
    have hd := cross_dist G ht e.symm (by simpa only [cutSwap G u v] using hx')
      (by simpa only [← cutSwap G v u] using hy)
    have hb := ecc_bound G x y
    rw [hye,eH] at hd
    have hzero : G.dist x v = 0 := by omega
    exact ht.isConnected.dist_eq_zero_iff.mp hzero

lemma centerSingleOrPair (ht : G.IsTree) (hne : Nonempty V) :
    (∃ c, ∀ x, IsCenter G x ↔ x = c) ∨
    (∃ u v, G.Adj u v ∧ height G u v = height G v u ∧
      ∀ x, IsCenter G x ↔ x = u ∨ x = v) := by
  classical
  obtain ⟨c,hc⟩ := exists_center G hne
  let r := eccentricity G c
  have dmax : diameter G ≤ 2*r := by
    apply Finset.sup_le
    intro a _
    apply Finset.sup_le
    intro b _
    have ha := ecc_bound G c a
    have hb := ecc_bound G c b
    have hh := ht.isConnected.dist_triangle (u:=a) (v:=c) (w:=b)
    rw [dist_comm (u:=a) (v:=c)] at hh
    omega
  by_cases h : diameter G = 2*r
  · left
    have hU : (univ : Finset V).Nonempty := ⟨c,mem_univ _⟩
    obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup _ hU (eccentricity G)
    obtain ⟨b,_,hb⟩ := Finset.exists_mem_eq_sup _ hU (G.dist a)
    have hab : G.dist a b = 2*r := by
      change eccentricity G a = _ at hb
      exact hb.symm.trans (ha.symm.trans h)
    have midpoint (x : V) (hx : IsCenter G x) :
        ∃ (P : G.Path a b), P.val.getVert r = x := by
      have ex : eccentricity G x = r := (hx c).antisymm (hc x)
      obtain ⟨p,hp⟩ := ht.isConnected.exists_walk_length_eq_dist a x
      obtain ⟨q,hq⟩ := ht.isConnected.exists_walk_length_eq_dist x b
      have h1 := ecc_bound G x a
      have h2 := ecc_bound G x b
      rw [ex,dist_comm (u:=x) (v:=a)] at h1
      rw [ex] at h2
      have hh := ht.isConnected.dist_triangle (u:=a) (v:=x) (w:=b)
      have hl : (p.append q).length = G.dist a b := by
        rw [Walk.length_append,hp,hq]; omega
      refine ⟨⟨p.append q,(p.append q).isPath_of_length_eq_dist hl⟩,?_⟩
      have hrl : r = p.length := by omega
      change (p.append q).getVert r = x
      simp [hrl,Walk.getVert_append]
    refine ⟨c,fun x => ⟨fun hx => ?_,fun e => e.symm ▸ hc⟩⟩
    obtain ⟨p,hp⟩ := midpoint x hx
    obtain ⟨q,hq⟩ := midpoint c hc
    have hEq := ht.IsAcyclic.path_unique p q
    exact hp.symm.trans (hEq ▸ hq)
  · right
    have rpos : 0 < r := by omega
    have hbound : diameter G ≤ 2*r-1 := by omega
    obtain ⟨v,e,hv⟩ := (center_bound_and_adjacent G ht r hbound c hc).2 rfl rpos
    obtain ⟨he,hh⟩ := centerPair G ht e hc hv
    exact ⟨c,v,e,he,hh⟩

#print axioms centerSingleOrPair
end Graffiti380
open Finset SimpleGraph
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option warningAsError true

namespace Graffiti367
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def TD (D : Finset V) := ∀ v, ∃ x ∈ D, G.Adj v x
def degFreq (k : ℕ) := (univ.filter fun v => G.degree v = k).card
def degrees : Finset ℕ := (univ : Finset V).image (fun v => G.degree v)
def nonLeaves := (univ.filter fun v => G.degree v ≠ 1).card

private lemma cardDartFst (S : Finset V) :
    (univ.filter fun d : G.Dart => d.fst ∈ S).card = ∑ v ∈ S, G.degree v := by
  classical
  rw [← sum_card_fiberwise_eq_card_filter (univ : Finset G.Dart) S (fun d => d.fst)]
  exact sum_congr rfl (fun v _ => G.dart_fst_fiber_card_eq_degree v)

private lemma dartEdgeCount (A : Finset (Sym2 V)) (hA : A ⊆ G.edgeFinset) :
    (univ.filter fun d : G.Dart => d.edge ∈ A).card = 2 * A.card := by
  classical
  rw [← sum_card_fiberwise_eq_card_filter (univ : Finset G.Dart) A (fun d => d.edge)]
  rw [← mul_comm, sum_const_nat]
  intro e he
  exact G.dart_edge_fiber_card e (mem_edgeFinset.mp (hA he))

lemma dartPart (D : Finset V) (hD : TD G D)
    (hpos : ∀ v, 0 < G.degree v) (ht : G.IsTree) :
    nonLeaves G + 2 ≤ D.card + 2*(D.card/2) := by
  classical
  let I := univ.filter (fun d : G.Dart => d.fst ∈ D ∧ d.snd ∈ D)
  let O := univ.filter (fun d : G.Dart => d.fst ∉ D ∧ d.snd ∉ D)
  let A := univ.filter (fun d : G.Dart => d.fst ∉ D ∧ d.snd ∈ D)
  let B := univ.filter (fun d : G.Dart => d.fst ∈ D ∧ d.snd ∉ D)
  let R := univ \ D
  have countA : R.card ≤ A.card := by
    let f (v : V) : G.Dart :=
      ⟨(v, Classical.choose (hD v)), (Classical.choose_spec (hD v)).2⟩
    apply card_le_card_of_injOn f
    · intro v hv
      exact mem_filter.mpr ⟨mem_univ _, (mem_sdiff.mp hv).2,
        (Classical.choose_spec (hD v)).1⟩
    · intro v _ w _ e
      exact congrArg (fun d : G.Dart => d.fst) e
  have countI : D.card ≤ I.card := by
    let f (v : V) : G.Dart :=
      ⟨(v, Classical.choose (hD v)), (Classical.choose_spec (hD v)).2⟩
    apply card_le_card_of_injOn f
    · intro v hv
      exact mem_filter.mpr ⟨mem_univ _, hv,(Classical.choose_spec (hD v)).1⟩
    · intro v _ w _ e
      exact congrArg (fun d : G.Dart => d.fst) e
  have ab : A.card = B.card := by
    refine Finset.card_bij' (fun d _ => d.symm) (fun d _ => d.symm) ?_ ?_ ?_ ?_
    · intro d hd
      change d.symm ∈ B
      unfold B
      apply mem_filter.mpr
      exact ⟨mem_univ _,(mem_filter.mp hd).2.2,(mem_filter.mp hd).2.1⟩
    · intro d hd
      change d.symm ∈ A
      unfold A
      apply mem_filter.mpr
      exact ⟨mem_univ _,(mem_filter.mp hd).2.2,(mem_filter.mp hd).2.1⟩
    · intro d _; exact d.symm_symm
    · intro d _; exact d.symm_symm
  have dd1 : Disjoint I B := disjoint_left.mpr (by intro d hi hb; exact (mem_filter.mp hb).2.2 (mem_filter.mp hi).2.2)
  have dd2 : Disjoint O A := disjoint_left.mpr (by intro d ho ha; exact (mem_filter.mp ho).2.2 (mem_filter.mp ha).2.2)
  have dd3 : Disjoint (I ∪ B) (O ∪ A) := by
    apply disjoint_left.mpr
    intro d h1 h2
    simp only [mem_union, I,B,O,A,mem_filter,mem_univ,true_and] at h1 h2
    exact (h1.elim And.left And.left) |> (h2.elim And.left And.left)
  have eqR : O ∪ A = univ.filter (fun d : G.Dart => d.fst ∈ R) := by
    ext d
    by_cases h : d.snd ∈ D <;> simp [O,A,R,h]
  have eqU : (I ∪ B) ∪ (O ∪ A) = univ := by
    ext d
    by_cases h : d.fst ∈ D <;> by_cases j : d.snd ∈ D <;> simp [I,O,A,B,h,j]
  have allC : I.card + O.card + 2*A.card = 2*G.edgeFinset.card := by
    have h := G.dart_card_eq_twice_card_edges
    rw [← card_univ, ← eqU, card_union_of_disjoint dd3, card_union_of_disjoint dd1,
      card_union_of_disjoint dd2, ← ab] at h
    omega
  have sumR : O.card + A.card = ∑ v ∈ R, G.degree v := by
    rw [← card_union_of_disjoint dd2,eqR,cardDartFst]
  let K := G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ D)
  have eqI : I = univ.filter (fun d : G.Dart => d.edge ∈ K) := by
    ext d
    have he := mem_edgeFinset.mpr d.edge_mem
    simp only [mem_filter, mem_univ,true_and]
    rw [show d.edge ∈ K ↔ (∀ v ∈ d.edge, v ∈ D) by simp only [K, mem_filter, he, true_and]]
    change (d ∈ I ↔ ∀ v ∈ s(d.fst,d.snd), v ∈ D)
    simp only [I,mem_filter,mem_univ,true_and,Sym2.forall_mem_pair]
  have iEven : I.card = 2*K.card := by
    rw [eqI, dartEdgeCount G K (filter_subset ..)]
  let NR := R.filter (fun v => G.degree v ≠ 1)
  have cla : R.card + NR.card ≤ O.card + A.card := by
    rw [sumR]
    have hn : (∑ v ∈ R, (1 + if G.degree v ≠ 1 then 1 else 0)) = R.card + NR.card := by
      rw [sum_add_distrib]
      simp [NR,Finset.card_filter]
    rw [← hn]
    exact sum_le_sum (by
      intro v hv
      have hvp := hpos v
      by_cases h : G.degree v = 1 <;> simp [h] <;> omega)
  have clb : nonLeaves G ≤ D.card + NR.card := by
    have h : univ.filter (fun v => G.degree v ≠ 1) ⊆ D ∪ NR := by
      intro v hv
      by_cases h : v ∈ D <;> simp_all [NR,R]
    exact (card_le_card h).trans (card_union_le _ _)
  have parts : R.card + D.card = Fintype.card V := by
    rw [card_sdiff_add_card_eq_card (subset_univ D),card_univ]
  have edges : G.edgeFinset.card + 1 = Fintype.card V := by
    simpa [Nat.card_eq_fintype_card,SimpleGraph.edgeFinset_card] using (isTree_iff_connected_and_card.mp ht).2
  omega

noncomputable def totalDomination : Nat :=
  sInf {k | ∃ D, TD G D ∧ D.card = k}

end Graffiti367
open Finset SimpleGraph GraffitiPeriphery GraffitiTreeRadius GraffitiBFS
set_option linter.unusedSectionVars false
set_option warningAsError true
namespace Graffiti380
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def distC (x : V) : ℕ :=
  sInf {d | ∃ c, IsCenter G c ∧ G.dist c x = d}

noncomputable def eccC : ℕ := (univ : Finset V).sup (distC G)

lemma distC_eq {r x : V} (hr : IsCenter G r)
    (h : ∀ c, IsCenter G c → G.dist r x ≤ G.dist c x) : distC G x = G.dist r x := by
  apply Nat.le_antisymm
  · exact Nat.sInf_le ⟨r,hr,rfl⟩
  · have hn : ({d | ∃ c, IsCenter G c ∧ G.dist c x = d} : Set ℕ).Nonempty :=
      ⟨G.dist r x,r,hr,rfl⟩
    obtain ⟨c,hc,he⟩ := Nat.sInf_mem hn
    unfold distC
    rw [← he]
    exact h c hc

private lemma gluing {r w x : V} (ht : G.IsTree) (e : G.Adj r w)
    (hs : (cut G r w).Reachable r x) :
    G.dist w x = G.dist r x+1 := by
  have h := cross_dist G ht e hs (Reachable.refl (G:=cut G r w) w)
  rw [dist_self,Nat.add_zero,dist_comm (u:=x) (v:=w),dist_comm (u:=x) (v:=r)] at h
  exact h

lemma distSide (ht : G.IsTree) {u v : V} (e : G.Adj u v)
    (hc : ∀ x, IsCenter G x ↔ x = u ∨ x = v) {x : V}
    (hx : (cut G u v).Reachable u x) : distC G x = G.dist u x := by
  apply distC_eq G ((hc u).mpr (Or.inl rfl))
  intro y hy
  rcases (hc y).mp hy with rfl | rfl
  · exact le_rfl
  · rw [gluing G ht e hx]
    omega

lemma eccPair (ht : G.IsTree) {u v : V} (e : G.Adj u v)
    (he : height G u v = height G v u)
    (hc : ∀ x, IsCenter G x ↔ x = u ∨ x = v) : eccC G = height G u v := by
  have hswap (x : V) : IsCenter G x ↔ x = v ∨ x = u :=
    (hc x).trans or_comm
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro x _
    rcases cut_surround G ht.isConnected u v x with hx | hx
    · rw [distSide G ht e hc hx]
      exact sideBound G hx
    · have hs : (cut G v u).Reachable v x := by simpa only [← cutSwap G u v] using hx
      rw [distSide G ht e.symm hswap hs,he]
      exact sideBound G hs
  · obtain ⟨x,hx,hxe⟩ := sideHeight G u v
    rw [← hxe,← distSide G ht e hc hx]
    exact Finset.le_sup (f:=distC G) (mem_univ x)

lemma stepDepth (ht : G.IsTree) {r a b : V} (e : G.Adj a b) :
    G.dist r a+1 = G.dist r b ∨ G.dist r b+1 = G.dist r a := by
  rcases cut_surround G ht.isConnected a b r with h | h
  · exact Or.inl (by simpa only [dist_comm (u:=r)] using (gluing G ht e h).symm)
  · have hs : (cut G b a).Reachable b r := by simpa only [← cutSwap G a b] using h
    exact Or.inr (by simpa only [dist_comm (u:=r)] using (gluing G ht e.symm hs).symm)

lemma parentUnique (ht : G.IsTree) {r a b c : V} (eb : G.Adj a b)
    (ec : G.Adj a c) (hb : G.dist r b+1 = G.dist r a)
    (hc : G.dist r c+1 = G.dist r a) : b = c := by
  obtain ⟨p,hp⟩ := ht.isConnected.exists_walk_length_eq_dist b r
  obtain ⟨q,hq⟩ := ht.isConnected.exists_walk_length_eq_dist c r
  have hpb : (Walk.cons eb p).IsPath := by
    apply Walk.isPath_of_length_eq_dist
    rw [Walk.length_cons,hp,dist_comm (u:=b),dist_comm (u:=a)]
    omega
  have hqc : (Walk.cons ec q).IsPath := by
    apply Walk.isPath_of_length_eq_dist
    rw [Walk.length_cons,hq,dist_comm (u:=c),dist_comm (u:=a)]
    omega
  have he := ht.IsAcyclic.path_unique ⟨_,hpb⟩ ⟨_,hqc⟩
  exact (Walk.cons.inj (congrArg (fun r : G.Path a r => r.val) he)).1

lemma cutClosed (ht : G.IsTree) {r s : V} (e : G.Adj r s) :
    ∀ a, (cut G r s).Reachable r a → a ≠ r → ∀ b, G.Adj a b →
      (cut G r s).Reachable r b := by
  intro a ha hne b hb
  have hba : (cut G r s).Adj a b := (cut_adj G hb).mpr (by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨eq,_⟩ | ⟨_,_⟩
    · exact hne eq
    · rename_i e1 _
      exact (isBridge_iff.mp ((isAcyclic_iff_forall_adj_isBridge.mp ht.IsAcyclic) e)).2 (e1 ▸ ha))
  exact ha.trans hba.reachable

end Graffiti380

open Finset SimpleGraph GraffitiPeriphery GraffitiTreeRadius GraffitiBFS Graffiti380
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option warningAsError true
namespace Graffiti356
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def centers : Finset V := by
  classical exact univ.filter (IsCenter G)
def inner := univ.filter (fun v => G.degree v ≠ 1)
noncomputable def leafDist (v : V) : ℕ := sInf {k | ∃ l, G.degree l = 1 ∧ G.dist v l = k}

private lemma distinctNb {v u : V} (e : G.Adj v u) (hn : G.degree v ≠ 1) :
    ∃ w, G.Adj v w ∧ w ≠ u := by
  classical
  by_contra h
  have he : G.neighborFinset v = {u} := by
    ext x
    rw [G.mem_neighborFinset v x,mem_singleton]
    exact ⟨fun ex => Classical.byContradiction (fun hne => h ⟨x,ex,hne⟩),
      fun eq => eq.symm ▸ e⟩
  exact hn (by rw [← G.card_neighborFinset_eq_degree,he,card_singleton])

private lemma children (ht : G.IsTree) (hn : 2 < Fintype.card V) :
    (∀ v, G.degree v ≠ 1 → ∃ w, G.Adj v w ∧ distC G w = distC G v + 1) ∧
    (∀ a b c, G.Adj a c → G.Adj b c → distC G c = distC G a + 1 →
      distC G c = distC G b + 1 → a = b) := by
  have hc := ht.isConnected
  rcases centerSingleOrPair G ht hc.nonempty with ⟨r,hr⟩ | ⟨r,s,e,he,hC⟩
  · have hDist (x : V) : distC G x = G.dist r x := by
      apply distC_eq G ((hr r).mpr rfl)
      intro c hc
      rw [(hr c).mp hc]
    simp only [hDist]
    constructor
    · intro v hv
      by_cases eq : v = r
      · obtain ⟨w,wn⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
        obtain ⟨p,hp,hpe⟩ := one_step_toward G hc v w wn
        have hdepth : G.dist r v = 0 := by rw [eq,dist_self]
        -- Any first edge goes outward; the path above supplies a nonempty walk.
        obtain ⟨q⟩ := hc v w
        cases q with
        | nil => exact (wn rfl).elim
        | @cons _ a _ ea _ =>
          exact ⟨a,ea,by rw [hdepth,← eq]; exact dist_eq_one_iff_adj.mpr ea⟩
      · obtain ⟨p,ep,hp⟩ := one_step_toward G hc r v eq
        obtain ⟨w,ew,wn⟩ := distinctNb G ep hv
        rcases stepDepth G ht (r:=r) ew with h | h
        · exact ⟨w,ew,h.symm⟩
        · exact (wn (parentUnique G ht ew ep h hp)).elim
    · intro a b c ea eb ha hb
      exact parentUnique G ht ea.symm eb.symm ha.symm hb.symm
  · let R := {x | (cut G r s).Reachable r x}
    let S := {x | (cut G s r).Reachable s x}
    have hswap (x) : IsCenter G x ↔ x = s ∨ x = r := (hC x).trans or_comm
    have dr (x : V) (h : x ∈ R) : distC G x = G.dist r x := distSide G ht e hC h
    have ds (x : V) (h : x ∈ S) : distC G x = G.dist s x := distSide G ht e.symm hswap h
    have rr : r ∈ R := Reachable.refl _
    have ss : s ∈ S := Reachable.refl _
    have noBoth {x : V} (h : x ∈ R) (j : x ∈ S) : False :=
      (isBridge_iff.mp ((isAcyclic_iff_forall_adj_isBridge.mp ht.IsAcyclic) e)).2
        ((show (cut G r s).Reachable r x from h).trans
          (show (cut G r s).Reachable s x from by rw [cutSwap G r s]; exact j).symm)
    have allSide (v : V) : v ∈ R ∨ v ∈ S := by
      rcases cut_surround G hc r s v with h | h
      · exact Or.inl h
      · exact Or.inr (by change (cut G s r).Reachable s v; rw [← cutSwap G r s]; exact h)
    have sameSide (r s : V) (er : G.Adj r s) (A : Set V)
        (aEq : ∀ x, x ∈ A ↔ (cut G r s).Reachable r x)
        (aDepth : ∀ x ∈ A, distC G x = G.dist r x)
        (aRoot : r ∈ A) (v : V) (hv : v ∈ A) (hn : G.degree v ≠ 1) :
        ∃ w, G.Adj v w ∧ distC G w = distC G v + 1 := by
      by_cases vr : v = r
      · subst v
        obtain ⟨w,ew,wn⟩ := distinctNb G er hn
        have hcut : (cut G r s).Adj r w := (cut_adj G ew).mpr (by
          intro h
          rcases Sym2.eq_iff.mp h with ⟨_,e1⟩ | ⟨e1,_⟩
          · exact wn e1
          · exact er.ne e1)
        have hw : w ∈ A := (aEq w).mpr hcut.reachable
        exact ⟨w,ew,by rw [aDepth w hw,aDepth r aRoot,dist_self]; exact dist_eq_one_iff_adj.mpr ew⟩
      · obtain ⟨p,ep,hp⟩ := one_step_toward G hc r v vr
        obtain ⟨w,ew,wn⟩ := distinctNb G ep hn
        have hw := (aEq w).mpr (cutClosed G ht er v ((aEq v).mp hv) vr w ew)
        rcases stepDepth G ht (r:=r) ew with h | h
        · exact ⟨w,ew,by rw [aDepth w hw,aDepth v hv]; exact h.symm⟩
        · exact (wn (parentUnique G ht ew ep h hp)).elim
    constructor
    · intro v hv
      rcases allSide v with h | h
      · exact sameSide r s e R (fun _ => Iff.rfl) dr rr v h hv
      · exact sameSide s r e.symm S (fun _ => Iff.rfl) ds ss v h hv
    · intro a b c ea eb ha hb
      rcases allSide c with h | h
      · have cn : c ≠ r := by intro e; rw [e,dr r rr,dist_self] at ha; omega
        have ar := cutClosed G ht e c h cn a ea.symm
        have br := cutClosed G ht e c h cn b eb.symm
        rw [dr c h,dr a ar] at ha
        rw [dr c h,dr b br] at hb
        exact parentUnique G ht ea.symm eb.symm ha.symm hb.symm
      · have cn : c ≠ s := by intro e; rw [e,ds s ss,dist_self] at ha; omega
        have ar := cutClosed G ht e.symm c h cn a ea.symm
        have br := cutClosed G ht e.symm c h cn b eb.symm
        rw [ds c h,ds a ar] at ha
        rw [ds c h,ds b br] at hb
        exact parentUnique G ht ea.symm eb.symm ha.symm hb.symm

private def fuelLen (f : V → V) (leaf : V → Prop) [DecidablePred leaf] : ℕ → V → ℕ
  | 0, _ => 0
  | n+1, v => if leaf v then 0 else fuelLen f leaf n (f v) + 1

private lemma chooseLength (ht : G.IsTree) (hn : 2 < Fintype.card V) :
    ∃ (f : V → V) (K : V → ℕ),
      (∀ v, K v ≤ eccC G) ∧ (∀ v, leafDist G v ≤ K v) ∧
      (∀ v, G.degree v = 1 → K v = 0) ∧
      (∀ v, G.degree v ≠ 1 → K v = K (f v) + 1) ∧
      (inner G : Set V).InjOn f := by
  classical
  obtain ⟨child,unique⟩ := children G ht hn
  let f (v : V) := if h : G.degree v ≠ 1 then Classical.choose (child v h) else v
  let depth := distC G
  let h := eccC G
  let fuel (v : V) := h - depth v
  let K (v : V) := fuelLen f (fun x => G.degree x = 1) (fuel v) v
  have bDepth (v : V) : depth v ≤ h := Finset.le_sup (f:=distC G) (mem_univ _)
  have spec {v : V} (hv : G.degree v ≠ 1) : G.Adj v (f v) ∧ depth (f v) = depth v+1 := by
    have e : f v = Classical.choose (child v hv) := dif_pos hv
    rw [e]
    exact Classical.choose_spec (child v hv)
  have base {v : V} (hv : G.degree v = 1) : K v = 0 := by
    unfold K
    cases fuel v <;> simp [fuelLen,hv]
  have fuelStep {v : V} (hv : G.degree v ≠ 1) : fuel v = fuel (f v) + 1 := by
    have hd := (spec hv).2
    have hh := bDepth (f v)
    unfold fuel
    omega
  have step {v : V} (hv : G.degree v ≠ 1) : K v = K (f v) + 1 := by
    unfold K
    rw [fuelStep hv]
    simp [fuelLen,hv]
  have ind (n : Nat) (v : V) (hv : fuel v = n) :
      K v ≤ fuel v ∧ ∃ l, G.degree l = 1 ∧ G.dist v l ≤ K v := by
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases eq : G.degree v = 1
      · rw [base eq]
        exact ⟨Nat.zero_le _,v,eq,by rw [dist_self]⟩
      · have ed := fuelStep eq
        have hlt : fuel (f v) < n := by omega
        obtain ⟨hb,l,hl,hle⟩ := ih (fuel (f v)) hlt (f v) rfl
        have ad := dist_eq_one_iff_adj.mpr (spec eq).1
        have tri := ht.isConnected.dist_triangle (u:=v) (v:=f v) (w:=l)
        rw [step eq]
        exact ⟨by omega,l,hl,by omega⟩
  refine ⟨f,K,fun v => (ind _ v rfl).1.trans (Nat.sub_le ..), ?_,fun _ => base,
    fun _ => step,?_⟩
  · intro v
    obtain ⟨l,hl,hd⟩ := (ind _ v rfl).2
    exact (Nat.sInf_le (show ∃ x, G.degree x = 1 ∧ G.dist v x = G.dist v l from ⟨l,hl,rfl⟩)).trans hd
  · intro a ha b hb he
    have hA := (mem_filter.mp (show a ∈ inner G from ha)).2
    have hB := (mem_filter.mp (show b ∈ inner G from hb)).2
    refine unique a b (f a) (spec hA).1 ?_ (spec hA).2 ?_
    · rw [he]; exact (spec hB).1
    · rw [he]; exact (spec hB).2

private lemma avgBound (ht : G.IsTree) (hn : 2 < Fintype.card V) :
    2 * (∑ v ∈ inner G, leafDist G v) ≤ (inner G).card * (eccC G + 1) := by
  classical
  obtain ⟨f,K,hK,hLeaf,hZero,hStep,hInj⟩ := chooseLength G ht hn
  let H := eccC G
  let phi (v : V) : Int := (K v : Int) * ((H : Int) - K v)
  have nonneg (v : V) : 0 ≤ phi v := by
    apply Int.mul_nonneg (Int.ofNat_nonneg _)
    apply Int.sub_nonneg.mpr
    exact_mod_cast hK v
  have imageSum :
      (∑ v ∈ inner G, phi (f v)) ≤ ∑ v ∈ inner G, phi v := by
    have hImage : (∑ v ∈ (inner G).image f, phi v) ≤ ∑ v : V, phi v :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun a _ _ => nonneg a)
    rw [sum_image hInj] at hImage
    have he : (∑ v : V, phi v) = ∑ v ∈ inner G, phi v := by
      symm
      apply sum_subset (subset_univ _)
      intro v _ hv
      have h : G.degree v = 1 := by
        by_contra hn
        exact hv (mem_filter.mpr ⟨mem_univ _,hn⟩)
      simp [phi,hZero v h]
    exact he ▸ hImage
  have hPoint (v : V) (hv : v ∈ inner G) :
      2*(K v : Int) + phi v = (H : Int)+1 + phi (f v) := by
    have hne := (mem_filter.mp hv).2
    have hk : (K v : Int) = (K (f v) : Int)+1 := by exact_mod_cast hStep v hne
    simp only [phi]
    rw [hk]
    ring
  have he : (∑ v ∈ inner G, (2*(K v : Int)+phi v)) =
      ∑ v ∈ inner G, ((H : Int)+1 + phi (f v)) := sum_congr rfl hPoint
  simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at he
  have ho : 2 * (∑ v ∈ inner G, (K v : Int)) ≤ ((inner G).card : Int)*((H : Int)+1) := by
    rw [mul_add,mul_one]
    omega
  have h' : 2*(∑ v ∈ inner G,K v) ≤ (inner G).card*(H+1) := by exact_mod_cast ho
  exact (Nat.mul_le_mul_left _ (sum_le_sum (fun v _ => hLeaf v))).trans h'

private lemma centerFacts (ht : G.IsTree) (hn : Nonempty V) :
    (centers G).card ≤ 2 ∧ 2*eccC G ≤ diameter G := by
  classical
  rcases centerSingleOrPair G ht hn with ⟨r,hr⟩ | ⟨r,s,e,he,hC⟩
  · have hcen : centers G = {r} := by ext v; simp [centers,hr v]
    refine ⟨by simp [hcen],?_⟩
    have hf : distC G = G.dist r := by
      funext v
      apply distC_eq G ((hr r).mpr rfl)
      intro c hc
      rw [(hr c).mp hc]
    have hE : eccC G = eccentricity G r := by simp only [eccC,eccentricity,hf]
    rw [hE]
    by_contra hen
    have hpos : 0 < eccentricity G r := by omega
    obtain ⟨q,e,h⟩ := (center_bound_and_adjacent G ht (eccentricity G r)
      (by omega) r ((hr r).mpr rfl)).2 rfl hpos
    exact e.ne ((hr q).mp h).symm
  · have hcen : centers G = {r,s} := by ext v; simp [centers,hC v]
    refine ⟨by rw [hcen]; exact (card_insert_le _ _).trans (by simp),?_⟩
    rw [eccPair G ht e he hC]
    obtain ⟨a,ha,ha'⟩ := sideHeight G r s
    obtain ⟨b,hb,hb'⟩ := sideHeight G s r
    have hd := cross_dist G ht e ha (show (cut G r s).Reachable s b from by
      rw [cutSwap G r s]; exact hb)
    rw [dist_comm (u:=a) (v:=r),ha',hb',← he] at hd
    have hbnd := (ecc_bound G a b).trans (diam_bound G a)
    omega

private lemma lengthTake {a b : V} (p : G.Walk a b) (i : Nat) : (p.take i).length ≤ i := by
  induction p generalizing i with
  | nil => simp [Walk.take]
  | cons e w ih =>
    cases i with
    | zero => simp [Walk.take]
    | succ i => simpa [Walk.take,Walk.length_cons] using Nat.succ_le_succ (ih i)

private lemma lengthDrop {a b : V} (p : G.Walk a b) (i : Nat) :
    (p.drop i).length ≤ p.length-i := by
  induction p generalizing i with
  | nil => simp [Walk.drop]
  | cons e w ih =>
    cases i with
    | zero => simp [Walk.drop]
    | succ i => simpa [Walk.drop,Walk.length_cons,Nat.add_sub_add_right] using ih i

private lemma noTriangle (ht : G.IsTree) {a b c : V}
    (ab : G.Adj a b) (ac : G.Adj a c) (bc : G.Adj b c) : False := by
  have bc' : (cut G a b).Adj b c := (cut_adj G bc).mpr (by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨ha,_⟩ | ⟨_,ha⟩
    · exact ab.ne ha.symm
    · exact ac.ne ha.symm)
  have ca' : (cut G a b).Adj c a := (cut_adj G ac.symm).mpr (by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨ha,_⟩ | ⟨ha,_⟩
    · exact ac.ne ha.symm
    · exact bc.ne ha.symm)
  exact (isBridge_iff.mp ((isAcyclic_iff_forall_adj_isBridge.mp ht.IsAcyclic) ab)).2
    (bc'.reachable.trans ca'.reachable).symm

private lemma diameterBound (ht : G.IsTree) (D : Finset V) (hD : Graffiti367.TD G D) :
    diameter G + 1 ≤ 2*D.card := by
  classical
  obtain ⟨v₀⟩ := ht.isConnected.nonempty
  have ne : (univ : Finset V).Nonempty := ⟨v₀,mem_univ _⟩
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_eq_sup _ ne (eccentricity G)
  obtain ⟨b,_,hb⟩ := Finset.exists_mem_eq_sup _ ne (G.dist a)
  obtain ⟨p,hp⟩ := ht.isConnected.exists_walk_length_eq_dist a b
  have pLen : p.length = diameter G := hp.trans (hb.symm.trans ha.symm)
  let S := range (p.length+1)
  let f (i : Nat) := Classical.choose (hD (p.getVert i))
  have fd (i : Nat) : f i ∈ D := (Classical.choose_spec (hD (p.getVert i))).1
  have fe (i : Nat) : G.Adj (p.getVert i) (f i) := (Classical.choose_spec (hD (p.getVert i))).2
  have sub (i : Nat) : G.dist a (p.getVert i) ≤ i :=
    (dist_le (p.take i)).trans (lengthTake G p i)
  have tail (j : Nat) : G.dist (p.getVert j) b ≤ p.length-j :=
    (dist_le (p.drop j)).trans (lengthDrop G p j)
  have indexSpan {i j : Nat} (hj : j ∈ S) (eq : f i = f j) : j ≤ i+2 := by
    have eat := ht.isConnected.dist_triangle (u:=a) (v:=p.getVert i) (w:=p.getVert j)
    have finish := ht.isConnected.dist_triangle (u:=a) (v:=p.getVert j) (w:=b)
    have mid := ht.isConnected.dist_triangle (u:=p.getVert i) (v:=f i) (w:=p.getVert j)
    have e1 := dist_eq_one_iff_adj.mpr (fe i)
    have e2 := dist_eq_one_iff_adj.mpr (fe j).symm
    rw [← eq] at e2
    have hs := sub i
    have htail := tail j
    have jle : j < p.length+1 := mem_range.mp hj
    omega
  have noConsec {i : Nat} (h : i < p.length) (eq : f i = f (i+1)) : False := by
    have e1 := fe i
    have e2 := fe (i+1)
    rw [← eq] at e2
    exact noTriangle G ht e1.symm e2.symm (p.adj_getVert_succ h)
  have fiber (x : V) : (S.filter (fun n => f n = x)).card ≤ 2 := by
    let F := S.filter (fun i => f i = x)
    by_cases he : F.Nonempty
    · let i := F.min' he
      have hi : i ∈ F := F.min'_mem he
      have hsub : F ⊆ ({i,i+2} : Finset Nat) := by
        intro j hj
        have e := (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
        have hspan := indexSpan (mem_filter.mp hj).1 e
        have hmin : i ≤ j := F.min'_le j hj
        have hne : j ≠ i+1 := by
          intro e'
          have hR : j < p.length+1 := mem_range.mp (mem_filter.mp hj).1
          rw [e'] at e hR
          exact noConsec (by omega) e
        simp only [mem_insert, mem_singleton]
        omega
      exact (card_le_card hsub).trans ((card_insert_le _ _).trans (by simp))
    · change F.card ≤ 2
      rw [Finset.not_nonempty_iff_eq_empty.mp he,card_empty]
      decide
  have count := Finset.card_eq_sum_card_fiberwise
    (s:=S) (t:=D) (f:=f) (fun i _ => fd i)
  have up : (∑ x ∈ D, (S.filter fun i => f i = x).card) ≤ 2*D.card := by
    calc
      _ ≤ ∑ _x ∈ D, (2 : Nat) := sum_le_sum (fun x _ => fiber x)
      _ = _ := by simp [mul_comm]
  have hs : S.card = p.length+1 := card_range _
  omega

/-- Definition 109 averages exactly the vertices with positive nearest-set distance. -/
theorem inner_exact (ht : G.IsTree) (hn : 2 < Fintype.card V) (v : V) :
    v ∈ inner G ↔ 0 < leafDist G v := by
  classical
  obtain ⟨a⟩ := ht.isConnected.nonempty
  obtain ⟨w,_,hMax⟩ := Finset.exists_mem_eq_sup _ (show (univ : Finset V).Nonempty from ⟨a,mem_univ _⟩)
    (distC G)
  have hw : G.degree w = 1 := by
    by_contra hh
    obtain ⟨x,_,h⟩ := (children G ht hn).1 w hh
    have h' := Finset.le_sup (f:=distC G) (mem_univ x)
    rw [hMax] at h'
    omega
  have hSet : ({k | ∃ l, G.degree l = 1 ∧ G.dist v l = k} : Set Nat).Nonempty :=
    ⟨G.dist v w,w,hw,rfl⟩
  obtain ⟨l,hl,he⟩ := Nat.sInf_mem hSet
  change G.dist v l = leafDist G v at he
  constructor
  · intro hv
    have hh : G.degree v ≠ 1 := (mem_filter.mp hv).2
    have nvl : v ≠ l := fun e => hh (e.symm ▸ hl)
    rw [← he]
    exact ht.isConnected.pos_dist_of_ne nvl
  · intro h
    apply mem_filter.mpr
    refine ⟨mem_univ _, fun he => ?_⟩
    have h0 : leafDist G v ≤ 0 := by
      unfold leafDist
      exact Nat.sInf_le ⟨v,he,dist_self⟩
    omega

theorem inner_nonempty (ht : G.IsTree) (hn : 2 < Fintype.card V) : 0 < (inner G).card := by
  classical
  by_contra hh
  have hEmpty : (inner G).card = 0 := by omega
  have dd (v : V) : G.degree v = 1 := by
    by_contra hn
    have hm : v ∈ inner G := mem_filter.mpr ⟨mem_univ _,hn⟩
    have := Finset.card_pos.mpr ⟨v,hm⟩
    omega
  have sum := G.sum_degrees_eq_twice_card_edges
  simp only [dd,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Nat.cast_id] at sum
  have edges : G.edgeFinset.card + 1 = Fintype.card V := by
    simpa [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
      (isTree_iff_connected_and_card.mp ht).2
  omega

/-- The #356 bound, with the finite average's positive denominator cleared. -/
theorem conjecture356 (ht : G.IsTree) (hn : 2 < Fintype.card V) :
    (centers G).card * (∑ v ∈ inner G, leafDist G v) ≤
      Graffiti367.totalDomination G * (inner G).card := by
  classical
  have hD : Graffiti367.TD G univ := by
    intro v
    obtain ⟨w,hne⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
    obtain ⟨p⟩ := ht.isConnected v w
    cases p with
    | nil => exact (hne rfl).elim
    | @cons _ u _ he _ => exact ⟨u,mem_univ _,he⟩
  have ha : ({k : Nat | ∃ D, Graffiti367.TD G D ∧ D.card = k} : Set Nat).Nonempty :=
    ⟨_,_,hD,rfl⟩
  obtain ⟨D,hD,he⟩ := Nat.sInf_mem ha
  rw [show Graffiti367.totalDomination G = D.card from he.symm]
  obtain ⟨hc,hc'⟩ := centerFacts G ht ht.isConnected.nonempty
  have hh := diameterBound G ht D hD
  have h : eccC G + 1 ≤ D.card := by omega
  calc
    _ ≤ 2 * (∑ v ∈ inner G, leafDist G v) := Nat.mul_le_mul_right _ hc
    _ ≤ (inner G).card * (eccC G+1) := avgBound G ht hn
    _ ≤ _ := by rw [Nat.mul_comm D.card]; exact Nat.mul_le_mul_left _ h

#print axioms inner_exact
#print axioms inner_nonempty
#print axioms conjecture356
end Graffiti356
