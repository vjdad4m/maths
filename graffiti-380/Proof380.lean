/-
# Graffiti.pc #380 on the positive-denominator domain

The [official catalogue JSON](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) lists #380 as open. For a tree \(T\) of order greater than two it prints \(\gamma_t(T)\ge |D_{\rm even}(T)|/(\operatorname{ecc}(C)-1)\), where \(C\) is the set of centers. Definition 52 specifies the greatest distance to the nearest member of the set; this is not the usual vertex radius when the tree has two centers.

**Domain caveat.** The source does not require \(\operatorname{ecc}(C)>1\), but the quotient is undefined when \(\operatorname{ecc}(C)=1\); for example \(P_3\) has center its middle vertex and a nonzero even-degree count. Interpreting the assertion as the unconditionally cross-multiplied inequality would make this example a counterexample. The proof below treats all trees where the displayed quotient is defined (positive denominator).

If \(\operatorname{ecc}(C)\ge3\), every even-degree vertex is a nonleaf. The established tree bound of [Chellali–Haynes](https://www.researchgate.net/profile/Teresa-Haynes-2/publication/252473513_A_note_on_the_total_domination_number_of_a_tree/links/0a85e53bdc97098fae000000/A-note-on-the-total-domination-number-of-a-tree.pdf) says \(n+2-L\le 2\gamma_t(T)\), so \(|D_{\rm even}|\le 2\gamma_t(T)-2\), which suffices.

Suppose \(\operatorname{ecc}(C)=2\). Root the tree at its central vertex or at both endpoints of the central edge. All vertices have depth at most two, so every noncentral nonleaf has a leaf child and belongs to every total dominating set \(D\). In the single-center case there is a vertex at depth two. In the two-center case each central side has a vertex of depth two: the two side heights are equal, since if the heights at the two endpoints of the central edge are \(a,b\), the respective eccentricities are \(\max(a,b+1)\) and \(\max(a+1,b)\), equal only if \(a=b\). For any even-degree center outside \(D\), choose the parent of a depth-two vertex on its side. This chosen parent has precisely the center and some leaves as neighbors. Because its center was omitted from \(D\), the parent must have a leaf neighbor in \(D\). Charge the omitted center to such a leaf; the two central sides are disjoint, so these leaf charges are distinct. Charge every other even-degree vertex to itself in \(D\). The map is injective, since every leaf has odd degree. Thus \(|D_{\rm even}|\le |D|\), and taking \(D\) minimum finishes the proof.

The [public audit](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa), §§7ia and 9a, tested a positive-denominator version. It did not provide a proof. No earlier proof of this exact positive-denominator form was located.

Replay with Lean 4.19.0 and Mathlib v4.19.0. The two conclusions are
Graffiti380.conjecture380_positive and Graffiti380.denominatorZero380.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega


import Mathlib.Combinatorics.SimpleGraph.Metric

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
def evenVertices := (univ : Finset V).filter (fun x => G.degree x % 2 = 0)

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

private lemma leafUnique {a b c : V} (ha : G.degree a = 1)
    (eb : G.Adj a b) (ec : G.Adj a c) : b = c := by
  have h : (G.neighborFinset a).card ≤ 1 := by rw [G.card_neighborFinset_eq_degree,ha]
  exact Finset.card_le_one.mp h b ((G.mem_neighborFinset a b).mpr eb)
    c ((G.mem_neighborFinset a c).mpr ec)

private lemma degreeTwoRegion (ht : G.IsTree) (r : V) (R : Set V)
    (closed : ∀ a ∈ R, a ≠ r → ∀ b, G.Adj a b → b ∈ R)
    (bound : ∀ a ∈ R, G.dist r a ≤ 2) :
    (∀ a ∈ R, G.dist r a = 2 → G.degree a = 1) ∧
    (∀ a ∈ R, G.dist r a = 1 → ∀ b, G.Adj a b →
      b = r ∨ (b ∈ R ∧ G.degree b = 1)) := by
  have l2 (a : V) (ha : a ∈ R) (he : G.dist r a = 2) : G.degree a = 1 := by
    have ne : a ≠ r := fun h => by rw [h,dist_self] at he; omega
    obtain ⟨p,ep,hp⟩ := one_step_toward G ht.isConnected r a ne
    have sub : G.neighborFinset a = {p} := by
      ext b
      rw [G.mem_neighborFinset a b,mem_singleton]
      refine ⟨fun eb => ?_,fun e => e.symm ▸ ep⟩
      have hb := bound b (closed a ha ne b eb)
      rcases stepDepth G ht (r:=r) eb with h | h
      · omega
      · exact parentUnique G ht eb ep h hp
    rw [← G.card_neighborFinset_eq_degree,sub,card_singleton]
  refine ⟨l2, fun a ha he b eb => ?_⟩
  have ne : a ≠ r := fun h => by rw [h,dist_self] at he; omega
  have hb := closed a ha ne b eb
  rcases stepDepth G ht (r:=r) eb with h | h
  · exact Or.inr ⟨hb,l2 b hb (by omega)⟩
  · exact Or.inl ((ht.isConnected.dist_eq_zero_iff.mp (by omega : G.dist r b = 0)).symm)

private lemma outsideRegion (ht : G.IsTree) (r : V) (R : Set V)
    (closed : ∀ a ∈ R, a ≠ r → ∀ b, G.Adj a b → b ∈ R)
    (bound : ∀ a ∈ R, G.dist r a ≤ 2) (D : Finset V) (hD : Graffiti367.TD G D)
    {a : V} (ha : a ∈ R) (ne : a ≠ r) (hn : G.degree a ≠ 1) : a ∈ D := by
  have hpos := ht.isConnected.pos_dist_of_ne ne.symm
  have hle := bound a ha
  obtain ⟨h2,h1⟩ := degreeTwoRegion G ht r R closed bound
  have hdist : G.dist r a = 1 := by
    by_contra h'; exact hn (h2 a ha (by omega))
  have ad := (dist_eq_one_iff_adj.mp hdist).symm
  have f : ∃ b, G.Adj a b ∧ b ≠ r := by
    by_contra hh
    have eq : G.neighborFinset a = {r} := by
      ext b
      rw [G.mem_neighborFinset a b,mem_singleton]
      exact ⟨fun e => Classical.byContradiction (fun ne => hh ⟨b,e,ne⟩),fun h => h.symm ▸ ad⟩
    exact hn (by rw [← G.card_neighborFinset_eq_degree,eq,card_singleton])
  obtain ⟨b,eb,bne⟩ := f
  obtain ⟨d,hd,ed⟩ := hD b
  have bl := (h1 a ha hdist b eb).resolve_left bne
  exact (leafUnique G bl.2 ed eb.symm) ▸ hd

private lemma chargeRoot (ht : G.IsTree) (r : V) (R : Set V)
    (closed : ∀ a ∈ R, a ≠ r → ∀ b, G.Adj a b → b ∈ R)
    (bound : ∀ a ∈ R, G.dist r a ≤ 2) (D : Finset V) (hD : Graffiti367.TD G D)
    (absent : r ∉ D) {x : V} (hx : x ∈ R) (he : G.dist r x = 2) :
    ∃ l ∈ D, l ∈ R ∧ G.degree l = 1 := by
  have ne : x ≠ r := fun h => by rw [h,dist_self] at he; omega
  obtain ⟨a,ea,hax⟩ := one_step_toward G ht.isConnected r x ne
  have ha := closed x hx ne a ea
  obtain ⟨l,hl,el⟩ := hD a
  have hb := (degreeTwoRegion G ht r R closed bound).2 a ha (by omega) l el
  exact ⟨l,hl,hb.resolve_left (fun h => absent (h ▸ hl))⟩

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

private lemma chargeCounting (D : Finset V) (Q : V → V → Prop)
    (existsCharge : ∀ x ∈ evenVertices G, x ∉ D → ∃ l ∈ D, G.degree l = 1 ∧ Q x l)
    (disjointCharge : ∀ x ∈ evenVertices G, ∀ y ∈ evenVertices G, x ∉ D → y ∉ D →
      ∀ l, Q x l → Q y l → x = y) :
    (evenVertices G).card ≤ D.card := by
  classical
  let f (x : V) := if h : x ∈ evenVertices G ∧ x ∉ D
    then Classical.choose (existsCharge x h.1 h.2) else x
  have props {x} (ex : x ∈ evenVertices G) (h : x ∉ D) :
      f x ∈ D ∧ G.degree (f x) = 1 ∧ Q x (f x) := by
    have e : f x = Classical.choose (existsCharge x ex h) :=
      dif_pos (show x ∈ evenVertices G ∧ x ∉ D from ⟨ex,h⟩)
    rw [e]
    exact Classical.choose_spec (existsCharge x ex h)
  have ident {x} (h : x ∈ D) : f x = x := by simp [f,h]
  apply card_le_card_of_injOn f
  · intro x ex
    by_cases h : x ∈ D
    · rw [ident h]; exact h
    · exact (props ex h).1
  · intro x hx y hy he
    have hx : x ∈ evenVertices G := hx
    have hy : y ∈ evenVertices G := hy
    by_cases hs : x ∈ D <;> by_cases ht : y ∈ D
    · rwa [ident hs,ident ht] at he
    · have e := (props hy ht).2.1
      have h := (mem_filter.mp hx).2
      rw [ident hs] at he
      rw [he,e] at h
      omega
    · have e := (props hx hs).2.1
      have h := (mem_filter.mp hy).2
      rw [ident ht] at he
      rw [← he,e] at h
      omega
    · exact disjointCharge x hx y hy hs ht (f x)
        (props hx hs).2.2 (he.symm ▸ (props hy ht).2.2)

private lemma boundSmall (ht : G.IsTree) (hn : Nonempty V) (hE : eccC G = 2)
    (D : Finset V) (hD : Graffiti367.TD G D) : (evenVertices G).card ≤ D.card := by
  classical
  have ev {x : V} (hx : x ∈ evenVertices G) : G.degree x ≠ 1 := by
    have he := (mem_filter.mp hx).2
    omega
  rcases centerSingleOrPair G ht hn with ⟨r,hr⟩ | ⟨r,s,e,he,hC⟩
  · have distEq (x : V) : distC G x = G.dist r x := by
      apply distC_eq G ((hr r).mpr rfl)
      intro y hy
      obtain rfl := (hr y).mp hy
      exact le_rfl
    have closed : ∀ a ∈ (Set.univ : Set V), a ≠ r → ∀ b, G.Adj a b →
        b ∈ (Set.univ : Set V) := by simp
    have bound : ∀ a ∈ (Set.univ : Set V), G.dist r a ≤ 2 := by
      intro a _
      rw [← distEq a, ← hE]
      exact Finset.le_sup (f:=distC G) (mem_univ a)
    have hu : (univ : Finset V).Nonempty := ⟨r,mem_univ _⟩
    obtain ⟨x,_,hx⟩ := Finset.exists_mem_eq_sup _ hu (distC G)
    change eccC G = distC G x at hx
    rw [hE,distEq x] at hx
    apply chargeCounting G D (fun c _ => c = r)
    · intro c hc cD
      have ec : c = r := by
        by_contra ne
        exact cD (outsideRegion G ht r Set.univ closed bound D hD trivial ne (ev hc))
      obtain ⟨l,hl,_,hdeg⟩ :=
        chargeRoot G ht r Set.univ closed bound D hD (ec ▸ cD) trivial hx.symm
      exact ⟨l,hl,hdeg,ec⟩
    · intro _ _ _ _ _ _ _ h j
      exact h.trans j.symm
  · let R := {x | (cut G r s).Reachable r x}
    let S := {x | (cut G s r).Reachable s x}
    have eR : height G r s = 2 := (eccPair G ht e he hC).symm.trans hE
    have eS : height G s r = 2 := he.symm.trans eR
    have bR (x : V) (hx : x ∈ R) : G.dist r x ≤ 2 := eR ▸ sideBound G hx
    have bS (x : V) (hx : x ∈ S) : G.dist s x ≤ 2 := eS ▸ sideBound G hx
    have cR (x : V) (hx : x ∈ R) (xn : x ≠ r) (y : V) (h : G.Adj x y) : y ∈ R :=
      cutClosed G ht e x hx xn y h
    have cS (x : V) (hx : x ∈ S) (xn : x ≠ s) (y : V) (h : G.Adj x y) : y ∈ S :=
      cutClosed G ht e.symm x hx xn y h
    have noBoth {l : V} (hl : l ∈ R) (hl' : l ∈ S) : False :=
      (isBridge_iff.mp ((isAcyclic_iff_forall_adj_isBridge.mp ht.IsAcyclic) e)).2
        ((show (cut G r s).Reachable r l from hl).trans
          (show (cut G r s).Reachable s l from by rw [cutSwap G r s]; exact hl').symm)
    have allSide (x : V) : x ∈ R ∨ x ∈ S := by
      rcases cut_surround G ht.isConnected r s x with h | h
      · exact Or.inl h
      · exact Or.inr (by change (cut G s r).Reachable s x; rw [← cutSwap G r s]; exact h)
    have isCenter {x : V} (hx : x ∈ evenVertices G) (hn : x ∉ D) : x = r ∨ x = s := by
      rcases allSide x with hr | hs
      · exact Or.inl (Classical.byContradiction (fun h => hn
          (outsideRegion G ht r R cR bR D hD hr h (ev hx))))
      · exact Or.inr (Classical.byContradiction (fun h => hn
          (outsideRegion G ht s S cS bS D hD hs h (ev hx))))
    obtain ⟨a,ha,hae⟩ := sideHeight G r s
    obtain ⟨b,hb,hbe⟩ := sideHeight G s r
    apply chargeCounting G D (fun x l => (x = r ∧ l ∈ R) ∨ (x = s ∧ l ∈ S))
    · intro x hx xn
      rcases isCenter hx xn with eq | eq
      · obtain ⟨l,hl,hr,hdeg⟩ := chargeRoot G ht r R cR bR D hD (eq ▸ xn) ha (hae.trans eR)
        exact ⟨l,hl,hdeg,Or.inl ⟨eq,hr⟩⟩
      · obtain ⟨l,hl,hs,hdeg⟩ := chargeRoot G ht s S cS bS D hD (eq ▸ xn) hb (hbe.trans eS)
        exact ⟨l,hl,hdeg,Or.inr ⟨eq,hs⟩⟩
    · intro x _ y _ _ _ l h j
      rcases h with ⟨h,lR⟩ | ⟨h,lS⟩ <;> rcases j with ⟨j,lR'⟩ | ⟨j,lS'⟩
      · exact h.trans j.symm
      · exact (noBoth lR lS').elim
      · exact (noBoth lR' lS).elim
      · exact h.trans j.symm

/-- The displayed #380 inequality on its positive-denominator domain. -/
theorem conjecture380_positive (ht : G.IsTree) (hn : 2 < Fintype.card V)
    (hE : 1 < eccC G) :
    (evenVertices G).card ≤ Graffiti367.totalDomination G * (eccC G-1) := by
  classical
  have nh (v : V) : ∃ u, G.Adj v u := by
    obtain ⟨w,hne⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
    obtain ⟨p⟩ := ht.isConnected v w
    cases p with
    | nil => exact (hne rfl).elim
    | @cons _ u _ he _ => exact ⟨u,he⟩
  have hd : Graffiti367.TD G univ := fun x => by
    obtain ⟨u,he⟩ := nh x
    exact ⟨u,mem_univ _,he⟩
  have ha : ({k : Nat | ∃ D, Graffiti367.TD G D ∧ D.card = k} : Set Nat).Nonempty :=
    ⟨_,_,hd,rfl⟩
  obtain ⟨D,hD,he⟩ := Nat.sInf_mem ha
  rw [show Graffiti367.totalDomination G = D.card from he.symm]
  by_cases hE' : eccC G = 2
  · rw [hE']
    simp only [Nat.reduceSub,Nat.mul_one]
    exact boundSmall G ht ht.isConnected.nonempty hE' D hD
  have hpos (v : V) : 0 < G.degree v := by
    obtain ⟨u,hu⟩ := nh v
    rw [← G.card_neighborFinset_eq_degree]
    exact card_pos.mpr ⟨u,(G.mem_neighborFinset v u).mpr hu⟩
  have hge := Graffiti367.dartPart G D hD hpos ht
  have hsl : evenVertices G ⊆ univ.filter (fun v => G.degree v ≠ 1) := by
    intro x hx
    have he := (mem_filter.mp hx).2
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  have hec : (evenVertices G).card ≤ Graffiti367.nonLeaves G := card_le_card hsl
  have hprod : D.card * 2 ≤ D.card * (eccC G-1) := Nat.mul_le_mul_left _ (by omega)
  omega

#print axioms conjecture380_positive
end Graffiti380

namespace Graffiti380
def P3 : SimpleGraph (Fin 3) := pathGraph 3
instance : DecidableRel P3.Adj := fun _ _ => decidable_of_iff _ pathGraph_adj.symm

theorem denominatorZero380 :
    P3.IsTree ∧ 2 < Fintype.card (Fin 3) ∧ eccC P3 = 1 ∧
      0 < (evenVertices P3).card ∧
      Graffiti367.totalDomination P3 * (eccC P3 - 1) < (evenVertices P3).card := by
  have hc : P3.Connected := pathGraph_connected 2
  have ht : P3.IsTree := by
    apply isTree_iff_connected_and_card.mpr
    refine ⟨hc, ?_⟩
    have hh := P3.sum_degrees_eq_twice_card_edges
    have he : (∑ v : Fin 3, P3.degree v) = 4 := by decide
    rw [he] at hh
    simp only [Nat.card_eq_fintype_card, ← edgeFinset_card,Fintype.card_fin]
    omega
  have h01 : P3.Adj 0 1 := by decide
  have h12 : P3.Adj 1 2 := by decide
  have d₀ : P3.dist 1 0 = 1 := dist_eq_one_iff_adj.mpr h01.symm
  have d₂ : P3.dist 1 2 = 1 := dist_eq_one_iff_adj.mpr h12
  have hm : eccentricity P3 1 = 1 := by
    apply Nat.le_antisymm
    · apply Finset.sup_le
      intro x _
      have options : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2 := by decide
      rcases options x with e | e | e <;> simp [e,d₀,d₂,dist_self]
    · rw [← d₀]
      exact ecc_bound P3 1 0
  have hd : 2 ≤ P3.dist 0 2 := by
    have hp := hc.pos_dist_of_ne (show (0 : Fin 3) ≠ 2 by decide)
    have hd : P3.dist 0 2 ≠ 1 := by
      intro h
      exact (show ¬ P3.Adj 0 2 by decide) (dist_eq_one_iff_adj.mp h)
    omega
  have hctr (x : Fin 3) : IsCenter P3 x ↔ x = 1 := by
    have options : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2 := by decide
    have b₀ := hd.trans (ecc_bound P3 0 2)
    have hI : IsCenter P3 1 := by
      intro y
      rcases options y with e | e | e
      · rw [e,hm]; omega
      · rw [e]
      · rw [e,hm]
        have hb := ecc_bound P3 2 0
        rw [dist_comm (u:=2) (v:=0)] at hb
        omega
    constructor
    · intro h
      have hle := h 1
      rw [hm] at hle
      rcases options x with e | e | e
      · rw [e] at hle; omega
      · exact e
      · rw [e] at hle
        have hb := ecc_bound P3 2 0
        rw [dist_comm (u:=2) (v:=0)] at hb
        omega
    · intro h
      rw [h]
      exact hI
  have hf : distC P3 = P3.dist 1 := by
    funext x
    refine distC_eq P3 ((hctr 1).mpr rfl) ?_
    intro y hy
    rw [(hctr y).mp hy]
  have hE : eccC P3 = 1 := by
    unfold eccC
    rw [hf]
    exact hm
  have hEv : 0 < (evenVertices P3).card := by decide
  exact ⟨ht,by decide,hE,hEv,by simpa [hE] using hEv⟩

#print axioms denominatorZero380
end Graffiti380
