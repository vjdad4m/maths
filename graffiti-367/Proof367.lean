/-
# Graffiti.pc #367: proof for a unique mode, disproof when ties count

[Written on the Wall II, #367](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json), marked open in its November 25 snapshot, and [DeLaViña–Larson–Pepper–Waller, *Some conjectures of Graffiti.pc on total domination*, Conjecture 6](https://math1um.github.io/Research/r05.pdf) ask whether a tree with more than two vertices in which degree two is the most frequent degree satisfies
\[
3\gamma_t(T)\ge 4\,dd(T),
\]
where \(dd\) is the number of distinct degrees. The singular wording suggests a unique mode, but the catalogue's linked definitions 94 and 27 do not prescribe a tie convention. Both interpretations are treated below. The [public audit](https://gist.github.com/siddhantdubey/22f22a7a23db5174ee59e32eaa8724aa), §9a, lists #367 as surviving finite tests (minimum slack \(2/3\)), consistent with requiring the unique mode. No earlier general resolution was located.

## Unique mode

For a total dominating set \(D\), put \(m=|D|\), and let \(c\) be the number of components of the forest \(T[D]\). Each component has at least two vertices because every vertex of \(D\) has a neighbor in \(D\); hence \(c\le\lfloor m/2\rfloor\). The \(m-c\) edges internal to \(D\), the at least \(n-m\) cross-edges (each outside vertex has a neighbor in \(D\)), and the \(n-1\) total tree edges show that at most \(c-1\) edges are internal to \(V\setminus D\). If that last edge count is \(b\), the sum of the degrees of the outside vertices is
\[
(n-1)-(m-c)-b+2b \le (n-m)+2(c-1).
\]
Every outside vertex has positive degree, so there are at most \(2(c-1)\) outside nonleaves. Writing \(N\) for the total number of nonleaves, we obtain
\[
N+2\le m+2\lfloor m/2\rfloor.
\]
This refines by one for odd \(m\) the familiar bound \(\gamma_t\ge(n+2-L)/2\) attributed to Chellali and Haynes. The proof above is elementary; in Lean the corresponding count uses directed edges.

Write \(L\) for the number of leaves, \(N_2\) for the number of degree-two vertices, and \(d=dd(T)\). The unique-mode hypothesis gives \(N_2\ge L+1\). The tree degree sum implies \(L=2+\sum_{\deg(v)\ge3}(\deg(v)-2)\), so
\[
N = N_2+|\{v:\deg(v)\ge3\}|
\ge 3+\sum_{\deg(v)\ge3}(\deg(v)-1).
\]
Select one vertex of each distinct degree at least three. Their degrees are distinct integers at least three, so the last sum is at least \(3(d-2)-1\) (only degree three contributes below three), and at least \(4(d-2)-3\) (only degrees three and four contribute below four). Thus \(N\ge3,\ 3d-4,\ 4d-8\).

If \(d\le2\), the first bound forces \(m\ge3\); if \(d=3\), the second forces \(m\ge4\); if \(d=4\), the second gives \(N\ge8\), and \(m=5\) is ruled out because \(5+2\lfloor5/2\rfloor=9<10\). If \(d\ge5\), the last bound gives \(2m\ge N+2\ge4d-6\), so \(3m\ge6d-9\ge4d\). Taking the minimum \(m\) proves the result.

## Ties allowed

On the four-vertex path \(P_4\), degrees 1 and 2 each occur twice. Its two middle vertices form a total dominating set, so \(\gamma_t(P_4)\le2<8/3\), while \(dd(P_4)=2\). Hence the tie-inclusive version is false.

Replay: Lean and Mathlib v4.19.0.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

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

private lemma dartPart (D : Finset V) (hD : TD G D)
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

private lemma lower367 (hpos : ∀ v, 0 < G.degree v) (ht : G.IsTree)
    (hmode : ∀ k : ℕ, k ≠ 2 → degFreq G k < degFreq G 2) :
    3 ≤ nonLeaves G ∧ 3 * (degrees G).card ≤ nonLeaves G + 4 ∧
      4 * (degrees G).card ≤ nonLeaves G + 8 := by
  classical
  let w (k : Nat) := if 3 ≤ k then k - 1 else 0
  let U := (degrees G).filter (fun d => 3 ≤ d)
  let N := (univ : Finset V).filter (fun v => 3 ≤ G.degree v)
  have parts : 2 + (∑ v : V, (G.degree v - 2)) = degFreq G 1 := by
    have hp : ∑ v : V, (G.degree v + if G.degree v = 1 then 1 else 0)
        = ∑ v : V, (2 + (G.degree v - 2)) := by
      apply sum_congr rfl
      intro v _
      have hh := hpos v
      split <;> omega
    rw [sum_add_distrib, sum_add_distrib] at hp
    simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] at hp
    rw [G.sum_degrees_eq_twice_card_edges] at hp
    have edges : G.edgeFinset.card + 1 = Fintype.card V := by
      simpa [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
        (isTree_iff_connected_and_card.mp ht).2
    have hf : (∑ v : V, if G.degree v = 1 then 1 else 0) = degFreq G 1 := by
      unfold degFreq
      rw [← Finset.sum_filter]
      exact (Finset.card_eq_sum_ones _).symm
    rw [hf] at hp
    omega
  have p2 : degFreq G 2 + N.card = nonLeaves G := by
    let Z := (univ : Finset V).filter (fun v => G.degree v = 2)
    have hdis : Disjoint Z N := disjoint_left.mpr (by
      intro v hv hn
      have a := (mem_filter.mp hv).2
      have b := (mem_filter.mp hn).2
      omega)
    have hU : Z ∪ N = (univ : Finset V).filter (fun v => G.degree v ≠ 1) := by
      ext v
      simp only [Z,N,mem_union,mem_filter,mem_univ,true_and]
      have hh := hpos v
      omega
    change Z.card + N.card = _
    rw [← card_union_of_disjoint hdis,hU]
    rfl
  have sumw : (∑ v : V, w (G.degree v)) = (∑ v : V, (G.degree v - 2)) + N.card := by
    have hpt : (∑ v : V, w (G.degree v)) =
        ∑ v : V, ((G.degree v - 2) + if 3 ≤ G.degree v then 1 else 0) := by
      apply sum_congr rfl
      intro v _
      by_cases hh : 3 ≤ G.degree v <;> simp [w,hh] <;> omega
    rw [hpt,sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter]
    exact (Finset.card_eq_sum_ones _).symm
  have hNL : 3 + (∑ v : V, w (G.degree v)) ≤ nonLeaves G := by
    have hh := hmode 1 (by decide)
    omega
  have HU : (∑ d ∈ U, w d) ≤ ∑ v : V, w (G.degree v) := by
    have rep (d : ↥(U : Set Nat)) : ∃ v : V, G.degree v = d.val := by
      obtain ⟨v,_,he⟩ := mem_image.mp (mem_filter.mp d.property).1
      exact ⟨v,he⟩
    let f (d : ↥(U : Set Nat)) := Classical.choose (rep d)
    have hf (d : ↥(U : Set Nat)) : G.degree (f d) = d.val := Classical.choose_spec (rep d)
    have hi : Function.Injective f := by
      intro a b h
      exact Subtype.ext ((hf a).symm.trans ((congrArg (fun v => G.degree v) h).trans (hf b)))
    rw [← Finset.sum_attach U]
    have he : (∑ x ∈ U.attach.image f, w (G.degree x)) = ∑ d ∈ U.attach, w d.val := by
      rw [Finset.sum_image hi.injOn]
      exact sum_congr rfl (fun d _ => congrArg w (hf d))
    rw [← he]
    exact Finset.sum_le_sum_of_subset (subset_univ _)
  have uc : (degrees G).card ≤ U.card + 2 := by
    have hu : degrees G ⊆ insert 1 (insert 2 U) := by
      intro d hd
      obtain ⟨v,_,he⟩ := mem_image.mp hd
      have hp := hpos v
      simp [U,hd]
      omega
    have h := card_le_card hu
    have h1 := card_insert_le 1 (insert 2 U)
    have h2 := card_insert_le 2 U
    omega
  have h3 : 3*U.card ≤ (∑ d ∈ U, w d) + 1 := by
    let S := U.erase 3
    have hh : 3*S.card ≤ ∑ d ∈ S, w d := by
      rw [show 3*S.card = ∑ _d ∈ S, (3 : Nat) by simp [mul_comm]]
      apply sum_le_sum
      intro d hd
      have h1 := (mem_erase.mp hd).1
      have h2 := (mem_filter.mp (mem_erase.mp hd).2).2
      simp [w,h2]
      omega
    by_cases h : 3 ∈ U
    · have he := sum_erase_add U w h
      have hc := card_erase_add_one h
      have hw : w 3 = 2 := by decide
      change (∑ d ∈ S, w d) + w 3 = _ at he
      change S.card + 1 = _ at hc
      omega
    · simpa [S,erase_eq_of_not_mem h] using (hh.trans (Nat.le_succ _))
  have h4 : 4*U.card ≤ (∑ d ∈ U, w d) + 3 := by
    let S := U.erase 3
    let R := S.erase 4
    have hh : 4*R.card ≤ ∑ d ∈ R, w d := by
      rw [show 4*R.card = ∑ _d ∈ R, (4 : Nat) by simp [mul_comm]]
      apply sum_le_sum
      intro d hd
      have h1 := (mem_erase.mp hd).1
      have h2 := (mem_erase.mp (mem_erase.mp hd).2).1
      have h3' := (mem_filter.mp (mem_erase.mp (mem_erase.mp hd).2).2).2
      simp [w,h3']
      omega
    have hs : 4*S.card ≤ (∑ d ∈ S, w d) + 1 := by
      by_cases h : 4 ∈ S
      · have he := sum_erase_add S w h
        have hc := card_erase_add_one h
        have hw : w 4 = 3 := by decide
        change (∑ d ∈ R, w d) + w 4 = _ at he
        change R.card + 1 = _ at hc
        omega
      · simpa [R,erase_eq_of_not_mem h] using (hh.trans (Nat.le_succ _))
    by_cases h : 3 ∈ U
    · have he := sum_erase_add U w h
      have hc := card_erase_add_one h
      have hw : w 3 = 2 := by decide
      change (∑ d ∈ S, w d) + w 3 = _ at he
      change S.card + 1 = _ at hc
      omega
    · have hh' : 4*U.card ≤ (∑ d ∈ U, w d) + 1 := by
        simpa [S,erase_eq_of_not_mem h] using hs
      omega
  omega

noncomputable def totalDomination : Nat :=
  sInf {k | ∃ D, TD G D ∧ D.card = k}

theorem conjecture367_strict (ht : G.IsTree) (hn : 2 < Fintype.card V)
    (hmode : ∀ k : ℕ, k ≠ 2 → degFreq G k < degFreq G 2) :
    4*(degrees G).card ≤ 3*totalDomination G := by
  classical
  have hh (v : V) : ∃ u, G.Adj v u := by
    obtain ⟨w,hne⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
    obtain ⟨p⟩ := ht.isConnected v w
    cases p with
    | nil => exact False.elim (hne rfl)
    | @cons _ u _ he _ => exact ⟨u,he⟩
  have hd : TD G Finset.univ := fun v => by
    obtain ⟨u,he⟩ := hh v
    exact ⟨u,mem_univ _,he⟩
  have ha : ({k : Nat | ∃ D : Finset V, TD G D ∧ D.card = k}).Nonempty :=
    ⟨_,_,hd,rfl⟩
  obtain ⟨D,hD,he⟩ := Nat.sInf_mem ha
  rw [show totalDomination G = D.card from he.symm]
  have hpos (v : V) : 0 < G.degree v := by
    obtain ⟨u,hu⟩ := hh v
    rw [← G.card_neighborFinset_eq_degree]
    exact card_pos.mpr ⟨u,(G.mem_neighborFinset v u).mpr hu⟩
  have hx := dartPart G D hD hpos ht
  obtain ⟨hn3,hn3',hn4⟩ := lower367 G hpos ht hmode
  by_cases h2 : (degrees G).card ≤ 2
  · omega
  by_cases h3 : (degrees G).card = 3
  · omega
  by_cases h4 : (degrees G).card = 4
  · omega
  omega

#print axioms conjecture367_strict
end Graffiti367

namespace Graffiti367
def P4 : SimpleGraph (Fin 4) := pathGraph 4
instance : DecidableRel P4.Adj := fun _ _ => decidable_of_iff _ pathGraph_adj.symm

private lemma p4Deg (v : Fin 4) :
    P4.degree v = if v = 0 ∨ v = 3 then 1 else 2 := by
  revert v
  decide

private lemma p4Tree : P4.IsTree := by
  apply isTree_iff_connected_and_card.mpr
  refine ⟨pathGraph_connected 3, ?_⟩
  have h := P4.sum_degrees_eq_twice_card_edges
  have hdeg : (∑ v : Fin 4, P4.degree v) = 6 := by decide
  rw [hdeg] at h
  simp only [Nat.card_eq_fintype_card, ← edgeFinset_card, Fintype.card_fin]
  omega

private lemma p4Mode : ∀ k, degFreq P4 k ≤ degFreq P4 2 := by
  intro k
  have d2 : degFreq P4 2 = 2 := by decide
  by_cases h1 : k = 1
  · subst k
    decide
  by_cases h2 : k = 2
  · subst k
    exact le_rfl
  have hz : degFreq P4 k = 0 := by
    unfold degFreq
    rw [Finset.card_filter_eq_zero_iff]
    intro v _
    rw [p4Deg]
    split <;> omega
  omega

theorem counterexample367_ties :
    P4.IsTree ∧ 2 < Fintype.card (Fin 4) ∧
    (∀ k, degFreq P4 k ≤ degFreq P4 2) ∧ 3*totalDomination P4 < 4*(degrees P4).card := by
  refine ⟨p4Tree,by decide,p4Mode,?_⟩
  have hd : TD P4 ({1,2} : Finset (Fin 4)) := by
    unfold TD
    decide
  have ht : totalDomination P4 ≤ 2 := by
    unfold totalDomination
    exact Nat.sInf_le ⟨{1,2},hd,by decide⟩
  have hf : (degrees P4).card = 2 := by decide
  omega

#print axioms counterexample367_ties
end Graffiti367
