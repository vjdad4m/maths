/-
# Graffiti.pc #412d: proof

The [official catalogue](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) lists #412d as open, with no pending review. It says that, for a connected bipartite graph on more than two vertices, the union H of all maximum critical independent sets has size at least the total domination number. Definition 105 first maximizes the difference |I| − |N(I)| over independent sets, then maximizes the cardinality among those attaining the difference. The [prior AI Village ledger](https://gitlab.com/ai-village-agents/village/graffiti-verification) §7ga explicitly leaves this exact statement open.

## 1. Replace maximum critical sets by maximum independent sets

Write A and B for the two bipartition classes and α for the independence number. For S contained in A, the set S ∪ (B ∖ N(S)) is independent, so |S| − |N(S)| ≤ α − |B|. A maximum independent set I is maximal and therefore its B part is exactly B ∖ N(I ∩ A); hence I ∩ A attains this bound. Likewise I ∩ B attains α − |A|. The difference of any independent set is the sum of these two one-side differences because their neighbor sets lie on opposite sides. Thus every maximum independent set is critical, and the maximum critical independent sets are precisely the α-sets.

## 2. Strict Hall from the two extremal α-sets

Let K be the intersection of all α-sets, O = V ∖ H, and Q = H ∖ K. No vertex of K is adjacent to one in H: every vertex of H belongs to an α-set which contains all of K. Conversely, an isolated vertex of the graph induced by H must belong to every α-set, since otherwise one could add it to such a set. Hence each vertex of Q has a neighbor in Q, and every vertex of K has a neighbor in O (the original graph has no isolates).

For two α-sets I and J, taking the union of their A-parts and the intersection of their B-parts defines an independent set; so does taking the intersection in A and the union in B. Their sizes sum to 2α, so both are α-sets. Repeating over all α-sets, we find that (H ∩ A) ∪ (K ∩ B) and (K ∩ A) ∪ (H ∩ B) are α-sets.

If S is a nonempty subset of O ∩ A, replace N(S) ∩ K in the first of these sets by S. This is independent (the only opposite-side vertices included were in K ∩ B). It cannot exceed α by maximal cardinality, and it cannot equal α because it includes a vertex of O. Thus |N(S) ∩ K| > |S|. Use the other extremal α-set for S contained in O ∩ B. The two neighborhoods on opposite sides are disjoint, so for every nonempty S contained in O the same strict Hall inequality holds.

## 3. Choose a ranked pair in K for each vertex in O

By Hall's marriage theorem choose distinct representatives f(o) in N(o) ∩ K for o in O. Put a directed arc from each f(o) to every other y in N(o) ∩ K. Every f(o) reaches an unmatched K vertex. Otherwise the set W reachable from f(o), including itself, consists entirely of matched vertices, and all K-neighbors of f⁻¹(W) are in W (either a representative itself, or reachable by one more arc), contrary to strict Hall.

Give each K vertex its shortest directed distance to an unmatched K vertex. For each o in O choose g(o) in N(o) ∩ K reached by the first step of a shortest such path from f(o). Then the rank decreases strictly from f(o) to g(o).

## 4. Cover using at most |K| choices

We select C contained in K meeting every pair {f(o),g(o)}, and P contained in O such that P collectively neighbors every vertex of K, with |C|+|P|≤|K|. The following induction makes the counting direct and avoids any additional matching theorem.

More generally run the construction for any subset U of K and any list of active pairs with both endpoints in U, asking C contained in U to meet the active pairs and P contained in O to neighbor all of U; P may use inactive indices. If there is no active pair, choose any O-neighbor for each vertex of U and choose C empty. Otherwise choose an active pair (x,y) whose first vertex x has greatest rank among first vertices of active pairs. No active pair has second vertex x, since ranks strictly decrease. No other active pair has first vertex x, by injectivity of f. Remove x and y from U and deactivate all incident pairs. By induction solve on U ∖ {x,y}. Add y to C and the chosen pair's index o to P. Every deactivated pair meets y, and o neighbors both removed vertices. The increase in |C|+|P| is at most two, exactly the decrease in |U|. This proves the claim.

## 5. Total domination

Take Q ∪ C ∪ P. Q is dominated within itself, K by P, and O by C since C meets every pair. This is a total dominating set of size at most |Q|+|K|=|H|, proving #412d. The proof actually works for every finite isolate-free bipartite graph.

No priority or curator-acceptance claim. 

## Lean verification

`Proof412d.lean` uses only Mathlib and Lean. The original statement is `Graffiti412d.graffiti412d_catalogue`; `graffiti412d_exact` is the stronger isolate-free variant. Definitions cover both stages of maximum criticality and the minimum over all total dominating sets. In a Lean/Mathlib v4.19.0 project, run `lake build Mathlib.Combinatorics.Hall.Finite` if that import is not yet built, then `lake env lean Proof412d.lean`. Both theorem axiom lists are exactly `propext`, `Classical.choice`, and `Quot.sound`.

Replay: Lean and Mathlib v4.19.0. Build Mathlib.Combinatorics.Hall.Finite if uncached.
Main theorem: Graffiti412d.graffiti412d_catalogue.
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega
import Mathlib.Combinatorics.Hall.Finite

open Finset SimpleGraph
namespace Graffiti412d
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

abbrev TotalDominates (D : Finset V) : Prop := ∀ v, ∃ u ∈ D, G.Adj v u

noncomputable def totalDominationNumber : ℕ :=
  sInf {k : ℕ | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}

def Indep (S : Finset V) : Prop := ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v
def MaxIndep (S : Finset V) : Prop := Indep G S ∧ ∀ T, Indep G T → T.card ≤ S.card

noncomputable def nbrs (S : Finset V) : Finset V := by
  classical exact Finset.univ.filter (fun v => ∃ u ∈ S, G.Adj u v)

omit [DecidableEq V] in
theorem mem_nbrs {S : Finset V} {v : V} : v ∈ nbrs G S ↔ ∃ u ∈ S, G.Adj u v := by
  classical simp [nbrs]

noncomputable def diff (S : Finset V) : ℤ := S.card - (nbrs G S).card

def Crit (S : Finset V) : Prop :=
  Indep G S ∧ ∀ T, Indep G T → diff G T ≤ diff G S
def MaxCrit (S : Finset V) : Prop :=
  Crit G S ∧ ∀ T, Crit G T → T.card ≤ S.card

noncomputable def corona : Finset V := by
  classical exact Finset.univ.filter (fun v => ∃ S, MaxIndep G S ∧ v ∈ S)

noncomputable def core : Finset V := by
  classical exact Finset.univ.filter (fun v => ∀ S, MaxIndep G S → v ∈ S)

noncomputable def critCorona : Finset V := by
  classical exact Finset.univ.filter (fun v => ∃ S, MaxCrit G S ∧ v ∈ S)

omit [DecidableEq V] in
theorem exists_maxIndep : ∃ S, MaxIndep G S := by
  classical
  let F := (Finset.univ : Finset V).powerset.filter (Indep G)
  have hf : (∅ : Finset V) ∈ F := by simp [F, Indep]
  obtain ⟨S,hS,hm⟩ := Finset.exists_max_image F Finset.card ⟨∅,hf⟩
  exact ⟨S,(Finset.mem_filter.mp hS).2,fun T ht => hm T (by simp [F,ht])⟩

theorem indep_part (A : Finset V) (hA : Indep G A)
    (B : Finset V) (hB : Indep G B) (S : Finset V) (hS : S ⊆ A) :
    Indep G (S ∪ (B \ nbrs G S)) := by
  intro u hu v hv e
  rcases Finset.mem_union.mp hu with hu|hu <;> rcases Finset.mem_union.mp hv with hv|hv
  · exact hA u (hS hu) v (hS hv) e
  · exact (Finset.mem_sdiff.mp hv).2 ((mem_nbrs G).mpr ⟨u,hu,e⟩)
  · exact (Finset.mem_sdiff.mp hu).2 ((mem_nbrs G).mpr ⟨v,hv,e.symm⟩)
  · exact hB u (Finset.mem_sdiff.mp hu).1 v (Finset.mem_sdiff.mp hv).1 e

theorem nbrs_subset_other (A B S : Finset V) (hA : Indep G A) (hab : A ∪ B = Finset.univ)
    (hS : S ⊆ A) : nbrs G S ⊆ B := by
  intro v hv
  obtain ⟨u,hu,e⟩ := (mem_nbrs G).mp hv
  have := Finset.mem_union.mp (hab.symm ▸ Finset.mem_univ v)
  exact this.resolve_left (fun hv' => hA u (hS hu) v hv' e)

theorem maxIndep_crit
    (A B : Finset V) (hd : Disjoint A B) (hab : A ∪ B = Finset.univ)
    (hA : Indep G A) (hB : Indep G B) (I : Finset V) (hI : MaxIndep G I) :
    Crit G I := by
  classical
  have hd' := hd.symm
  have hba := Finset.union_comm B A |>.trans hab
  have side (A B S : Finset V) (hd : Disjoint A B) (hab : A ∪ B = Finset.univ)
      (hA : Indep G A) (hB : Indep G B) (hS : S ⊆ A) :
      diff G S + (B.card : ℤ) ≤ I.card := by
    have hNB := nbrs_subset_other G A B S hA hab hS
    have h := hI.2 _ (indep_part G A hA B hB S hS)
    rw [Finset.card_union_of_disjoint (Disjoint.mono hS Finset.sdiff_subset hd),
      Finset.card_sdiff hNB] at h
    have := Finset.card_le_card hNB
    unfold diff
    omega
  have part (I : Finset V) (hI : Indep G I) :
      diff G I = diff G (I ∩ A) + diff G (I ∩ B) := by
    have hparts : (I ∩ A) ∪ (I ∩ B) = I := by
      rw [← Finset.inter_union_distrib_left, hab, Finset.inter_univ]
    have he : nbrs G (I ∩ A) ∪ nbrs G (I ∩ B) = nbrs G I := by
      ext v; rw [Finset.mem_union, mem_nbrs, mem_nbrs, mem_nbrs, ← hparts]
      simp only [Finset.mem_union]
      aesop
    have h1 := Finset.card_union_of_disjoint
      (Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hd :
        Disjoint (I ∩ A) (I ∩ B))
    have h2 := Finset.card_union_of_disjoint
      (Disjoint.mono (nbrs_subset_other G A B (I ∩ A) hA hab Finset.inter_subset_right)
        (nbrs_subset_other G B A (I ∩ B) hB hba Finset.inter_subset_right) hd')
    rw [hparts] at h1
    rw [he] at h2
    unfold diff
    omega
  have attain (A B : Finset V) (hd : Disjoint A B) (hab : A ∪ B = Finset.univ)
      (hA : Indep G A) (hB : Indep G B) :
      diff G (I ∩ A) + (B.card : ℤ) = I.card := by
    have h := side A B (I ∩ A) hd hab hA hB Finset.inter_subset_right
    have hNB := nbrs_subset_other G A B (I ∩ A) hA hab Finset.inter_subset_right
    have hi : I ∩ B ⊆ B \ nbrs G (I ∩ A) := by
      intro v hv
      refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hv).2,?_⟩
      intro hN
      obtain ⟨u,hu,e⟩ := (mem_nbrs G).mp hN
      exact hI.1 u (Finset.mem_inter.mp hu).1 v (Finset.mem_inter.mp hv).1 e
    have hci := Finset.card_le_card hi
    rw [Finset.card_sdiff hNB] at hci
    have hcnt := Finset.card_union_of_disjoint
      (Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hd :
        Disjoint (I ∩ A) (I ∩ B))
    rw [← Finset.inter_union_distrib_left, hab, Finset.inter_univ] at hcnt
    have := Finset.card_le_card hNB
    unfold diff at *
    omega
  refine ⟨hI.1,?_⟩
  intro T hT
  rw [part I hI.1, part T hT]
  have := side A B (T ∩ A) hd hab hA hB Finset.inter_subset_right
  have := side B A (T ∩ B) hd' hba hB hA Finset.inter_subset_right
  have := attain A B hd hab hA hB
  have := attain B A hd' hba hB hA
  omega

theorem maxCrit_iff (A B : Finset V) (hd : Disjoint A B) (hab : A ∪ B = Finset.univ)
    (hA : Indep G A) (hB : Indep G B) (S : Finset V) :
    MaxCrit G S ↔ MaxIndep G S := by
  constructor
  · intro hS
    obtain ⟨I,hI⟩ := exists_maxIndep G
    have h := hS.2 I (maxIndep_crit G A B hd hab hA hB I hI)
    exact ⟨hS.1.1, fun T ht => (hI.2 T ht).trans h⟩
  · intro hS
    exact ⟨maxIndep_crit G A B hd hab hA hB S hS, fun T ht => hS.2 T ht.1⟩


theorem ranked_cover {K O : Type*} [DecidableEq K] [DecidableEq O]
    (R : O → K → Prop) (f g : O → K) (rank : K → ℕ)
    (hf : Function.Injective f) (hr : ∀ o, rank (g o) < rank (f o))
    (hfr : ∀ o, R o (f o)) (hgr : ∀ o, R o (g o))
    (U : Finset K) (P : Finset O) (hU : ∀ x ∈ U, ∃ o, R o x)
    (ha : ∀ o ∈ P, f o ∈ U ∧ g o ∈ U) :
    ∃ C : Finset K, ∃ Q : Finset O,
      C ⊆ U ∧ (∀ o ∈ P, f o ∈ C ∨ g o ∈ C) ∧
      (∀ x ∈ U, ∃ o ∈ Q, R o x) ∧ C.card + Q.card ≤ U.card := by
  classical
  induction hn : U.card using Nat.strong_induction_on generalizing U P with
  | h n ih =>
    rename_i hn
    by_cases hp : P.Nonempty
    · obtain ⟨o,ho,hm⟩ := Finset.exists_max_image P (rank ∘ f) hp
      let x := f o
      let y := g o
      have hxy : x ≠ y := by
        intro h; have h' : rank y < rank x := hr o
        rw [h] at h'; exact (lt_irrefl _ h')
      have hxu : x ∈ U := (ha o ho).1
      have hyu : y ∈ U := (ha o ho).2
      let U' := (U.erase x).erase y
      let P' := P.filter (fun i => f i ∈ U' ∧ g i ∈ U')
      have hcU : U'.card + 2 = U.card := by
        have hh : y ∈ U.erase x := Finset.mem_erase.mpr ⟨hxy.symm,hyu⟩
        have h1 := Finset.card_erase_add_one hh
        have h2 := Finset.card_erase_add_one hxu
        dsimp [U']; omega
      have ht : U'.card < n := by omega
      have hU'U : U' ⊆ U := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      obtain ⟨C,Q,hC,hP,hQ,hbound⟩ :=
        ih U'.card ht U' P' (fun z hz => hU z (hU'U hz))
          (fun i hi => (Finset.mem_filter.mp hi).2) rfl
      refine ⟨insert y C, insert o Q, ?_, ?_, ?_, ?_⟩
      · exact Finset.insert_subset hyu (hC.trans hU'U)
      · intro i hi
        have hmx : g i ≠ x := by
          intro heq
          have h1 := hr i
          have h2 := hm i hi
          change rank (f i) ≤ rank x at h2
          rw [heq] at h1
          omega
        by_cases hfy : f i = y
        · exact Or.inl (hfy ▸ Finset.mem_insert_self _ _)
        by_cases hgy : g i = y
        · exact Or.inr (hgy ▸ Finset.mem_insert_self _ _)
        have hfx : f i ≠ x := by
          intro heq
          have hh : i = o := hf heq
          exact hgy (hh ▸ rfl)
        have hp'i : i ∈ P' := Finset.mem_filter.mpr ⟨hi,
          Finset.mem_erase.mpr ⟨hfy, Finset.mem_erase.mpr ⟨hfx,(ha i hi).1⟩⟩,
          Finset.mem_erase.mpr ⟨hgy, Finset.mem_erase.mpr ⟨hmx,(ha i hi).2⟩⟩⟩
        exact (hP i hp'i).imp Finset.mem_insert_of_mem Finset.mem_insert_of_mem
      · intro z hz
        by_cases hxz : z = x
        · exact ⟨o,Finset.mem_insert_self _ _,hxz ▸ hfr o⟩
        by_cases hyz : z = y
        · exact ⟨o,Finset.mem_insert_self _ _,hyz ▸ hgr o⟩
        obtain ⟨i,hi,hr⟩ := hQ z (Finset.mem_erase.mpr ⟨hyz,Finset.mem_erase.mpr ⟨hxz,hz⟩⟩)
        exact ⟨i,Finset.mem_insert_of_mem hi,hr⟩
      · have ha := Finset.card_insert_le y C
        have hb := Finset.card_insert_le o Q
        omega
    · have hP : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
      let pick : U → O := fun z => Classical.choose (hU z.1 z.2)
      let Q : Finset O := Finset.univ.image pick
      refine ⟨∅, Q, Finset.empty_subset _, ?_, ?_, ?_⟩
      · intro o ho
        simp [hP] at ho
      · intro z hz
        exact ⟨pick ⟨z,hz⟩, Finset.mem_image_of_mem pick (Finset.mem_univ _),
          Classical.choose_spec (hU z hz)⟩
      · have hq := Finset.card_image_le (s := (Finset.univ : Finset U)) (f := pick)
        rw [Finset.card_univ, Fintype.card_coe] at hq
        simpa [Q, ← hn] using hq


theorem mem_corona {v : V} : v ∈ corona G ↔ ∃ S, MaxIndep G S ∧ v ∈ S := by
  classical simp [corona]
theorem mem_core {v : V} : v ∈ core G ↔ ∀ S, MaxIndep G S → v ∈ S := by
  classical simp [core]

theorem extreme (A B : Finset V) (hd : Disjoint A B) (hab : A ∪ B = Finset.univ)
    (hA : Indep G A) (hB : Indep G B) :
    MaxIndep G ((corona G ∩ A) ∪ (core G ∩ B)) := by
  classical
  let F := (Finset.univ : Finset V).powerset.filter (MaxIndep G)
  have hF (S : Finset V) : S ∈ F ↔ MaxIndep G S := by simp [F]
  obtain ⟨J,hJ⟩ := exists_maxIndep G
  obtain ⟨I,hi,hm⟩ := F.exists_max_image (fun S => (S ∩ A).card) ⟨J,(hF J).mpr hJ⟩
  have hI := (hF I).mp hi
  have disj (X Y : Finset V) : Disjoint (X ∩ A) (Y ∩ B) :=
    Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hd
  have cut (X : Finset V) : (X ∩ A) ∪ (X ∩ B) = X := by
    rw [← Finset.inter_union_distrib_left, hab, Finset.inter_univ]
  have uncross (I J A B : Finset V) (hI : Indep G I) (hJ : Indep G J)
      (hA : Indep G A) (hB : Indep G B) :
      Indep G (((I ∩ A) ∪ (J ∩ A)) ∪ ((I ∩ B) ∩ (J ∩ B))) := by
    intro u hu v hv e
    simp only [Finset.mem_union, Finset.mem_inter] at hu hv
    rcases hu with (hu|hu)|hu <;> rcases hv with (hv|hv)|hv
    · exact hA u hu.2 v hv.2 e
    · exact hA u hu.2 v hv.2 e
    · exact hI u hu.1 v hv.1.1 e
    · exact hA u hu.2 v hv.2 e
    · exact hA u hu.2 v hv.2 e
    · exact hJ u hu.1 v hv.2.1 e
    · exact hI u hu.1.1 v hv.1 e
    · exact hJ u hu.2.1 v hv.1 e
    · exact hB u hu.1.2 v hv.1.2 e
  have left_in (J : Finset V) (hJ : MaxIndep G J) : J ∩ A ⊆ I ∩ A := by
    let X := (I ∩ A) ∪ (J ∩ A)
    let Y := (I ∩ B) ∩ (J ∩ B)
    let X' := (I ∩ A) ∩ (J ∩ A)
    let Y' := (I ∩ B) ∪ (J ∩ B)
    have hXA : X ⊆ A := Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
    have hYB : Y ⊆ B := Finset.inter_subset_left.trans Finset.inter_subset_right
    have hX'A : X' ⊆ A := Finset.inter_subset_left.trans Finset.inter_subset_right
    have hY'B : Y' ⊆ B := Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
    have h1 : Disjoint X Y := Disjoint.mono hXA hYB hd
    have h2 : Disjoint X' Y' := Disjoint.mono hX'A hY'B hd
    have h3 : Indep G (X ∪ Y) := uncross I J A B hI.1 hJ.1 hA hB
    have h4 : Indep G (X' ∪ Y') := by
      rw [Finset.union_comm]; exact uncross I J B A hI.1 hJ.1 hB hA
    have h5 := hI.2 _ h3
    have h6 := hJ.2 _ h4
    rw [Finset.card_union_of_disjoint h1] at h5
    rw [Finset.card_union_of_disjoint h2] at h6
    have h7 : X.card + X'.card = (I ∩ A).card + (J ∩ A).card :=
      Finset.card_union_add_card_inter _ _
    have h8 : Y'.card + Y.card = (I ∩ B).card + (J ∩ B).card :=
      Finset.card_union_add_card_inter _ _
    have hcard (S : Finset V) : (S ∩ A).card + (S ∩ B).card = S.card := by
      rw [← Finset.card_union_of_disjoint (disj S S), cut S]
    have h9 := hcard I
    have h10 := hcard J
    have hc : (X ∪ Y).card = I.card := by
      rw [Finset.card_union_of_disjoint h1]
      omega
    have hmax' : MaxIndep G (X ∪ Y) := ⟨h3,fun T ht => hc.symm ▸ hI.2 T ht⟩
    have hA' : (X ∪ Y) ∩ A = X := by
      ext v
      have hyB : Y ⊆ B := Finset.inter_subset_left.trans Finset.inter_subset_right
      have hxA : X ⊆ A := Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
      simp only [Finset.mem_inter,Finset.mem_union]
      constructor
      · rintro ⟨hx|hy,hva⟩
        · exact hx
        · exact (Finset.disjoint_left.mp hd hva (hyB hy)).elim
      · intro hx; exact ⟨Or.inl hx,hxA hx⟩
    have hmax := hm _ ((hF _).mpr hmax')
    rw [hA'] at hmax
    have hsub : I ∩ A ⊆ X := Finset.subset_union_left
    have hh := Finset.eq_of_subset_of_card_le hsub hmax
    exact hh ▸ Finset.subset_union_right
  have hLA : I ∩ A = corona G ∩ A := by
    ext v
    simp only [Finset.mem_inter,mem_corona]
    constructor
    · intro h; exact ⟨⟨I,hI,h.1⟩,h.2⟩
    · rintro ⟨⟨J,hJ,hv⟩,ha⟩
      exact Finset.mem_inter.mp (left_in J hJ (Finset.mem_inter.mpr ⟨hv,ha⟩))
  have hLB : I ∩ B = core G ∩ B := by
    ext v
    simp only [Finset.mem_inter,mem_core]
    constructor
    · rintro ⟨hv,hvb⟩
      refine ⟨fun J hJ => ?_,hvb⟩
      by_contra hmiss
      have hn : ∀ u ∈ J, ¬ G.Adj u v := by
        intro u hu he
        have hside := Finset.mem_union.mp (hab.symm ▸ Finset.mem_univ u)
        rcases hside with ha|hb
        · have hsub := left_in J hJ (Finset.mem_inter.mpr ⟨hu,ha⟩)
          exact hI.1 u (Finset.mem_inter.mp hsub).1 v hv he
        · exact hB u hb v hvb he
      have hins : Indep G (insert v J) := by
        intro x hx y hy e
        simp only [Finset.mem_insert] at hx hy
        rcases hx with rfl|hx <;> rcases hy with rfl|hy
        · exact G.loopless _ e
        · exact hn _ hy e.symm
        · exact hn _ hx e
        · exact hJ.1 _ hx _ hy e
      have hlt := hJ.2 _ hins
      rw [Finset.card_insert_of_not_mem hmiss] at hlt
      omega
    · intro h; exact ⟨h.1 _ hI,h.2⟩
  rw [← hLA, ← hLB, cut I]
  exact hI


def ReachesRoot {K : Type*} (edge : K → K → Prop) (root : K → Prop) :
    ℕ → K → Prop
  | 0, x => root x
  | n+1, x => ∃ y, edge x y ∧ ReachesRoot edge root n y

theorem strictHall_rank {K O : Type*} [Fintype K] [Fintype O] [DecidableEq K]
    (R : O → K → Prop) [∀ o, DecidablePred (R o)]
    (h : ∀ S : Finset O, S.Nonempty →
      S.card < (S.biUnion (fun o => Finset.univ.filter (R o))).card) :
    ∃ (f g : O → K) (rank : K → ℕ), Function.Injective f ∧
      (∀ o, rank (g o) < rank (f o)) ∧ (∀ o, R o (f o)) ∧ (∀ o, R o (g o)) := by
  classical
  let N : O → Finset K := fun o => Finset.univ.filter (R o)
  have hh : ∀ S : Finset O, S.card ≤ (S.biUnion N).card := by
    intro S
    by_cases hs : S.Nonempty
    · exact (h S hs).le
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs]
  obtain ⟨f,hf,hm⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hh
  have hfr (o : O) : R o (f o) := (Finset.mem_filter.mp (hm o)).2
  let root : K → Prop := fun x => ¬ ∃ o, f o = x
  let edge : K → K → Prop := fun x y => ∃ o, f o = x ∧ R o y ∧ y ≠ x
  let reaches : K → Prop := fun x => ∃ n, ReachesRoot edge root n x
  have hreachable (x : K) : reaches x := by
    by_contra hn
    let W : Finset K := Finset.univ.filter (fun w => ¬ reaches w)
    let S : Finset O := Finset.univ.filter (fun o => f o ∈ W)
    have hx : x ∈ W := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩
    have hmW : ∀ w ∈ W, ∃ o, f o = w := by
      intro w hw
      by_contra hn
      exact (Finset.mem_filter.mp hw).2 ⟨0,hn⟩
    have hW : S.image f = W := by
      ext w
      constructor
      · intro hw
        obtain ⟨o,ho,rfl⟩ := Finset.mem_image.mp hw
        exact (Finset.mem_filter.mp ho).2
      · intro hw
        obtain ⟨o,rfl⟩ := hmW w hw
        exact Finset.mem_image.mpr ⟨o,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩,rfl⟩
    have hs : S.Nonempty := by
      obtain ⟨o,rfl⟩ := hmW x hx
      exact ⟨o,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩⟩
    have hsub : S.biUnion N ⊆ W := by
      intro w hw
      obtain ⟨o,ho,hwo⟩ := Finset.mem_biUnion.mp hw
      have hW' := (Finset.mem_filter.mp ho).2
      by_cases hww : w = f o
      · exact hww ▸ hW'
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      rintro ⟨n,hnw⟩
      exact (Finset.mem_filter.mp hW').2 ⟨n+1,w,⟨o,rfl,(Finset.mem_filter.mp hwo).2,hww⟩,hnw⟩
    have hcard := Finset.card_le_card hsub
    rw [← hW, Finset.card_image_of_injective _ hf] at hcard
    exact (not_lt_of_ge hcard) (h S hs)
  let rank : K → ℕ := fun x => Nat.find (hreachable x)
  have hstep (o : O) : ∃ y, R o y ∧ rank y < rank (f o) := by
    have hbest : ReachesRoot edge root (rank (f o)) (f o) := Nat.find_spec (hreachable (f o))
    cases heq : rank (f o) with
    | zero =>
      rw [heq] at hbest
      exact (hbest ⟨o,rfl⟩).elim
    | succ n =>
      rw [heq] at hbest
      obtain ⟨y,⟨o',ho',hy,_⟩,hny⟩ := hbest
      have hh : o' = o := hf ho'
      subst o'
      have le : rank y ≤ n := Nat.find_min' (hreachable y) hny
      exact ⟨y,hy,by omega⟩
  choose g hg using hstep
  exact ⟨f,g,rank,hf,fun o => (hg o).2,hfr,fun o => (hg o).1⟩


theorem strictHallPart (A B S : Finset V) (hd : Disjoint A B) (hab : A ∪ B = Finset.univ)
    (hA : Indep G A) (hB : Indep G B) (hSA : S ⊆ A)
    (hSO : Disjoint S (corona G)) (hne : S.Nonempty) :
    S.card < (nbrs G S ∩ core G).card := by
  classical
  let E := (corona G ∩ A) ∪ (core G ∩ B)
  let N := nbrs G S ∩ core G
  have hE : MaxIndep G E := extreme G A B hd hab hA hB
  have hN : N ⊆ E := by
    intro v hv
    obtain ⟨hn,hk⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hk,
      nbrs_subset_other G A B S hA hab hSA hn⟩)
  have hcore : core G ⊆ corona G := by
    obtain ⟨I,hI⟩ := exists_maxIndep G
    intro v hv
    exact (mem_corona G).mpr ⟨I,hI,(mem_core G).mp hv I hI⟩
  have hEH : E ⊆ corona G :=
    Finset.union_subset Finset.inter_subset_left (Finset.inter_subset_left.trans hcore)
  have hds : Disjoint S (E \ N) :=
    Disjoint.mono_right (Finset.sdiff_subset.trans hEH) hSO
  let T := S ∪ (E \ N)
  have hT : Indep G T := by
    intro u hu v hv e
    rcases Finset.mem_union.mp hu with hu|hu <;> rcases Finset.mem_union.mp hv with hv|hv
    · exact hA _ (hSA hu) _ (hSA hv) e
    · obtain ⟨he,hn⟩ := Finset.mem_sdiff.mp hv
      rcases Finset.mem_union.mp he with he|he
      · exact hA _ (hSA hu) _ (Finset.mem_inter.mp he).2 e
      · exact hn (Finset.mem_inter.mpr ⟨(mem_nbrs G).mpr ⟨u,hu,e⟩,(Finset.mem_inter.mp he).1⟩)
    · obtain ⟨he,hn⟩ := Finset.mem_sdiff.mp hu
      rcases Finset.mem_union.mp he with he|he
      · exact hA _ (Finset.mem_inter.mp he).2 _ (hSA hv) e
      · exact hn (Finset.mem_inter.mpr ⟨(mem_nbrs G).mpr ⟨v,hv,e.symm⟩,(Finset.mem_inter.mp he).1⟩)
    · exact hE.1 _ (Finset.mem_sdiff.mp hu).1 _ (Finset.mem_sdiff.mp hv).1 e
  have hle := hE.2 T hT
  have hlt : T.card < E.card := by
    by_contra hh
    have hM : MaxIndep G T := ⟨hT,fun I hI => (hE.2 I hI).trans (Nat.le_of_not_gt hh)⟩
    obtain ⟨v,hv⟩ := hne
    exact Finset.disjoint_left.mp hSO hv ((mem_corona G).mpr ⟨T,hM,Finset.mem_union_left _ hv⟩)
  change (S ∪ (E \ N)).card < E.card at hlt
  rw [Finset.card_union_of_disjoint hds, Finset.card_sdiff hN] at hlt
  have := Finset.card_le_card hN
  change S.card < N.card
  omega

theorem strictHallGraph (A B S : Finset V) (hd : Disjoint A B) (hab : A ∪ B = Finset.univ)
    (hA : Indep G A) (hB : Indep G B)
    (hSO : Disjoint S (corona G)) (hne : S.Nonempty) :
    S.card < (nbrs G S ∩ core G).card := by
  classical
  let SA := S ∩ A
  let SB := S ∩ B
  have hs : SA ∪ SB = S := by
    change S ∩ A ∪ S ∩ B = S
    rw [← Finset.inter_union_distrib_left,hab,Finset.inter_univ]
  have hsdis : Disjoint SA SB :=
    Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hd
  have hcS := Finset.card_union_of_disjoint hsdis
  rw [hs] at hcS
  have hn : (nbrs G SA ∩ core G) ∪ (nbrs G SB ∩ core G) = nbrs G S ∩ core G := by
    have hn' : nbrs G SA ∪ nbrs G SB = nbrs G S := by
      ext v
      rw [Finset.mem_union, mem_nbrs, mem_nbrs, mem_nbrs, ← hs]
      simp only [Finset.mem_union]
      aesop
    rw [← Finset.union_inter_distrib_right,hn']
  have hnd : Disjoint (nbrs G SA ∩ core G) (nbrs G SB ∩ core G) := by
    have hNA := nbrs_subset_other G A B SA hA hab Finset.inter_subset_right
    have hNB := nbrs_subset_other G B A SB hB (by simpa [Finset.union_comm] using hab)
      Finset.inter_subset_right
    exact Disjoint.mono (Finset.inter_subset_left.trans hNA)
      (Finset.inter_subset_left.trans hNB) hd.symm
  have hcN := Finset.card_union_of_disjoint hnd
  rw [hn] at hcN
  have hA' : SA.Nonempty → SA.card < (nbrs G SA ∩ core G).card :=
    strictHallPart G A B SA hd hab hA hB Finset.inter_subset_right
      (Disjoint.mono_left Finset.inter_subset_left hSO)
  have hB' : SB.Nonempty → SB.card < (nbrs G SB ∩ core G).card :=
    strictHallPart G B A SB hd.symm (by simpa [Finset.union_comm] using hab) hB hA
      Finset.inter_subset_right (Disjoint.mono_left Finset.inter_subset_left hSO)
  by_cases ha : SA.Nonempty
  · have ha' := hA' ha
    by_cases hb : SB.Nonempty
    · have hb' := hB' hb; omega
    · have h := Finset.not_nonempty_iff_eq_empty.mp hb
      have hc : SB.card = 0 := by simp [h]
      omega
  · have h := Finset.not_nonempty_iff_eq_empty.mp ha
    have hc : SA.card = 0 := by simp [h]
    have hb : SB.Nonempty := by rw [h,Finset.empty_union] at hs; simpa [hs] using hne
    have hb' := hB' hb
    omega


theorem exact_witness (A B : Finset V) (hd : Disjoint A B) (hab : A ∪ B = Finset.univ)
    (hA : Indep G A) (hB : Indep G B) (hNI : ∀ v, ∃ u, G.Adj v u) :
    ∃ D : Finset V, TotalDominates G D ∧ D.card ≤ (critCorona G).card := by
  classical
  let H := corona G
  let K := core G
  let O := Finset.univ \ H
  let Q := H \ K
  have hcrit : critCorona G = H := by
    ext v
    simp [critCorona, corona, H, maxCrit_iff G A B hd hab hA hB]
  obtain ⟨I,hI⟩ := exists_maxIndep G
  have hsub : K ⊆ H := by
    intro v hv
    exact (mem_corona G).mpr ⟨I,hI,(mem_core G).mp hv I hI⟩
  have hno {v u : V} (hv : v ∈ K) (hu : u ∈ H) : ¬ G.Adj v u := by
    obtain ⟨J,hJ,hu⟩ := (mem_corona G).mp hu
    exact hJ.1 v ((mem_core G).mp hv J hJ) u hu
  have hQ : ∀ v ∈ Q, ∃ u ∈ Q, G.Adj v u := by
    intro v hv
    obtain ⟨hvH,hvK⟩ := Finset.mem_sdiff.mp hv
    by_contra hmiss
    have hN : ∀ u ∈ H, ¬ G.Adj v u := by
      intro u hu e
      by_cases huK : u ∈ K
      · exact hno huK hvH e.symm
      · exact hmiss ⟨u,Finset.mem_sdiff.mpr ⟨hu,huK⟩,e⟩
    apply hvK
    apply (mem_core G).mpr
    intro J hJ
    by_contra hJv
    have hJH (u : V) (hu : u ∈ J) : u ∈ H := (mem_corona G).mpr ⟨J,hJ,hu⟩
    have hins : Indep G (insert v J) := by
      intro x hx y hy e
      simp only [Finset.mem_insert] at hx hy
      rcases hx with rfl|hx <;> rcases hy with rfl|hy
      · exact G.loopless _ e
      · exact hN _ (hJH _ hy) e
      · exact hN _ (hJH _ hx) e.symm
      · exact hJ.1 _ hx _ hy e
    have ht := hJ.2 _ hins
    rw [Finset.card_insert_of_not_mem hJv] at ht
    omega
  let R : O → K → Prop := fun o k => G.Adj o.1 k.1
  letI : ∀ o, DecidablePred (R o) := fun _ => Classical.decPred _
  have hHall (S : Finset O) (hs : S.Nonempty) :
      S.card < (S.biUnion (fun o => Finset.univ.filter (R o))).card := by
    let SO := S.map ⟨Subtype.val,Subtype.val_injective⟩
    have hsO : SO.Nonempty := hs.map
    have hdis : Disjoint SO H := by
      apply Finset.disjoint_left.mpr
      intro v hv hH
      obtain ⟨o,_,rfl⟩ := Finset.mem_map.mp hv
      exact (Finset.mem_sdiff.mp o.2).2 hH
    have h := strictHallGraph G A B SO hd hab hA hB hdis hsO
    have he : (S.biUnion (fun o => Finset.univ.filter (R o))).map
        ⟨Subtype.val,Subtype.val_injective⟩ = nbrs G SO ∩ K := by
      ext v
      simp only [Finset.mem_map,Finset.mem_biUnion,Finset.mem_filter,
        Finset.mem_univ,true_and,Finset.mem_inter,mem_nbrs]
      change (∃ (k : K), (∃ o ∈ S, R o k) ∧ k.1 = v) ↔
        (∃ u ∈ SO, G.Adj u v) ∧ v ∈ K
      constructor
      · rintro ⟨k,⟨o,ho,ha⟩,rfl⟩
        exact ⟨⟨o.1,Finset.mem_map.mpr ⟨o,ho,rfl⟩,ha⟩,k.2⟩
      · rintro ⟨⟨u,hu,e⟩,hk⟩
        obtain ⟨o,ho,rfl⟩ := Finset.mem_map.mp hu
        exact ⟨⟨_,hk⟩,⟨o,ho,e⟩,rfl⟩
    rw [← he, Finset.card_map] at h
    simpa [SO] using h
  obtain ⟨f,g,rank,hf,hr,hfr,hgr⟩ := strictHall_rank R hHall
  have hCov : ∀ x ∈ (Finset.univ : Finset K), ∃ o, R o x := by
    intro x _
    obtain ⟨y,e⟩ := hNI x.1
    have hy : y ∈ O := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hy => hno x.2 hy e⟩
    exact ⟨⟨y,hy⟩,e.symm⟩
  obtain ⟨C,P,_,hm,hp,hcp⟩ :=
    ranked_cover R f g rank hf hr hfr hgr Finset.univ Finset.univ hCov
      (by intro o _; simp)
  let CV : Finset V := C.map ⟨Subtype.val,Subtype.val_injective⟩
  let PV : Finset V := P.map ⟨Subtype.val,Subtype.val_injective⟩
  refine ⟨Q ∪ CV ∪ PV, ?_, ?_⟩
  · intro v
    by_cases hvK : v ∈ K
    · obtain ⟨o,ho,e⟩ := hp ⟨v,hvK⟩ (Finset.mem_univ _)
      exact ⟨o.1,Finset.mem_union_right _ (Finset.mem_map.mpr ⟨o,ho,rfl⟩), e.symm⟩
    by_cases hvH : v ∈ H
    · obtain ⟨u,hu,e⟩ := hQ v (Finset.mem_sdiff.mpr ⟨hvH,hvK⟩)
      exact ⟨u,Finset.mem_union_left _ (Finset.mem_union_left _ hu),e⟩
    let o : O := ⟨v,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hvH⟩⟩
    rcases hm o (Finset.mem_univ _) with ho|ho
    · exact ⟨(f o).1,Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨f o,ho,rfl⟩)),hfr o⟩
    · exact ⟨(g o).1,Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨g o,ho,rfl⟩)),hgr o⟩
  · rw [hcrit]
    have h1 := Finset.card_union_le Q CV
    have h2 := Finset.card_union_le (Q ∪ CV) PV
    have h3 := Finset.card_sdiff_add_card_eq_card hsub
    have h4 : CV.card = C.card := Finset.card_map _
    have h5 : PV.card = P.card := Finset.card_map _
    rw [Finset.card_univ,Fintype.card_coe] at hcp
    change Q.card + K.card = H.card at h3
    omega

/-- Exact Graffiti.pc #412d, strengthened from nontrivial connected graphs to isolate-free graphs.
    The disjoint independent sets A and B are the two parts of a bipartition. -/
theorem graffiti412d_exact (A B : Finset V) (hd : Disjoint A B) (hab : A ∪ B = Finset.univ)
    (hA : Indep G A) (hB : Indep G B) (hNI : ∀ v, ∃ u, G.Adj v u) :
    totalDominationNumber G ≤ (critCorona G).card := by
  classical
  obtain ⟨D,hD,hc⟩ := exact_witness G A B hd hab hA hB hNI
  have hm : D.card ∈ {k : ℕ | ∃ E : Finset V, TotalDominates G E ∧ E.card = k} :=
    ⟨D,hD,rfl⟩
  exact (Nat.sInf_le hm).trans hc

/-- The original connected, order-greater-than-two statement. -/
theorem graffiti412d_catalogue (hc : G.Connected) (hn : 2 < Fintype.card V)
    (hBip : ∃ A B : Finset V, Disjoint A B ∧ A ∪ B = Finset.univ ∧
      Indep G A ∧ Indep G B) :
    totalDominationNumber G ≤ (critCorona G).card := by
  obtain ⟨A,B,hd,hab,hA,hB⟩ := hBip
  apply graffiti412d_exact G A B hd hab hA hB
  intro v
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v w
  have hz : 0 < p.length := by
    rw [hp]
    exact hc.pos_dist_of_ne hw.symm
  exact ⟨p.getVert 1, by simpa using p.adj_getVert_succ (i := 0) hz⟩

#print axioms graffiti412d_catalogue
#print axioms graffiti412d_exact
end Graffiti412d
