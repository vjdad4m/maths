/-
# Graffiti.pc #376: isolated maximum-degree vertices and transmission minima

Let T be a finite simple tree of order n>2. Let M be the set of vertices of maximum degree Δ, I the isolates of T[M], and C the set minimizing the total distance τ(v)=Σₓ dist(v,x), also called transmission. Then **γₜ(T) ≥ |I|+|C|**.

The [official Written on the Wall II data](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json) lists #376 open, announced February 18, 2009. [AI Village's separate #378 report](https://grok-ai-village-news-496089.gitlab.io/articles/opus5-wow2-conj378-false-one-hundred-sixty-four) explicitly lists only an earlier finite #376 search, with no violations. Exact-statement and number searches and the earlier research worklogs did not turn up a proof of #376. This is not a priority claim.

## Tree transmission facts

For an oriented edge uv, let B(u,v) be the vertices closer to v than to u. In a tree, deleting uv separates the two sides, and the distance to any vertex changes by one across uv, decreasing exactly on B(u,v). Hence τ(v)−τ(u)=n−2|B(u,v)|.

In particular a leaf v with neighbor u has |B(u,v)|=1 and strictly larger transmission than u. Also, for distinct neighbors a,c of b, B(b,a) and B(b,c) are disjoint and neither contains b. Thus τ(a)+τ(c)≥2τ(b)+2. This strict convexity along paths shows distinct transmission minima must be adjacent: starting at a minimum, the first increment along a path is nonnegative, and each subsequent increment is strictly larger. Three distinct minima would contradict the same strict convexity. Therefore |C|≤2.

## Proof of the bound

Let D be any total dominating set, t=|D| and k=|I|. As in #377, the independent maximum-degree set I gives kΔ≤n−1, and the open neighborhoods of D give n≤tΔ. Hence t≥k+1, and t≥k+2 already suffices.

Suppose t=k+1. Then k≥1 because total domination needs at least two vertices. If Δ≤2, a vertex of I has only leaves as neighbors, and this star is all of T by connectivity. Its center is the only possible transmission minimum.

If Δ≥3, put q=|D∩I|. The #379 edge reservation argument gives (k−q)(Δ−1)≤t−q−1=k−q. Thus q=k, so D contains I and exactly one other vertex z. Every vertex outside D is a leaf, because its reserved edge is the only edge incident to it once no unreserved edges remain. Since I is independent and D totally dominates, each v in I is adjacent to z. All other neighbors of v are leaves, so B(z,v) consists of v and these leaves and has size Δ.

- If k≥2, then n≥kΔ+1>2Δ, so τ(v)>τ(z) for every v∈I. Leaves cannot minimize transmission; only z can.
- If k=1, write I={v}. Also all neighbors of z other than v are leaves, so |B(v,z)|=deg(z). The two branches partition V, giving n=Δ+deg(z). Since v is isolated in T[M] and adjacent to z, we have deg(z)<Δ, so τ(z)>τ(v). Here only v can minimize transmission.

Thus |C|≤1 in the case t=k+1, proving the claim. Apply it to a minimum total dominating set.


Verified with Lean/Mathlib v4.19.0. Entry point: Graffiti376.conjecture376.
-/
/- Reproduce with Lean 4.19.0 and Mathlib v4.19.0: run this source with lake env lean. -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Combinatorics.SimpleGraph.Metric

/- Proof module: Exact379 -/
set_option warningAsError true
set_option linter.unusedSectionVars false
open Finset
open scoped BigOperators

namespace Graffiti379
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def TotalDom (D : Finset V) : Prop := ∀ v, ∃ w ∈ D, G.Adj v w

noncomputable def totalDomination : Nat :=
  sInf {k | ∃ D, TotalDom G D ∧ D.card = k}

def maxVertices : Finset V := Finset.univ.filter (fun v => G.degree v = G.maxDegree)

noncomputable def maxComponentCount : Nat :=
  Nat.card ((G.induce (maxVertices G : Set V)).ConnectedComponent)

def distinctDegrees : Nat := ((Finset.univ : Finset V).image (fun v => G.degree v)).card

theorem representatives : ∃ I : Finset V, I.card = maxComponentCount G ∧
    (∀ v ∈ I, G.degree v = G.maxDegree) ∧
    (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v) := by
  classical
  let H := G.induce (maxVertices G : Set V)
  have hex (c : H.ConnectedComponent) : ∃ v, H.connectedComponentMk v = c := Quot.exists_rep c
  let rep (c : H.ConnectedComponent) : (maxVertices G : Set V) := Classical.choose (hex c)
  have hrep (c : H.ConnectedComponent) : H.connectedComponentMk (rep c) = c :=
    Classical.choose_spec (hex c)
  letI : Finite H.ConnectedComponent := Finite.of_surjective _ (fun c => ⟨rep c,hrep c⟩)
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let f : H.ConnectedComponent → V := fun c => (rep c).1
  have inj : Function.Injective f := by
    intro a b h
    have hs : rep a = rep b := Subtype.ext h
    exact (hrep a).symm.trans ((congrArg H.connectedComponentMk hs).trans (hrep b))
  let I := Finset.univ.image f
  refine ⟨I,?_,?_,?_⟩
  · unfold I
    rw [Finset.card_image_of_injOn inj.injOn]
    simp [maxComponentCount, H, Nat.card_eq_fintype_card]
  · intro v hv
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp (rep c).property).2
  · intro u hu v hv ne edge
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hv
    have hadj : H.Adj (rep c) (rep d) := edge
    have hcd := SimpleGraph.ConnectedComponent.sound hadj.reachable
    rw [hrep c,hrep d] at hcd
    exact ne (congrArg f hcd)

theorem incident_disjoint {I : Finset V}
    (hI : ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v) :
    Set.PairwiseDisjoint (↑I : Set V) (fun v : V => G.incidenceFinset v) := by
  intro u hu v hv ne
  apply Finset.disjoint_left.mpr
  intro e hue hve
  have h1 := (G.mem_incidenceFinset u e).mp hue
  have h2 := (G.mem_incidenceFinset v e).mp hve
  exact hI u hu v hv ne (SimpleGraph.adj_iff_exists_edge.mpr ⟨ne,e,h1.1,h1.2,h2.2⟩)

theorem independentDegree (I : Finset V)
    (hI : ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v)
    (hmax : ∀ v ∈ I, G.degree v = G.maxDegree) :
    I.card * G.maxDegree ≤ G.edgeFinset.card := by
  have hx := Finset.card_biUnion (incident_disjoint G hI)
  rw [Finset.sum_const_nat (fun v hv =>
    (G.card_incidenceFinset_eq_degree v).trans (hmax v hv))] at hx
  rw [← hx]
  apply Finset.card_le_card
  intro e he
  obtain ⟨u,_,he⟩ := Finset.mem_biUnion.mp he
  exact SimpleGraph.mem_edgeFinset.mpr ((G.mem_incidenceFinset u e).mp he).1

theorem dominatingDegree (D : Finset V) (hD : TotalDom G D) :
    Fintype.card V ≤ D.card * G.maxDegree := by
  have hc : (Finset.univ : Finset V) ⊆ D.biUnion (fun w => G.neighborFinset w) := by
    intro v _
    obtain ⟨w,hw,e⟩ := hD v
    exact Finset.mem_biUnion.mpr ⟨w,hw,(G.mem_neighborFinset w v).mpr e.symm⟩
  calc
    Fintype.card V ≤ (D.biUnion (fun w => G.neighborFinset w)).card := by
      simpa using Finset.card_le_card hc
    _ ≤ ∑ w ∈ D, (G.neighborFinset w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ D, G.maxDegree := by
      apply Finset.sum_le_sum
      intro w _
      rw [G.card_neighborFinset_eq_degree]
      exact G.degree_le_maxDegree w
    _ = D.card * G.maxDegree := Finset.sum_const_nat (fun _ _ => rfl)

theorem minDomExists (hT : G.IsTree) (hn : 2 < Fintype.card V) :
    ∃ D : Finset V, TotalDom G D ∧ D.card = totalDomination G := by
  classical
  have hd : TotalDom G Finset.univ := by
    intro v
    obtain ⟨w,hne⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
    obtain ⟨p⟩ := hT.isConnected v w
    cases p with
    | nil => exact False.elim (hne rfl)
    | @cons _ u _ he _ => exact ⟨u,Finset.mem_univ _,he⟩
  have ha : ({k : Nat | ∃ D : Finset V, TotalDom G D ∧ D.card = k}).Nonempty :=
    ⟨_,_,hd,rfl⟩
  exact Nat.sInf_mem ha

/-- One edge is reserved for each vertex outside D and for each independent
representative inside D. These edge choices are mutually distinct. -/
theorem residualBound (hT : G.IsTree) (I D : Finset V) (hD : TotalDom G D)
    (hI : ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v)
    (hmax : ∀ v ∈ I, G.degree v = G.maxDegree) :
    ((I \ D).card * (G.maxDegree-1) ≤ D.card - (I∩D).card - 1) ∧
    ∀ v, v ∉ D → G.degree v ≤ D.card - (I∩D).card := by
  classical
  let OUT := (Finset.univ : Finset V) \ D
  let IN := I ∩ D
  let X := OUT ∪ IN
  let f (v : V) : V := Classical.choose (hD v)
  have fD (v : V) : f v ∈ D := (Classical.choose_spec (hD v)).1
  have fAdj (v : V) : G.Adj v (f v) := (Classical.choose_spec (hD v)).2
  let chooseEdge (v : V) : Sym2 V := s(v,f v)
  let reserved := X.image chooseEdge
  have hinD (u : V) (hu : u ∈ X) (h : u ∈ D) : u ∈ I := by
    rcases Finset.mem_union.mp hu with ho | hi
    · exact False.elim ((Finset.mem_sdiff.mp ho).2 h)
    · exact (Finset.mem_inter.mp hi).1
  have inj : Set.InjOn chooseEdge (↑X : Set V) := by
    intro u hu v hv h
    change u ∈ X at hu
    change v ∈ X at hv
    change s(u,f u) = s(v,f v) at h
    rcases Sym2.eq_iff.mp h with h | h
    · exact h.1
    · have uD : u ∈ D := h.1.symm ▸ fD v
      have vD : v ∈ D := h.2 ▸ fD u
      have e : G.Adj u v := h.2 ▸ fAdj u
      exact False.elim (hI u (hinD u hu uD) v (hinD v hv vD) e.ne e)
  have reserveSub : reserved ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp he
    exact SimpleGraph.mem_edgeFinset.mpr (G.mem_edgeSet.mpr (fAdj u))
  have hdisjoint : Disjoint OUT IN := by
    apply Finset.disjoint_left.mpr
    intro u h₁ h₂
    exact (Finset.mem_sdiff.mp h₁).2 (Finset.mem_inter.mp h₂).2
  have hX : X.card = (Fintype.card V - D.card) + IN.card := by
    rw [Finset.card_union_of_disjoint hdisjoint]
    have h := Finset.card_sdiff (Finset.subset_univ D)
    simpa [OUT] using congrArg (fun a : Nat => a + IN.card) h
  have hrr : reserved.card = X.card := Finset.card_image_of_injOn inj
  let R := G.edgeFinset \ reserved
  have hR := Finset.card_sdiff_add_card_eq_card reserveSub
  change R.card + reserved.card = G.edgeFinset.card at hR
  have hTree := hT.card_edgeFinset
  have hDc : D.card ≤ Fintype.card V := Finset.card_le_univ D
  have hin : IN.card ≤ D.card := Finset.card_le_card Finset.inter_subset_right
  have hRc : R.card + 1 + IN.card = D.card := by omega
  let rest (u : V) := (G.incidenceFinset u).erase (chooseEdge u)
  have restSub (u : V) (hu : u ∉ D) : rest u ⊆ R := by
    intro e he
    have ino := Finset.mem_erase.mp he
    have inc := (G.mem_incidenceFinset u e).mp ino.2
    apply Finset.mem_sdiff.mpr
    refine ⟨SimpleGraph.mem_edgeFinset.mpr inc.1,?_⟩
    intro h
    obtain ⟨v,_,hv⟩ := Finset.mem_image.mp h
    rw [← hv] at inc
    have e' : u ∈ s(v,f v) := inc.2
    rcases Sym2.mem_iff.mp e' with eq | eq
    · subst u
      exact ino.1 hv.symm
    · exact hu (eq.symm ▸ fD v)
  have restCard (u : V) : (rest u).card = G.degree u - 1 := by
    have ce : chooseEdge u ∈ G.incidenceFinset u :=
      (G.mem_incidenceFinset u _).mpr ((G.mem_incidenceSet u (f u)).mpr (fAdj u))
    rw [Finset.card_erase_of_mem ce,G.card_incidenceFinset_eq_degree]
  have hDis : Set.PairwiseDisjoint (↑(I \ D) : Set V) rest := by
    intro u hu v hv hne
    change u ∈ I \ D at hu
    change v ∈ I \ D at hv
    have hn := incident_disjoint G hI
    have hdis := hn (Finset.mem_sdiff.mp hu).1 (Finset.mem_sdiff.mp hv).1 hne
    exact hdis.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  have hcount : ((I \ D).biUnion rest).card = (I \ D).card * (G.maxDegree-1) := by
    rw [Finset.card_biUnion hDis]
    apply Finset.sum_const_nat
    intro u hu
    rw [restCard,hmax u (Finset.mem_sdiff.mp hu).1]
  have hsub : ((I \ D).biUnion rest) ⊆ R := by
    intro e he
    obtain ⟨u,hu,hue⟩ := Finset.mem_biUnion.mp he
    exact restSub u (Finset.mem_sdiff.mp hu).2 hue
  have hlo := Finset.card_le_card hsub
  rw [hcount] at hlo
  constructor
  · change (I \ D).card * (G.maxDegree-1) ≤ D.card-IN.card-1
    omega
  · intro u hu
    have deg := Finset.card_le_card (restSub u hu)
    rw [restCard] at deg
    change G.degree u ≤ D.card - IN.card
    omega

private theorem degree_pos (hT : G.IsTree) (hn : 2 < Fintype.card V) (v : V) :
    0 < G.degree v := by
  obtain ⟨D,hD,_⟩ := minDomExists G hT hn
  obtain ⟨w,_,hw⟩ := hD v
  have h := Finset.card_pos.mpr ⟨w,(G.mem_neighborFinset v w).mpr hw⟩
  simpa [G.card_neighborFinset_eq_degree] using h


theorem bound379 (hT : G.IsTree) (hn : 2 < Fintype.card V)
    (D : Finset V) (hD : TotalDom G D) :
    3*maxComponentCount G + distinctDegrees G ≤ 3*D.card := by
  classical
  obtain ⟨I, hIc, hDeg, hI⟩ := representatives G
  let k := I.card
  let t := D.card
  let d := G.maxDegree
  let δ := t-k
  have he := hT.card_edgeFinset
  have h1 : k*d ≤ G.edgeFinset.card := independentDegree G I hI hDeg
  have h2 : Fintype.card V ≤ t*d := dominatingDegree G D hD
  have hkt : k < t := by
    by_cases hb : t ≤ k
    · have hh := Nat.mul_le_mul_right d hb
      omega
    · omega
  have hδpos : 1 ≤ δ := by dsimp [δ]; omega
  have ht : t = k+δ := by dsimp [δ]; omega
  have hPos : ∀ u, 0 < G.degree u := degree_pos G hT hn
  have degreeRange (b : Nat) : ((Finset.range (b+1)).erase 0).card = b := by
    have hm : 0 ∈ Finset.range (b+1) := by simp
    rw [Finset.card_erase_of_mem hm,Finset.card_range]
    omega
  have memRange (b : Nat) (v : V) (h : G.degree v ≤ b) :
      G.degree v ∈ (Finset.range (b+1)).erase 0 := by
    apply Finset.mem_erase.mpr
    exact ⟨Nat.ne_of_gt (hPos v),Finset.mem_range.mpr (by omega)⟩
  have endProof (h : distinctDegrees G ≤ 3*δ) :
      3*maxComponentCount G + distinctDegrees G ≤ 3*D.card := by
    change 3*maxComponentCount G + distinctDegrees G ≤ 3*t
    have hk : k = maxComponentCount G := hIc
    omega
  apply endProof
  by_cases easy : d ≤ 3*δ
  · let A := (Finset.range (3*δ+1)).erase 0
    have hd : ((Finset.univ : Finset V).image (fun v => G.degree v)) ⊆ A := by
      intro e he
      obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp he
      exact memRange _ _ (Nat.le_trans (G.degree_le_maxDegree v) easy)
    have hb := Finset.card_le_card hd
    rw [degreeRange] at hb
    exact hb
  · obtain ⟨hx,hOutside⟩ := residualBound G hT I D hD hI hDeg
    let j := (I \ D).card
    let q := (I ∩ D).card
    have hsplit : q+j=k := Finset.card_inter_add_card_sdiff I D
    change j*(d-1) ≤ t-q-1 at hx
    have hj : j = 0 := by
      by_cases hn : 1 ≤ j
      · have Δ2 : d-1 = (d-2)+1 := by omega
        have low := Nat.mul_le_mul_left (d-2) hn
        rw [Nat.mul_one] at low
        rw [Δ2,Nat.mul_add,Nat.mul_one,Nat.mul_comm j (d-2)] at hx
        omega
      · omega
    have hq : q=k := by omega
    have hDCard : (D \ I).card = δ := by
      have hcard := Finset.card_inter_add_card_sdiff D I
      rw [Finset.inter_comm D I] at hcard
      change q + (D \ I).card = t at hcard
      omega
    let A := (Finset.range (δ+1)).erase 0
    let B := insert d ((D \ I).image (fun v => G.degree v))
    have hsub : ((Finset.univ : Finset V).image (fun v => G.degree v)) ⊆ A∪B := by
      intro e he
      obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp he
      by_cases hu : u ∈ D
      · apply Finset.mem_union.mpr
        right
        by_cases hi : u ∈ I
        · apply Finset.mem_insert.mpr
          exact Or.inl (hDeg u hi)
        · apply Finset.mem_insert.mpr
          exact Or.inr (Finset.mem_image.mpr ⟨u,Finset.mem_sdiff.mpr ⟨hu,hi⟩,rfl⟩)
      · apply Finset.mem_union.mpr
        left
        have hout := hOutside u hu
        change G.degree u ≤ t-q at hout
        exact memRange δ u (by omega)
    have aC : A.card=δ := degreeRange δ
    have bC : B.card ≤ δ+1 := by
      calc
        B.card ≤ ((D \ I).image (fun v => G.degree v)).card+1 :=
          Finset.card_insert_le d _
        _ ≤ (D \ I).card+1 := Nat.add_le_add_right Finset.card_image_le _
        _ = δ+1 := by rw [hDCard]
    have hu := Finset.card_union_le A B
    have hd := Finset.card_le_card hsub
    change distinctDegrees G ≤ (A∪B).card at hd
    omega

/-- Graffiti.pc #379, with the denominator 3 cleared. -/
theorem conjecture379 (hT : G.IsTree) (hn : 2 < Fintype.card V) :
    3*maxComponentCount G + distinctDegrees G ≤ 3*totalDomination G := by
  obtain ⟨D,hD,he⟩ := minDomExists G hT hn
  rw [← he]
  exact bound379 G hT hn D hD

#print axioms conjecture379
end Graffiti379

/- Proof module: Exact377 -/
set_option warningAsError true
set_option linter.unusedSectionVars false
open Finset
open scoped BigOperators

namespace Graffiti377
open Graffiti379
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def isolatedMax : Finset V := by
  classical exact Finset.univ.filter (fun v =>
    G.degree v = G.maxDegree ∧ ∀ w, G.Adj v w → G.degree w ≠ G.maxDegree)

theorem isolatedMaxExact (v : V) :
    v ∈ isolatedMax G ↔ G.degree v = G.maxDegree ∧
      ∀ w, G.Adj v w → G.degree w ≠ G.maxDegree := by
  classical
  simp [isolatedMax]

def lowerDegreeCount (d : Nat) : Nat :=
  ((Finset.univ : Finset V).filter (fun v => G.degree v ≤ d)).card

/-- Least degree threshold covering strictly over half the vertices:
the higher of the middle two entries for an even order. -/
noncomputable def upperMedian : Nat :=
  sInf {d : Nat | Fintype.card V / 2 < lowerDegreeCount G d}

theorem medianLe (b : Nat) (h : Fintype.card V/2 < lowerDegreeCount G b) :
    upperMedian G ≤ b := Nat.sInf_le h

theorem minDegreePositive (D : Finset V) (hD : TotalDom G D) (v : V) :
    1 ≤ G.degree v := by
  obtain ⟨w,_,hw⟩ := hD v
  have h := Finset.card_pos.mpr ⟨w,(G.mem_neighborFinset v w).mpr hw⟩
  simpa [G.card_neighborFinset_eq_degree] using h

theorem medianLeTwo (hT : G.IsTree) (D : Finset V) (hD : TotalDom G D) :
    upperMedian G ≤ 2 := by
  classical
  apply medianLe
  let A := (Finset.univ : Finset V).filter (fun v => G.degree v ≤ 2)
  let B := (Finset.univ : Finset V) \ A
  have hs := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  change B.card + A.card = (Finset.univ : Finset V).card at hs
  rw [Finset.card_univ] at hs
  have ha : A.card ≤ ∑ v ∈ A, G.degree v := by
    calc
      A.card = ∑ _v ∈ A, (1 : Nat) := by simp
      _ ≤ ∑ v ∈ A, G.degree v := Finset.sum_le_sum (fun v _ => minDegreePositive G D hD v)
  have hb : 3*B.card ≤ ∑ v ∈ B, G.degree v := by
    calc
      3*B.card = ∑ _v ∈ B, (3 : Nat) := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ B, G.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        have hn := (Finset.mem_sdiff.mp hv).2
        have h : ¬ G.degree v ≤ 2 := by simpa [A] using hn
        omega
  have hsum := Finset.sum_sdiff (f := fun v => G.degree v) (Finset.subset_univ A)
  change (∑ v ∈ B, G.degree v) + (∑ v ∈ A, G.degree v) = _ at hsum
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  have ht := hT.card_edgeFinset
  change Fintype.card V/2 < A.card
  omega

theorem closedOfWalk {u v : V} {C : Finset V} (p : G.Walk u v)
    (hc : ∀ x y, x ∈ C → G.Adj x y → y ∈ C) (hu : u ∈ C) : v ∈ C := by
  induction p with
  | nil => exact hu
  | cons h _ ih => exact ih (hc _ _ hu h)

theorem lowMaxCase (hT : G.IsTree) (hn : 2 < Fintype.card V)
    (D : Finset V) (hD : TotalDom G D) (v : V) (hv : v ∈ isolatedMax G)
    (hΔ : G.maxDegree ≤ 2) : upperMedian G ≤ 1 := by
  classical
  obtain ⟨hvΔ,hvIso⟩ := (isolatedMaxExact G v).mp hv
  let N := G.neighborFinset v
  let C := insert v N
  have hLeaf (w : V) (hw : w ∈ N) : G.degree w = 1 := by
    have hnot := hvIso w ((G.mem_neighborFinset v w).mp hw)
    have hle := G.degree_le_maxDegree w
    have hp := minDegreePositive G D hD w
    omega
  have closed (x y : V) (hx : x ∈ C) (e : G.Adj x y) : y ∈ C := by
    rcases Finset.mem_insert.mp hx with rfl | hM
    · exact Finset.mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr e)
    · have hA : y ∈ G.neighborFinset x := (G.mem_neighborFinset _ _).mpr e
      have hB : v ∈ G.neighborFinset x :=
        (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hM).symm
      have hC : (G.neighborFinset x).card = 1 :=
        (G.card_neighborFinset_eq_degree _).trans (hLeaf x hM)
      obtain ⟨z,hz⟩ := Finset.card_eq_one.mp hC
      rw [hz,Finset.mem_singleton] at hA hB
      have he : y = v := hA.trans hB.symm
      exact Finset.mem_insert.mpr (Or.inl he)
  have cover : (Finset.univ : Finset V) ⊆ C := by
    intro w _
    obtain ⟨p⟩ := hT.isConnected v w
    exact closedOfWalk G p closed (Finset.mem_insert_self _ _)
  have hnC := Finset.card_le_card cover
  rw [Finset.card_univ] at hnC
  have hC := Finset.card_insert_le v N
  change C.card ≤ N.card+1 at hC
  have hN : N.card = G.degree v := G.card_neighborFinset_eq_degree v
  have hen : Fintype.card V = 3 := by omega
  have hNe : N.card = 2 := by omega
  apply medianLe
  have hi : N ⊆ (Finset.univ : Finset V).filter (fun u => G.degree u ≤ 1) := by
    intro u hu
    simp [hLeaf u hu]
  have he := Finset.card_le_card hi
  unfold lowerDegreeCount
  omega

theorem degreeLeavesFour (hT : G.IsTree) (D : Finset V) (hD : TotalDom G D)
    (h4 : Fintype.card V = 4) (v : V) (hdeg : 3 ≤ G.degree v) :
    upperMedian G ≤ 1 := by
  classical
  let R := (Finset.univ : Finset V).erase v
  have hRC : R.card = 3 := by
    simp [R,Finset.card_erase_of_mem, h4]
  have degreeR (u : V) (hu : u ∈ R) : G.degree u ≤ 1 := by
    let S := R.erase u
    have hS : S.card = 2 := by
      rw [Finset.card_erase_of_mem hu,hRC]
    have hSum := Finset.sum_erase_add (s := (Finset.univ : Finset V))
      (f := fun w => G.degree w) (Finset.mem_univ v)
    change (∑ w ∈ R, G.degree w) + G.degree v = _ at hSum
    rw [G.sum_degrees_eq_twice_card_edges] at hSum
    have ht := hT.card_edgeFinset
    have hs := Finset.sum_erase_add (s := R) (f := fun w => G.degree w) hu
    change (∑ w ∈ S, G.degree w) + G.degree u = (∑ w ∈ R, G.degree w) at hs
    have hlo : S.card ≤ ∑ w ∈ S, G.degree w := by
      calc
        S.card = ∑ _w ∈ S, (1 : Nat) := by simp
        _ ≤ ∑ w ∈ S, G.degree w := Finset.sum_le_sum (fun w _ => minDegreePositive G D hD w)
    omega
  have incl : R ⊆ (Finset.univ : Finset V).filter (fun u => G.degree u ≤ 1) := by
    intro u hu; simp [degreeR u hu]
  have h := Finset.card_le_card incl
  apply medianLe
  unfold lowerDegreeCount
  omega

theorem bound377 (hT : G.IsTree) (hn : 2 < Fintype.card V)
    (D : Finset V) (hD : TotalDom G D) :
    (isolatedMax G).card + upperMedian G ≤ D.card := by
  classical
  let I := isolatedMax G
  let k := I.card
  let t := D.card
  let d := G.maxDegree
  have hDeg : ∀ v ∈ I, G.degree v = d := fun v hv => ((isolatedMaxExact G v).mp hv).1
  have hInd : ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v := by
    intro u hu v hv _ he
    exact ((isolatedMaxExact G u).mp hu).2 v he (hDeg v hv)
  have h₁ : k*d ≤ G.edgeFinset.card := independentDegree G I hInd hDeg
  have hn' : Fintype.card V ≤ t*d := dominatingDegree G D hD
  have hEdge := hT.card_edgeFinset
  have hkt : k < t := by
    by_cases hb : t ≤ k
    · have hh := Nat.mul_le_mul_right d hb
      omega
    · omega
  have hmed := medianLeTwo G hT D hD
  change k + upperMedian G ≤ t
  by_cases easy : k+2 ≤ t
  · omega
  have htk : t=k+1 := by omega
  have ht2 : 2 ≤ t := by
    letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨w,hw,_⟩ := hD (Classical.choice (inferInstance : Nonempty V))
    obtain ⟨z,hz,e⟩ := hD w
    have hsub : ({w,z} : Finset V) ⊆ D := by
      simp [Finset.insert_subset_iff,hw,hz]
    have hb := Finset.card_le_card hsub
    rwa [Finset.card_pair e.ne] at hb
  have hkp : 1 ≤ k := by omega
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  have hvΔ := hDeg v hv
  by_cases low : d ≤ 2
  · have hl := lowMaxCase G hT hn D hD v hv low
    omega
  obtain ⟨hx,hout⟩ := residualBound G hT I D hD hInd hDeg
  let j := (I \ D).card
  let q := (I ∩ D).card
  have hsplit : q+j=k := Finset.card_inter_add_card_sdiff I D
  change j*(d-1) ≤ t-q-1 at hx
  have hj : j = 0 := by
    have h3 : 2 ≤ d-1 := by omega
    have hlo := Nat.mul_le_mul_left j h3
    rw [Nat.mul_comm j 2] at hlo
    omega
  have hq : t-q=1 := by omega
  have degreeOut (u : V) (hu : u ∉ D) : G.degree u ≤ 1 := by
    have he := hout u hu
    change G.degree u ≤ t-q at he
    omega
  by_cases h4 : Fintype.card V = 4
  · have hdeg : 3 ≤ G.degree v := by omega
    have hm := degreeLeavesFour G hT D hD h4 v hdeg
    omega
  let OUT := (Finset.univ : Finset V) \ D
  have cOut : OUT.card = Fintype.card V-t := by
    have hc := Finset.card_sdiff (Finset.subset_univ D)
    simpa [OUT,t] using hc
  have inc : OUT ⊆ (Finset.univ : Finset V).filter (fun u => G.degree u ≤ 1) := by
    intro u hu
    simp [degreeOut u (Finset.mem_sdiff.mp hu).2]
  have hc := Finset.card_le_card inc
  have hN : 3*k≤G.edgeFinset.card := by
    have hge : 3≤d := by omega
    exact Nat.le_trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left k hge) h₁
  have nLarge : 2*t < Fintype.card V := by
    by_cases hk : k=1
    · omega
    · omega
  have hm : upperMedian G ≤ 1 := by
    apply medianLe
    unfold lowerDegreeCount
    omega
  omega

/-- Graffiti.pc #377, with the upper median taken at the higher middle rank. -/
theorem conjecture377 (hT : G.IsTree) (hn : 2 < Fintype.card V) :
    (isolatedMax G).card + upperMedian G ≤ totalDomination G := by
  obtain ⟨D,hD,he⟩ := minDomExists G hT hn
  rw [← he]
  exact bound377 G hT hn D hD

#print axioms conjecture377
end Graffiti377

/- Proof module: MedianMetric -/
set_option warningAsError true
set_option linter.unusedSectionVars false
open Finset SimpleGraph
open scoped BigOperators

namespace Median376
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

noncomputable def transmission (u : V) : Nat := ∑ x : V, G.dist u x

noncomputable def medians : Finset V := by
  classical exact Finset.univ.filter (fun v => ∀ w, transmission G v ≤ transmission G w)

theorem medians_exact (v : V) :
    v ∈ medians G ↔ ∀ w, transmission G v ≤ transmission G w := by
  classical
  simp [medians]

noncomputable def branch (u v : V) : Finset V := by
  classical exact Finset.univ.filter (fun w => G.dist v w < G.dist u w)

theorem branch_exact (u v w : V) :
    w ∈ branch G u v ↔ G.dist v w < G.dist u w := by
  classical
  simp [branch]

theorem pathDist (hG : G.IsTree) {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    p.length = G.dist u v := by
  obtain ⟨q,hq,hLen⟩ := hG.isConnected.exists_path_of_dist u v
  have he := hG.IsAcyclic.path_unique ⟨p,hp⟩ ⟨q,hq⟩
  exact (congrArg (fun r : G.Path u v => r.val.length) he).trans hLen

theorem stepDist (hG : G.IsTree) {u v : V} (e : G.Adj u v) (w : V) :
    G.dist v w+1 = G.dist u w ∨ G.dist u w+1 = G.dist v w := by
  obtain ⟨p,hp,_⟩ := hG.isConnected.exists_path_of_dist u w
  by_cases hv : v ∈ p.support
  · have hpre := pathDist G hG (p.takeUntil v hv) (hp.takeUntil hv)
    have htail := pathDist G hG (p.dropUntil v hv) (hp.dropUntil hv)
    have whole := pathDist G hG p hp
    have hadj := SimpleGraph.dist_eq_one_iff_adj.mpr e
    have hdecomp := congrArg (fun q : G.Walk u w => q.length) (p.take_spec hv)
    change ((p.takeUntil v hv).append (p.dropUntil v hv)).length = p.length at hdecomp
    rw [SimpleGraph.Walk.length_append] at hdecomp
    omega
  · have hp' := (SimpleGraph.Walk.cons_isPath_iff e.symm p).mpr ⟨hp,hv⟩
    have hnew := pathDist G hG (SimpleGraph.Walk.cons e.symm p) hp'
    have hold := pathDist G hG p hp
    rw [SimpleGraph.Walk.length_cons] at hnew
    omega

theorem distinctCloseNeighbors (hG : G.IsTree) {a b c w : V}
    (e : G.Adj b a) (f : G.Adj b c)
    (ha : G.dist a w+1 = G.dist b w) (hc : G.dist c w+1 = G.dist b w) :
    a = c := by
  obtain ⟨p,_,ph⟩ := hG.isConnected.exists_path_of_dist a w
  obtain ⟨q,_,qh⟩ := hG.isConnected.exists_path_of_dist c w
  have hpa : (SimpleGraph.Walk.cons e p).IsPath := by
    apply SimpleGraph.Walk.isPath_of_length_eq_dist
    rw [SimpleGraph.Walk.length_cons,ph,ha]
  have hqc : (SimpleGraph.Walk.cons f q).IsPath := by
    apply SimpleGraph.Walk.isPath_of_length_eq_dist
    rw [SimpleGraph.Walk.length_cons,qh,hc]
  have he := hG.IsAcyclic.path_unique ⟨_,hpa⟩ ⟨_,hqc⟩
  exact (SimpleGraph.Walk.cons.inj (congrArg (fun r : G.Path b w => r.val) he)).1

theorem branchDiff (hG : G.IsTree) {u v : V} (e : G.Adj u v) :
    transmission G v + 2*(branch G u v).card = transmission G u + Fintype.card V := by
  classical
  have point (w : V) : G.dist v w + (if w ∈ branch G u v then 2 else 0) = G.dist u w + 1 := by
    have hd := stepDist G hG e w
    by_cases h : w ∈ branch G u v
    · have hl := (branch_exact G u v w).mp h
      simp [h]
      omega
    · have hl : ¬ G.dist v w < G.dist u w := fun f => h ((branch_exact G u v w).mpr f)
      simp [h]
      omega
  have summed : (∑ w : V, (G.dist v w + (if w ∈ branch G u v then 2 else 0))) =
      (∑ w : V, (G.dist u w + 1)) := Finset.sum_congr rfl (fun w _ => point w)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at summed
  have hsum : (∑ w : V, if w ∈ branch G u v then (2 : Nat) else 0) =
      2*(branch G u v).card := by
    have hs := Finset.sum_filter (s := (Finset.univ : Finset V))
      (fun w => w ∈ branch G u v) (fun _ => (2:Nat))
    have ht : ((Finset.univ : Finset V).filter (fun w => w ∈ branch G u v)) = branch G u v := by
      ext w; simp
    rw [ht] at hs
    simp [← hs, Nat.mul_comm]
  rw [hsum] at summed
  simpa [transmission] using summed

theorem localStrict (hG : G.IsTree) {a b c : V}
    (e : G.Adj a b) (f : G.Adj b c) (ne : a ≠ c) :
    2*transmission G b+2 ≤ transmission G a + transmission G c := by
  classical
  let A := branch G b a
  let C := branch G b c
  have hd : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwC
    have ha := (branch_exact G b a w).mp hwA
    have hc := (branch_exact G b c w).mp hwC
    have hA := stepDist G hG e.symm w
    have hC := stepDist G hG f w
    exact ne (distinctCloseNeighbors G hG (w:=w) e.symm f (by omega) (by omega))
  have hsub : A∪C ⊆ (Finset.univ : Finset V).erase b := by
    intro w hw
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_univ _,⟩
    intro h
    subst w
    rcases Finset.mem_union.mp hw with hw | hw
    · have he := (branch_exact G b a b).mp hw
      rw [SimpleGraph.dist_self] at he
      omega
    · have he := (branch_exact G b c b).mp hw
      rw [SimpleGraph.dist_self] at he
      omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, Finset.card_erase_of_mem (Finset.mem_univ b),
    Finset.card_univ] at hc
  have p1 := branchDiff G hG e.symm
  have p2 := branchDiff G hG f
  change transmission G a + 2*A.card = transmission G b + Fintype.card V at p1
  change transmission G c + 2*C.card = transmission G b + Fintype.card V at p2
  have hp : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨b⟩
  omega

theorem path_increase (hG : G.IsTree) {b z : V} (p : G.Walk b z) :
    ∀ {a : V} (e : G.Adj a b), (SimpleGraph.Walk.cons e p).IsPath →
      transmission G a ≤ transmission G b →
      transmission G b ≤ transmission G z ∧
        (0 < p.length → transmission G b < transmission G z) := by
  induction p with
  | nil =>
    intro _ _ _ _
    exact ⟨Nat.le_refl _, fun h => False.elim (Nat.not_lt_zero _ h)⟩
  | @cons b c z f q ih =>
    intro a e hp hab
    have path' := ((SimpleGraph.Walk.cons_isPath_iff e _).mp hp).1
    have hm := ((SimpleGraph.Walk.cons_isPath_iff e _).mp hp).2
    have hn : a ≠ c := by
      intro eq
      subst c
      apply hm
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support _)
    have he := localStrict G hG e f hn
    have hbc : transmission G b ≤ transmission G c := by omega
    have hz := ih f path' hbc
    exact ⟨by omega, fun _ => by omega⟩

theorem medians_adjacent (hG : G.IsTree) {u v : V}
    (hu : u ∈ medians G) (hv : v ∈ medians G) (hne : u ≠ v) : G.Adj u v := by
  obtain ⟨p,hp,_⟩ := hG.isConnected.exists_path_of_dist u v
  have hU := (medians_exact G u).mp hu
  have hV := (medians_exact G v).mp hv
  cases p with
  | nil => exact False.elim (hne rfl)
  | @cons u w v e q =>
    have hind := path_increase G hG q e hp (hU w)
    cases q with
    | nil => exact e
    | @cons _ y _ e' r =>
      have hpos : 0 < (SimpleGraph.Walk.cons e' r).length := by simp
      have hd := hind.2 hpos
      exact False.elim (Nat.not_lt_of_ge (hV w) hd)

theorem medianAtMostTwo (hG : G.IsTree) : (medians G).card ≤ 2 := by
  classical
  by_cases h : ∃ a ∈ medians G, ∃ b ∈ medians G, a ≠ b
  · obtain ⟨a,ha,b,hb,hne⟩ := h
    have incl : medians G ⊆ ({a,b} : Finset V) := by
      intro c hc
      by_cases e : c=a
      · subst c; simp
      by_cases f : c=b
      · subst c; simp
      have ab := medians_adjacent G hG ha hb hne
      have bc := medians_adjacent G hG hb hc (Ne.symm f)
      have hconv := localStrict G hG ab bc (Ne.symm e)
      have hap := (medians_exact G a).mp ha b
      have hcp := (medians_exact G c).mp hc b
      omega
    have he := Finset.card_le_card incl
    simpa [Finset.card_pair hne] using he
  · by_cases hs : (medians G).Nonempty
    · obtain ⟨a,ha⟩ := hs
      have incl : medians G ⊆ ({a} : Finset V) := by
        intro b hb
        apply Finset.mem_singleton.mpr
        by_cases he : b=a
        · exact he
        · exact False.elim (h ⟨b,hb,a,ha,he⟩)
      have he := Finset.card_le_card incl
      simp at he
      omega
    · have he := Finset.not_nonempty_iff_eq_empty.mp hs
      simp [he]

theorem finiteLeafUnique [DecidableRel G.Adj] {u v w : V}
    (hdeg : G.degree v = 1) (e : G.Adj v u) (f : G.Adj v w) : w=u := by
  have hc : (G.neighborFinset v).card = 1 :=
    (G.card_neighborFinset_eq_degree v).trans hdeg
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
  have hu := (G.mem_neighborFinset v u).mpr e
  have hw := (G.mem_neighborFinset v w).mpr f
  rw [hx,Finset.mem_singleton] at hu hw
  exact hw.trans hu.symm

theorem leafDistance [DecidableRel G.Adj] (hG : G.IsTree) {u v x : V}
    (e : G.Adj v u) (hdeg : G.degree v = 1) (hx : x ≠ v) :
    G.dist v x = G.dist u x + 1 := by
  obtain ⟨p,hp,hl⟩ := hG.isConnected.exists_path_of_dist v x
  cases p with
  | nil => exact False.elim (hx rfl)
  | @cons v w x f q =>
    have hw := finiteLeafUnique G hdeg e f
    subst w
    have hh := pathDist G hG q hp.of_cons
    rw [SimpleGraph.Walk.length_cons,hh] at hl
    exact hl.symm

/-- If all neighbors of v other than u are leaves, the u→v branch contains
v and those leaves and therefore has cardinality degree(v). -/
theorem branchLeaves [DecidableRel G.Adj] (hG : G.IsTree) {u v : V}
    (e : G.Adj u v) (hL : ∀ w, w ≠ u → G.Adj v w → G.degree w = 1) :
    (branch G u v).card = G.degree v := by
  classical
  let B := insert v ((G.neighborFinset v).erase u)
  have eq : branch G u v = B := by
    ext x
    rw [branch_exact]
    change (G.dist v x < G.dist u x) ↔ x ∈ insert v ((G.neighborFinset v).erase u)
    by_cases hx : x=v
    · subst x
      rw [SimpleGraph.dist_self,SimpleGraph.dist_eq_one_iff_adj.mpr e]
      simp
    by_cases hxl : x ≠ u ∧ G.Adj v x
    · obtain ⟨hxu,adj⟩ := hxl
      have hleaf := hL x hxu adj
      have dm := leafDistance G hG adj.symm hleaf (Ne.symm hxu)
      rw [SimpleGraph.dist_comm (u:=x) (v:=u), SimpleGraph.dist_eq_one_iff_adj.mpr e.symm] at dm
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr adj]
      constructor
      · intro _
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxu,(G.mem_neighborFinset v x).mpr adj⟩)
      · intro _
        omega
    have notin : x ∉ insert v ((G.neighborFinset v).erase u) := by
      intro hh
      rcases Finset.mem_insert.mp hh with h | h
      · exact hx h
      · have hp := Finset.mem_erase.mp h
        exact hxl ⟨hp.1,(G.mem_neighborFinset v x).mp hp.2⟩
    suffices h : ¬ G.dist v x < G.dist u x by
      exact ⟨fun h' => False.elim (h h'),fun h' => False.elim (notin h')⟩
    obtain ⟨p,hpath,hlen⟩ := hG.isConnected.exists_path_of_dist v x
    cases p with
    | nil => exact False.elim (hx rfl)
    | @cons v w x f q =>
      have hq := pathDist G hG q hpath.of_cons
      rw [SimpleGraph.Walk.length_cons,hq] at hlen
      by_cases equal : w=u
      · subst w
        omega
      · have hLeaf := hL w equal f
        have xw : x ≠ w := by
          intro equ
          subst x
          exact hxl ⟨equal,f⟩
        have hc := leafDistance G hG f.symm hLeaf xw
        omega
  rw [eq]
  have none : v ∉ (G.neighborFinset v).erase u := by
    intro h
    exact (G.loopless _) ((G.mem_neighborFinset v v).mp (Finset.mem_erase.mp h).2)
  have hu := (G.mem_neighborFinset v u).mpr e.symm
  unfold B
  rw [Finset.card_insert_of_not_mem none,Finset.card_erase_of_mem hu,
    G.card_neighborFinset_eq_degree]
  have hpos := Finset.card_pos.mpr ⟨u,hu⟩
  rw [G.card_neighborFinset_eq_degree] at hpos
  omega

theorem leafNotMedian [DecidableRel G.Adj] (hG : G.IsTree)
    (hn : 2 < Fintype.card V) {u v : V}
    (e : G.Adj u v) (hdeg : G.degree v=1) : v ∉ medians G := by
  have hL : ∀ w, w ≠ u → G.Adj v w → G.degree w = 1 := by
    intro w ne f
    exact False.elim (ne (finiteLeafUnique G hdeg e.symm f))
  have hnB := branchLeaves G hG e hL
  have hf := branchDiff G hG e
  intro h
  have hm := (medians_exact G v).mp h u
  omega

end Median376

/- Proof module: Exact376 -/
set_option warningAsError true
set_option linter.unusedSectionVars false
open Finset SimpleGraph
open scoped BigOperators

namespace Graffiti376
open Graffiti377 Graffiti379 Median376
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem lowMaxUniqueMedian (hT : G.IsTree) (hn : 2 < Fintype.card V)
    (D : Finset V) (hD : TotalDom G D) (v : V) (hv : v ∈ isolatedMax G)
    (hΔ : G.maxDegree ≤ 2) : (medians G).card ≤ 1 := by
  classical
  obtain ⟨_,hvIso⟩ := (isolatedMaxExact G v).mp hv
  let N := G.neighborFinset v
  let C := insert v N
  have hLeaf (w : V) (hw : w ∈ N) : G.degree w = 1 := by
    have hnot := hvIso w ((G.mem_neighborFinset v w).mp hw)
    have hle := G.degree_le_maxDegree w
    have hp := minDegreePositive G D hD w
    omega
  have closed (x y : V) (hx : x ∈ C) (e : G.Adj x y) : y ∈ C := by
    rcases Finset.mem_insert.mp hx with rfl | hM
    · exact Finset.mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr e)
    · have ev := ((G.mem_neighborFinset v x).mp hM).symm
      have eq := finiteLeafUnique G (hLeaf x hM) ev e
      exact Finset.mem_insert.mpr (Or.inl eq)
  have cover (w : V) : w ∈ C := by
    obtain ⟨p⟩ := hT.isConnected v w
    exact closedOfWalk G p closed (Finset.mem_insert_self _ _)
  have hs : medians G ⊆ ({v} : Finset V) := by
    intro w hw
    rcases Finset.mem_insert.mp (cover w) with eq|ho
    · exact Finset.mem_singleton.mpr eq
    · have e := (G.mem_neighborFinset v w).mp ho
      exact False.elim (leafNotMedian G hT hn e (hLeaf w ho) hw)
  simpa using Finset.card_le_card hs

theorem bound376 (hT : G.IsTree) (hn : 2 < Fintype.card V)
    (D : Finset V) (hD : TotalDom G D) :
    (isolatedMax G).card + (medians G).card ≤ D.card := by
  classical
  let I := isolatedMax G
  let k := I.card
  let t := D.card
  let d := G.maxDegree
  have hDeg : ∀ v ∈ I, G.degree v = d := fun v hv => ((isolatedMaxExact G v).mp hv).1
  have hInd : ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v := by
    intro u hu v hv _ he
    exact ((isolatedMaxExact G u).mp hu).2 v he (hDeg v hv)
  have h₁ : k*d ≤ G.edgeFinset.card := independentDegree G I hInd hDeg
  have hn' : Fintype.card V ≤ t*d := dominatingDegree G D hD
  have hEdge := hT.card_edgeFinset
  have hkt : k < t := by
    by_cases hb : t ≤ k
    · have hh := Nat.mul_le_mul_right d hb
      omega
    · omega
  have hmed := medianAtMostTwo G hT
  change k + (medians G).card ≤ t
  by_cases easy : k+2 ≤ t
  · omega
  have htk : t=k+1 := by omega
  have ht2 : 2 ≤ t := by
    letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨w,hw,_⟩ := hD (Classical.choice (inferInstance : Nonempty V))
    obtain ⟨z,hz,e⟩ := hD w
    have hsub : ({w,z} : Finset V) ⊆ D := by
      simp [Finset.insert_subset_iff,hw,hz]
    have hb := Finset.card_le_card hsub
    rwa [Finset.card_pair e.ne] at hb
  have hkpos : 1 ≤ k := by omega
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0 < I.card by omega)
  by_cases low : d ≤ 2
  · have hl := lowMaxUniqueMedian G hT hn D hD v hv low
    omega
  obtain ⟨hx,hout⟩ := residualBound G hT I D hD hInd hDeg
  let j := (I \ D).card
  let q := (I ∩ D).card
  have hsplit : q+j=k := Finset.card_inter_add_card_sdiff I D
  change j*(d-1) ≤ t-q-1 at hx
  have hj : j = 0 := by
    have h3 : 2 ≤ d-1 := by omega
    have hlo := Nat.mul_le_mul_left j h3
    rw [Nat.mul_comm j 2] at hlo
    omega
  have hq : t-q=1 := by omega
  have leavesOut (u : V) (hu : u ∉ D) : G.degree u = 1 := by
    have he := hout u hu
    change G.degree u ≤ t-q at he
    have hge := minDegreePositive G D hD u
    omega
  have medianInD (u : V) (hu : u ∈ medians G) : u ∈ D := by
    by_cases ho : u ∈ D
    · exact ho
    · obtain ⟨w,_,e⟩ := hD u
      exact False.elim (leafNotMedian G hT hn e.symm (leavesOut u ho) hu)
  have hCard : (D \ I).card = 1 := by
    have hh := Finset.card_inter_add_card_sdiff D I
    rw [Finset.inter_comm] at hh
    change q + (D \ I).card = t at hh
    omega
  obtain ⟨z,hZ⟩ := Finset.card_eq_one.mp hCard
  have hZD : z ∈ D :=
    (Finset.mem_sdiff.mp (by rw [hZ]; exact Finset.mem_singleton_self z)).1
  have classify (w : V) (hw : w ∈ D) : w ∈ I ∨ w=z := by
    by_cases he : w ∈ I
    · exact Or.inl he
    · have h' := Finset.mem_sdiff.mpr ⟨hw,he⟩
      rw [hZ,Finset.mem_singleton] at h'
      exact Or.inr h'
  have incident (w : V) (hw : w ∈ I) : G.Adj w z := by
    obtain ⟨u,hu,huE⟩ := hD w
    rcases classify u hu with huI | eq
    · exact False.elim (hInd w hw u huI huE.ne huE)
    · simpa [eq] using huE
  have allOtherLeaves (w : V) (hw : w ∈ I) (u : V) (hne : u ≠ z)
      (e : G.Adj w u) : G.degree u = 1 := by
    apply leavesOut
    intro h
    rcases classify u h with huI | eq
    · exact hInd w hw u huI e.ne e
    · exact hne eq
  have branchSize (w : V) (hw : w ∈ I) : (branch G z w).card = d := by
    rw [branchLeaves G hT (incident w hw).symm (allOtherLeaves w hw), hDeg w hw]
  by_cases h2 : 2 ≤ k
  · have hnHalf : 2*d < Fintype.card V := by
      have hh := Nat.mul_le_mul_right d h2
      omega
    have dominated (u : V) (hu : u ∈ I) : u ∉ medians G := by
      intro hm
      have hbr := branchDiff G hT (incident u hu).symm
      rw [branchSize u hu] at hbr
      have hsum := (medians_exact G u).mp hm z
      omega
    have hs : medians G ⊆ ({z} : Finset V) := by
      intro w hw
      rcases classify w (medianInD w hw) with hI' | eq
      · exact False.elim ((dominated w hI') hw)
      · exact Finset.mem_singleton.mpr eq
    have hp : (medians G).card ≤ 1 := by simpa using Finset.card_le_card hs
    omega
  · have hIk : I.card = 1 := by omega
    obtain ⟨v',heq⟩ := Finset.card_eq_one.mp hIk
    have vv : v=v' := by
      rw [heq,Finset.mem_singleton] at hv
      exact hv
    subst v'
    have e := incident v hv
    have zDegree : G.degree z < d := by
      have hz := ((isolatedMaxExact G v).mp hv).2 z e
      have hle := G.degree_le_maxDegree z
      omega
    have zOther (w : V) (hw : w≠v) (f : G.Adj z w) : G.degree w=1 := by
      apply leavesOut
      intro hmem
      rcases classify w hmem with hi' | eq
      · rw [heq,Finset.mem_singleton] at hi'
        exact hw hi'
      · exact f.ne eq.symm
    have zB := branchLeaves G hT e zOther
    have hVZ := branchDiff G hT e
    have hZV := branchDiff G hT e.symm
    rw [zB] at hVZ
    rw [branchSize v hv] at hZV
    have zNot : z ∉ medians G := by
      intro hz
      have hmed := (medians_exact G z).mp hz v
      omega
    have hs : medians G ⊆ ({v} : Finset V) := by
      intro w hw
      rcases classify w (medianInD w hw) with h' | eq
      · rwa [heq] at h'
      · exact False.elim (zNot (eq ▸ hw))
    have hp : (medians G).card ≤ 1 := by simpa using Finset.card_le_card hs
    omega

/-- Graffiti.pc #376. The two counts are the isolated vertices of the
induced maximum-degree set, and the vertices of minimum total distance. -/
theorem conjecture376 (hT : G.IsTree) (hn : 2 < Fintype.card V) :
    (isolatedMax G).card + (medians G).card ≤ totalDomination G := by
  obtain ⟨D,hD,he⟩ := minDomExists G hT hn
  rw [← he]
  exact bound376 G hT hn D hD

#print axioms conjecture376
end Graffiti376
