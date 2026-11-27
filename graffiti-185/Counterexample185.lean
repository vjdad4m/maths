import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A 22-vertex counterexample to Written on the Wall II #185. -/

namespace Graffiti185

open SimpleGraph Finset
open scoped BigOperators
noncomputable section

variable {V : Type*} [Fintype V]

def square (G : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ G.dist x y ≤ 2
  symm := fun x y h => ⟨h.1.symm, (G.dist_comm (u := x) (v := y)) ▸ h.2⟩
  loopless := fun _ h => h.1 rfl


def squareMaxDegree (G : SimpleGraph V) : ℕ := by
  classical
  exact (square G).maxDegree

def squareNeighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact (square G).neighborFinset v

def maxLeaves (G : SimpleGraph V) : ℕ := by
  classical
  exact sSup {k | ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧
    (univ.filter (fun v => T.degree v = 1)).card = k}

def bipartiteNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact (univ.powerset.filter (fun s : Finset V =>
    ∃ c : s → Bool, ∀ a b : s, G.Adj a.val b.val → c a ≠ c b)).sup Finset.card

/-- Sum of distances over all ordered pairs of the given set. Diagonals have
distance zero, so the sum is unchanged by dropping them. -/
def pairSum (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ∑ x ∈ S, ∑ y ∈ S, G.dist x y

def distinctPairs (V : Type*) [Fintype V] : Finset (V × V) := by
  classical
  exact (univ : Finset V).offDiag

def averageDistance (G : SimpleGraph V) : ℚ :=
  (pairSum G univ : ℚ) / (distinctPairs V).card

def Claim185 (G : SimpleGraph V) : Prop :=
  (squareMaxDegree G : ℚ) + 2 * averageDistance (square G) ≤
    (maxLeaves G : ℚ) + (bipartiteNumber G : ℚ)

theorem distinctPairs_card (V : Type*) [Fintype V] :
    (distinctPairs V).card = Fintype.card V * (Fintype.card V - 1) := by
  classical
  rw [distinctPairs, offDiag_card, card_univ, Nat.mul_sub, Nat.mul_one]

theorem pairSum_eq_distinct_sum (G : SimpleGraph V) :
    pairSum G univ = ∑ p ∈ distinctPairs V, G.dist p.1 p.2 := by
  classical
  unfold pairSum
  rw [← Finset.sum_product (f := fun p : V × V => G.dist p.1 p.2)]
  apply Eq.symm
  apply sum_subset
  · intro p hp
    simp
  · intro ⟨x,y⟩ _ hy
    have hxy : x = y := by simpa [distinctPairs, Finset.mem_offDiag] using hy
    simp [hxy, dist_self]

theorem claim185_cross_multiply {G : SimpleGraph V} [Nontrivial V] :
    Claim185 G ↔
      squareMaxDegree G * (distinctPairs V).card + 2 * pairSum (square G) univ ≤
        (maxLeaves G + bipartiteNumber G) * (distinctPairs V).card := by
  have hp : (0 : ℚ) < ((distinctPairs V).card : ℚ) := by
    have hn : 1 < Fintype.card V := Fintype.one_lt_card
    have hpos : 0 < (distinctPairs V).card := by
      rw [distinctPairs_card]
      exact Nat.mul_pos (by omega) (by omega)
    exact_mod_cast hpos
  unfold Claim185 averageDistance
  rw [← mul_div_assoc, ← le_sub_iff_add_le', div_le_iff₀ hp, sub_mul, le_sub_iff_add_le]
  rw [add_comm, add_mul]
  norm_cast
  simp [Nat.add_mul]

end
end Graffiti185

namespace Graffiti185.Counterexample
open SimpleGraph Finset

set_option maxHeartbeats 1500000
set_option maxRecDepth 5000

abbrev V := Fin 22

def inA (x : V) : Prop := 1 ≤ x.val ∧ x.val ≤ 9
def inQ (x : V) : Prop := x.val = 0 ∨ 10 ≤ x.val ∧ x.val ≤ 15
def inP (x : V) : Prop := 16 ≤ x.val

instance (x : V) : Decidable (inA x) := inferInstanceAs (Decidable (1 ≤ x.val ∧ x.val ≤ 9))
instance (x : V) : Decidable (inQ x) := inferInstanceAs (Decidable (x.val = 0 ∨ 10 ≤ x.val ∧ x.val ≤ 15))
instance (x : V) : Decidable (inP x) := inferInstanceAs (Decidable (16 ≤ x.val))

def special (x y : V) : Prop :=
  (x.val = 0 ∧ y.val = 1) ∨ (10 ≤ x.val ∧ x.val ≤ 15 ∧ y.val = x.val + 6)

instance (x y : V) : Decidable (special x y) :=
  inferInstanceAs (Decidable ((x.val = 0 ∧ y.val = 1) ∨
    (10 ≤ x.val ∧ x.val ≤ 15 ∧ y.val = x.val + 6)))

def Adj (x y : V) : Prop :=
  x ≠ y ∧ ((inA x ∧ inA y) ∨ (inQ x ∧ inQ y) ∨ special x y ∨ special y x)

instance (x y : V) : Decidable (Adj x y) :=
  inferInstanceAs (Decidable
    (x ≠ y ∧ ((inA x ∧ inA y) ∨ (inQ x ∧ inQ y) ∨ special x y ∨ special y x)))

def G : SimpleGraph V where
  Adj := Adj
  symm := by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    rcases h.2 with h | h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  loopless := fun _ e => e.1 rfl

instance : DecidableRel G.Adj := fun x y => inferInstanceAs (Decidable (Adj x y))

lemma adj_iff (x y : V) : G.Adj x y ↔ Adj x y := Iff.rfl

lemma all_reach_root (x : V) : G.dist x 0 ≤ 2 ∧ G.Reachable x 0 := by
  by_cases hx : x = 0
  · subst x; exact ⟨by rw [SimpleGraph.dist_self]; decide,SimpleGraph.Reachable.rfl⟩
  by_cases ha : inA x
  · have h10 : G.Adj 1 0 := by decide
    by_cases h1 : x = 1
    · subst x; exact ⟨(G.dist_le h10.toWalk).trans (by simp [SimpleGraph.Adj.toWalk]),h10.reachable⟩
    have h : G.Adj x 1 := by
      change Adj x 1
      exact ⟨h1,Or.inl ⟨ha,by decide⟩⟩
    let p := SimpleGraph.Walk.cons h h10.toWalk
    exact ⟨(G.dist_le p).trans (by rfl),p.reachable⟩
  by_cases hq : inQ x
  · have h : G.Adj x 0 := by change Adj x 0; exact ⟨hx,Or.inr (Or.inl ⟨hq,by decide⟩)⟩
    exact ⟨(G.dist_le h.toWalk).trans (by simp [SimpleGraph.Adj.toWalk]),h.reachable⟩
  have hpx : 16 ≤ x.val := by
    simp only [inA,inQ] at ha hq
    have hz : x.val ≠ 0 := fun h => hx (Fin.ext h)
    omega
  let y : V := ⟨x.val-6,by have := x.isLt; omega⟩
  have hyQ : inQ y := by
    unfold inQ
    change x.val - 6 = 0 ∨ 10 ≤ x.val - 6 ∧ x.val - 6 ≤ 15
    have := x.isLt
    omega
  have hy0 : y ≠ 0 := by
    intro h
    have hh := congrArg Fin.val h
    change x.val - 6 = 0 at hh
    omega
  have hyx : y ≠ x := by
    intro h
    have hh := congrArg Fin.val h
    change x.val - 6 = x.val at hh
    omega
  have hxy : G.Adj x y := by
    change Adj x y
    refine ⟨hyx.symm,Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
    change 10 ≤ x.val-6 ∧ x.val-6 ≤ 15 ∧ x.val = x.val-6+6
    have := x.isLt
    omega
  have hyAdj : G.Adj y 0 := by
    change Adj y 0
    exact ⟨hy0,Or.inr (Or.inl ⟨hyQ,by decide⟩)⟩
  let p := SimpleGraph.Walk.cons hxy hyAdj.toWalk
  exact ⟨(G.dist_le p).trans (by rfl),p.reachable⟩

theorem connected_G : G.Connected := by
  apply (connected_iff_exists_forall_reachable _).mpr
  exact ⟨0,fun v => (all_reach_root v).2.symm⟩

def adjSquare (x y : V) : Prop := x ≠ y ∧ (G.Adj x y ∨ ∃ z : V, G.Adj x z ∧ G.Adj z y)
instance (x y : V) : Decidable (adjSquare x y) := inferInstanceAs
  (Decidable (x ≠ y ∧ (G.Adj x y ∨ ∃ z : V, G.Adj x z ∧ G.Adj z y)))

lemma square_adj_exact (x y : V) : (Graffiti185.square G).Adj x y ↔ adjSquare x y := by
  change (x ≠ y ∧ G.dist x y ≤ 2) ↔ _
  constructor
  · intro ⟨hn,hd⟩
    refine ⟨hn,?_⟩
    obtain ⟨p,hp⟩ := connected_G.exists_walk_length_eq_dist x y
    have h : p.length ≤ 2 := hp ▸ hd
    cases p with
    | nil => exact (hn rfl).elim
    | @cons _ z _ e q =>
      cases q with
      | nil => exact Or.inl e
      | @cons _ w _ f s =>
        cases s with
        | nil => exact Or.inr ⟨z,e,f⟩
        | cons _ _ => simp only [SimpleGraph.Walk.length_cons] at h; omega
  · rintro ⟨hn, h | ⟨z,h,h'⟩⟩
    · exact ⟨hn,(G.dist_le h.toWalk).trans (by simp [SimpleGraph.Adj.toWalk])⟩
    · exact ⟨hn,(G.dist_le (SimpleGraph.Walk.cons h h'.toWalk)).trans (by rfl)⟩

#print axioms square_adj_exact
end Graffiti185.Counterexample

namespace Graffiti185.Counterexample
open SimpleGraph Finset
set_option maxHeartbeats 2200000
set_option maxRecDepth 5000

private lemma cross_T (T : SimpleGraph V) (hc : T.Connected) (P : Finset V)
    {a b : V} (ha : a ∈ P) (hb : b ∉ P) : ∃ x ∈ P, ∃ y ∉ P, T.Adj x y := by
  obtain ⟨p⟩ := hc.preconnected a b
  induction p with
  | nil => exact (hb ha).elim
  | @cons u z w e q ih =>
    by_cases hz : z ∈ P
    · exact ih hz hb
    · exact ⟨u,ha,z,hz,e⟩

private lemma degree_two_of_adj (T : SimpleGraph V) [DecidableRel T.Adj]
    {a b c : V} (h : b ≠ c) (hb : T.Adj a b) (hc : T.Adj a c) : 2 ≤ T.degree a := by
  rw [← T.card_neighborFinset_eq_degree, ← Finset.card_pair h]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact (T.mem_neighborFinset _ _).mpr hb
  · exact (T.mem_neighborFinset _ _).mpr hc

lemma forced_bridge (T : SimpleGraph V) (hT : T ≤ G) (hc : T.Connected) :
    T.Adj 0 1 := by
  let P := (univ : Finset V).filter inA
  obtain ⟨x,hx,y,hy,hxy⟩ := cross_T T hc P (a:=1) (b:=0) (by decide) (by decide)
  have ha : inA x := (mem_filter.mp hx).2
  have hn : ¬inA y := fun h => hy (mem_filter.mpr ⟨mem_univ _,h⟩)
  have hed : Adj x y := hT hxy
  have x0 : x = 1 := by
    simp only [Adj,inA,inQ,special] at hed
    simp only [inA] at ha hn
    apply Fin.ext
    omega
  have y0 : y = 0 := by
    simp only [Adj,inA,inQ,special] at hed
    simp only [inA] at ha hn
    apply Fin.ext
    omega
  exact x0 ▸ y0 ▸ hxy.symm

lemma a_internal (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T ≤ G) (hc : T.Connected) : 2 ≤ T.degree 1 := by
  let P := (univ : Finset V).filter (fun x => 2 ≤ x.val ∧ x.val ≤ 9)
  obtain ⟨x,hx,y,hy,hxy⟩ := cross_T T hc P (a:=2) (b:=0) (by decide) (by decide)
  have ha : 2 ≤ x.val ∧ x.val ≤ 9 := (mem_filter.mp hx).2
  have hn : ¬ (2 ≤ y.val ∧ y.val ≤ 9) := fun h => hy (mem_filter.mpr ⟨mem_univ _,h⟩)
  have hed : Adj x y := hT hxy
  simp only [Adj,inA,inQ,special] at hed
  have x0 : x ≠ 0 := by intro e; subst x; simp at ha
  have y1 : y = 1 := by apply Fin.ext; omega
  exact degree_two_of_adj T x0 (y1 ▸ hxy.symm) (forced_bridge T hT hc).symm

lemma root_internal (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T ≤ G) (hc : T.Connected) : 2 ≤ T.degree 0 := by
  let P : Finset V := (univ : Finset V).filter (fun x => 10 ≤ x.val)
  obtain ⟨x,hx,y,hy,hxy⟩ := cross_T T hc P (a:=10) (b:=0) (by decide) (by decide)
  have ha : 10 ≤ x.val := (mem_filter.mp hx).2
  have hn : ¬10 ≤ y.val := fun h => hy (mem_filter.mpr ⟨mem_univ _,h⟩)
  have hed : Adj x y := hT hxy
  simp only [Adj,inA,inQ,special] at hed
  have x0 : x ≠ 1 := by intro e; subst x; simp at ha
  have y0 : y = 0 := by apply Fin.ext; omega
  exact degree_two_of_adj T x0 (y0 ▸ hxy.symm) (forced_bridge T hT hc)

lemma support_internal (T : SimpleGraph V) [DecidableRel T.Adj]
    (hT : T ≤ G) (hc : T.Connected) (s : V) (hs : 10 ≤ s.val ∧ s.val ≤ 15) :
    2 ≤ T.degree s := by
  let l : V := ⟨s.val+6,by omega⟩
  have hls : l ≠ s := by
    intro e
    have hh : l.val = s.val := congrArg Fin.val e
    change s.val+6 = s.val at hh
    omega
  have hz : (0 : V) ≠ l := by
    intro e
    have hh := congrArg Fin.val e
    change 0 = s.val+6 at hh
    omega
  have hsz : (0 : V) ≠ s := by
    intro e
    have hh := congrArg Fin.val e
    change 0 = s.val at hh
    omega
  have uniq (x : V) (e : G.Adj l x) : x = s := by
    change Adj l x at e
    simp only [Adj,inA,inQ,special] at e
    change _ ∧
      (((1 ≤ s.val+6 ∧ s.val+6 ≤ 9) ∧ (1 ≤ x.val ∧ x.val ≤ 9)) ∨
       ((s.val+6 = 0 ∨ 10 ≤ s.val+6 ∧ s.val+6 ≤ 15) ∧
         (x.val = 0 ∨ 10 ≤ x.val ∧ x.val ≤ 15)) ∨
       ((s.val+6 = 0 ∧ x.val = 1) ∨ (10 ≤ s.val+6 ∧ s.val+6 ≤ 15 ∧ x.val = s.val+6+6)) ∨
       (x.val = 0 ∧ s.val+6 = 1) ∨ (10 ≤ x.val ∧ x.val ≤ 15 ∧ s.val+6 = x.val+6)) at e
    apply Fin.ext
    omega
  obtain ⟨x,hx,y,_hy,e⟩ := cross_T T hc {l} (a:=l) (b:=0) (mem_singleton_self _) (by simpa using hz)
  have hx' : x = l := mem_singleton.mp hx
  subst x
  have hy' : y = s := uniq y (hT e)
  subst y
  obtain ⟨x,hx,y,hn,e'⟩ := cross_T T hc {s,l} (a:=l) (b:=0) (by simp) (by simp [hz,hsz])
  have hx' : x = s := by
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with he | rfl
    · exact he
    · have hy' := uniq y (hT e')
      subst y
      exact (hn (by simp)).elim
  subst x
  have hly : y ≠ l := by intro eq; subst y; exact hn (by simp)
  exact degree_two_of_adj T hly e' e.symm

def mandatory (x : V) : Prop := x.val = 0 ∨ x.val = 1 ∨ 10 ≤ x.val ∧ x.val ≤ 15
instance (x : V) : Decidable (mandatory x) := inferInstanceAs
  (Decidable (x.val = 0 ∨ x.val = 1 ∨ 10 ≤ x.val ∧ x.val ≤ 15))

lemma nonmandatory_card : ((univ : Finset V).filter (fun x => ¬ mandatory x)).card = 14 := by decide

lemma leaves_upper : Graffiti185.maxLeaves G ≤ 14 := by
  classical
  unfold Graffiti185.maxLeaves
  apply csSup_le
  · obtain ⟨T,hle,hT⟩ := connected_G.exists_isTree_le
    exact ⟨_,T,hle,hT,rfl⟩
  · rintro k ⟨T,hTG,hT,rfl⟩
    rw [← nonmandatory_card]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨_, hx⟩ := mem_filter.mp hx
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    intro hm
    have hd : 2 ≤ T.degree x := by
      rcases hm with h | h | h
      · have hx0 : x = 0 := Fin.ext h
        subst x; exact root_internal T hTG hT.isConnected
      · have hx1 : x = 1 := Fin.ext h
        subst x; exact a_internal T hTG hT.isConnected
      · exact support_internal T hTG hT.isConnected x h
    omega

private lemma clique_two (S : Finset V) (U : Finset V)
    (hU : U ⊆ S) (hc : ∀ x ∈ U, ∀ y ∈ U, x ≠ y → G.Adj x y)
    (χ : S → Bool) (hs : ∀ x y : S, G.Adj x.val y.val → χ x ≠ χ y) :
    U.card ≤ 2 := by
  let φ (x : U) := χ ⟨x.val,hU x.prop⟩
  have him : Function.Injective φ := by
    intro x y he
    by_contra! hn
    have hne : x.val ≠ y.val := fun e => hn (Subtype.ext e)
    exact hs ⟨x.val,hU x.prop⟩ ⟨y.val,hU y.prop⟩ (hc _ x.prop _ y.prop hne) he
  have h := Fintype.card_le_of_injective φ him
  rw [Fintype.card_coe] at h
  exact h

lemma leaves_part_card : ((univ : Finset V).filter inP).card = 6 := by decide

lemma card_of_coloring (S : Finset V) (χ : S → Bool)
    (h : ∀ x y : S, G.Adj x.val y.val → χ x ≠ χ y) : S.card ≤ 10 := by
  classical
  let A := S.filter inA
  let Q := S.filter inQ
  let P := S.filter inP
  have dAQ : Disjoint A Q := Finset.disjoint_left.mpr (by
    intro x ha hq
    have h1 : inA x := (mem_filter.mp ha).2
    have h2 : inQ x := (mem_filter.mp hq).2
    simp only [inA,inQ] at h1 h2
    omega)
  have dP : Disjoint (A ∪ Q) P := Finset.disjoint_left.mpr (by
    intro x hx hp
    have h1 : inP x := (mem_filter.mp hp).2
    rcases mem_union.mp hx with ha | hq
    · have h2 : inA x := (mem_filter.mp ha).2
      simp only [inP,inA] at h1 h2
      omega
    · have h2 : inQ x := (mem_filter.mp hq).2
      simp only [inP,inQ] at h1 h2
      omega)
  have hu : (A ∪ Q) ∪ P = S := by
    ext x
    simp only [A,Q,P,mem_union,mem_filter]
    refine ⟨?_,?_⟩
    · rintro ((⟨h,_⟩ | ⟨h,_⟩) | ⟨h,_⟩) <;> exact h
    · intro hs
      have hc : inA x ∨ inQ x ∨ inP x := by
        simp only [inA,inQ,inP]
        omega
      rcases hc with h | h | h
      · exact Or.inl (Or.inl ⟨hs,h⟩)
      · exact Or.inl (Or.inr ⟨hs,h⟩)
      · exact Or.inr ⟨hs,h⟩
  have hA : A.card ≤ 2 := clique_two S A (filter_subset _ _)
    (fun x hx y hy hn => ⟨hn,Or.inl ⟨(mem_filter.mp hx).2,(mem_filter.mp hy).2⟩⟩) χ h
  have hQ : Q.card ≤ 2 := clique_two S Q (filter_subset _ _)
    (fun x hx y hy hn => ⟨hn,Or.inr (Or.inl ⟨(mem_filter.mp hx).2,(mem_filter.mp hy).2⟩)⟩) χ h
  have hP : P.card ≤ 6 := by
    rw [← leaves_part_card]
    apply card_le_card
    intro x hx
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩
  have ha := Finset.card_union_of_disjoint dAQ
  have hq := Finset.card_union_of_disjoint dP
  rw [hu, ha] at hq
  omega

lemma bipartite_upper : Graffiti185.bipartiteNumber G ≤ 10 := by
  classical
  unfold Graffiti185.bipartiteNumber
  apply Finset.sup_le
  intro S hS
  simp only [Finset.mem_filter] at hS
  obtain ⟨χ,hχ⟩ := hS.2
  exact card_of_coloring S χ hχ

#print axioms leaves_upper
#print axioms bipartite_upper
end Graffiti185.Counterexample

namespace Graffiti185.Counterexample
open SimpleGraph Finset
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

lemma square_root_adj (x : V) (hx : x ≠ 0) : (Graffiti185.square G).Adj x 0 :=
  ⟨hx,(all_reach_root x).1⟩

lemma square_connected_G : (Graffiti185.square G).Connected := by
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨0,?_⟩
  intro x
  by_cases hx : x = 0
  · subst x; exact SimpleGraph.Reachable.rfl
  · exact (square_root_adj x hx).symm.reachable

lemma square_all_dist_le (x y : V) : (Graffiti185.square G).dist x y ≤ 2 := by
  have h1 (z : V) : (Graffiti185.square G).dist z 0 ≤ 1 := by
    by_cases hz : z = 0
    · subst z; rw [SimpleGraph.dist_self]; decide
    · exact SimpleGraph.dist_eq_one_iff_adj.mpr (square_root_adj z hz) |>.le
  have h2 := square_connected_G.dist_triangle (u:=x) (v:=0) (w:=y)
  have hx := h1 x
  have hy := h1 y
  rw [SimpleGraph.dist_comm (u:=0) (v:=y)] at h2
  omega

def inS (x : V) : Prop := 10 ≤ x.val ∧ x.val ≤ 15
instance (x : V) : Decidable (inS x) := inferInstanceAs (Decidable (10 ≤ x.val ∧ x.val ≤ 15))

/-- Explicit interval model of adjacency in the square. -/
def fastSq (x y : V) : Prop := x ≠ y ∧
  (x.val = 0 ∨ y.val = 0 ∨ (inA x ∧ inA y) ∨ (inS x ∧ inS y) ∨
   (inS x ∧ inP y) ∨ (inP x ∧ inS y) ∨ (x.val = 1 ∧ inS y) ∨ (inS x ∧ y.val = 1))

instance (x y : V) : Decidable (fastSq x y) := inferInstanceAs (Decidable (x ≠ y ∧
  (x.val = 0 ∨ y.val = 0 ∨ (inA x ∧ inA y) ∨ (inS x ∧ inS y) ∨
   (inS x ∧ inP y) ∨ (inP x ∧ inS y) ∨ (x.val = 1 ∧ inS y) ∨ (inS x ∧ y.val = 1))))

lemma fastSq_exact (x y : V) : (Graffiti185.square G).Adj x y ↔ fastSq x y := by
  constructor
  · intro h
    have h' := (square_adj_exact x y).mp h
    rcases h' with ⟨hn,e | ⟨z,e,e'⟩⟩
    · refine ⟨hn,?_⟩
      change Adj x y at e
      simp only [Adj,inA,inQ,special] at e
      simp only [inA,inS,inP]
      omega
    · refine ⟨hn,?_⟩
      change Adj x z at e
      change Adj z y at e'
      simp only [Adj,inA,inQ,special] at e e'
      simp only [inA,inS,inP]
      have hnv : x.val ≠ y.val := fun hh => hn (Fin.ext hh)
      omega
  · rintro ⟨hne,hx | hy | hAA | hSS | hSP | hPS | h1S | hS1⟩
    · have h : x = 0 := Fin.ext hx
      subst x; exact (square_root_adj y hne.symm).symm
    · have h : y = 0 := Fin.ext hy
      subst y; exact square_root_adj x hne
    · exact (square_adj_exact x y).mpr ⟨hne,Or.inl ⟨hne,Or.inl hAA⟩⟩
    · exact (square_adj_exact x y).mpr ⟨hne,Or.inl ⟨hne,
        Or.inr (Or.inl ⟨Or.inr hSS.1,Or.inr hSS.2⟩)⟩⟩
    · have hs : ∀ (a b : V), inS a → inP b → a ≠ b → (Graffiti185.square G).Adj a b := by
        intro a b ha hb hne
        let z : V := ⟨b.val-6,by have := b.isLt; omega⟩
        have hz : inS z := by unfold inS; change 10 ≤ b.val-6 ∧ b.val-6 ≤ 15; unfold inP at hb; have := b.isLt; omega
        have hzb : G.Adj z b := by
          change Adj z b
          refine ⟨?_,Or.inr (Or.inr (Or.inl (Or.inr ?_)))⟩
          · intro eq
            have he := congrArg Fin.val eq
            change b.val-6 = b.val at he
            unfold inP at hb
            omega
          · have hzv : z.val = b.val-6 := rfl
            unfold inP at hb
            change 10 ≤ z.val ∧ z.val ≤ 15 at hz
            exact ⟨hz.1,hz.2,by omega⟩
        apply (square_adj_exact a b).mpr
        refine ⟨hne,?_⟩
        by_cases az : a = z
        · exact Or.inl (az.symm ▸ hzb)
        · exact Or.inr ⟨z,⟨az,Or.inr (Or.inl ⟨Or.inr ha,Or.inr hz⟩)⟩,hzb⟩
      exact hs x y hSP.1 hSP.2 hne
    · have hs : ∀ (a b : V), inS a → inP b → a ≠ b → adjSquare a b := by
        intro a b ha hb hab
        let z : V := ⟨b.val-6,by have := b.isLt; omega⟩
        have hz : inS z := by unfold inS; change 10 ≤ b.val-6 ∧ b.val-6 ≤ 15; unfold inP at hb; have := b.isLt; omega
        have hzb : G.Adj z b := by
          change Adj z b
          refine ⟨?_,Or.inr (Or.inr (Or.inl (Or.inr ?_)))⟩
          · intro eq
            have he := congrArg Fin.val eq
            change b.val-6 = b.val at he
            unfold inP at hb
            omega
          · have hzv : z.val = b.val-6 := rfl
            unfold inP at hb
            exact ⟨hz.1,hz.2,by omega⟩
        refine ⟨hab,?_⟩
        by_cases az : a = z
        · exact Or.inl (az.symm ▸ hzb)
        · exact Or.inr ⟨z,⟨az,Or.inr (Or.inl ⟨Or.inr ha,Or.inr hz⟩)⟩,hzb⟩
      exact ((square_adj_exact y x).mpr (hs y x hPS.2 hPS.1 hne.symm)).symm
    · obtain ⟨hx,hy⟩ := h1S
      have h : x = 1 := Fin.ext hx
      subst x
      have hy0 : (0 : V) ≠ y := by
        intro h
        subst y
        exact (show ¬inS (0:V) from by decide) hy
      exact (square_adj_exact 1 y).mpr ⟨hne,Or.inr ⟨0, by decide,
        ⟨hy0, Or.inr (Or.inl ⟨Or.inl rfl, Or.inr hy⟩)⟩⟩⟩
    · obtain ⟨hx,hy⟩ := hS1
      have h : y = 1 := Fin.ext hy
      subst y
      have hx0 : x ≠ (0 : V) := by
        intro h
        subst x
        exact (show ¬inS (0:V) from by decide) hx
      exact (square_adj_exact x 1).mpr ⟨hne,Or.inr ⟨0,
        ⟨hx0,Or.inr (Or.inl ⟨Or.inr hx,Or.inl rfl⟩)⟩,by decide⟩⟩

def numericSquareDist (x y : V) : ℕ :=
  if x = y then 0 else if fastSq x y then 1 else 2

lemma distance_model (x y : V) : (Graffiti185.square G).dist x y = numericSquareDist x y := by
  by_cases h : x = y
  · subst y; simp [numericSquareDist,SimpleGraph.dist_self]
  by_cases ha : fastSq x y
  · have hx := SimpleGraph.dist_eq_one_iff_adj.mpr ((fastSq_exact x y).mpr ha)
    simpa only [numericSquareDist,if_neg h,if_pos ha] using hx
  have h0 : (Graffiti185.square G).dist x y ≠ 0 := by
    intro h'
    exact h ((square_connected_G.dist_eq_zero_iff).mp h')
  have h1 : (Graffiti185.square G).dist x y ≠ 1 := by
    intro h'
    exact ha ((fastSq_exact x y).mp (SimpleGraph.dist_eq_one_iff_adj.mp h'))
  simp only [numericSquareDist,if_neg h,if_neg ha]
  have := square_all_dist_le x y
  omega

def rowDist (x : V) : ℕ := ∑ y : V, numericSquareDist x y

def claimedRow (x : V) : ℕ :=
  if x.val = 0 then 21 else if x.val = 1 then 27 else
    if x.val ≤ 9 then 33 else if x.val ≤ 15 then 29 else 35

lemma row_computed (x : V) : rowDist x = claimedRow x := by
  fin_cases x <;> decide

lemma pair_distance_sum : Graffiti185.pairSum (Graffiti185.square G) univ = 696 := by
  unfold Graffiti185.pairSum
  simp only [distance_model]
  change (∑ x : V, rowDist x) = 696
  simp only [row_computed]
  decide

lemma degree_lower : 21 ≤ Graffiti185.squareMaxDegree G := by
  classical
  let H := Graffiti185.square G
  have sub : ((univ : Finset V).erase 0) ⊆ H.neighborFinset 0 := by
    intro x hx
    exact (H.mem_neighborFinset _ _).mpr (square_root_adj x (mem_erase.mp hx).1).symm
  have hd := Finset.card_le_card sub
  rw [Finset.card_erase_of_mem (mem_univ _),Finset.card_univ,H.card_neighborFinset_eq_degree] at hd
  have hM := H.degree_le_maxDegree 0
  have hfin : Fintype.card V = 22 := Fintype.card_fin 22
  change 21 ≤ H.maxDegree
  omega

#print axioms pair_distance_sum
#print axioms degree_lower
end Graffiti185.Counterexample

namespace Graffiti185.Counterexample
open Finset

/-- An exact 22-vertex counterexample to Written on the Wall II conjecture 185. -/
theorem not_claim185 : ¬ Graffiti185.Claim185 G := by
  intro h
  have h' := (Graffiti185.claim185_cross_multiply (G := G)).mp h
  rw [pair_distance_sum, Graffiti185.distinctPairs_card, Fintype.card_fin] at h'
  norm_num at h'
  have ha := leaves_upper
  have hb := bipartite_upper
  have hd := degree_lower
  omega

theorem counterexample185 : ∃ H : SimpleGraph (Fin 22), H.Connected ∧ ¬ Graffiti185.Claim185 H :=
  ⟨G,connected_G,not_claim185⟩

#print axioms not_claim185
#print axioms counterexample185

end Graffiti185.Counterexample

namespace Graffiti185.Counterexample
open Finset SimpleGraph

theorem average_exact : Graffiti185.averageDistance (Graffiti185.square G) = (116 : ℚ) / 77 := by
  unfold Graffiti185.averageDistance
  rw [pair_distance_sum,Graffiti185.distinctPairs_card,Fintype.card_fin]
  norm_num

theorem degree_exact : Graffiti185.squareMaxDegree G = 21 := by
  classical
  have hi := (Graffiti185.square G).maxDegree_lt_card_verts
  have lo : 21 ≤ (Graffiti185.square G).maxDegree := degree_lower
  rw [show Fintype.card V = 22 by decide] at hi
  change (Graffiti185.square G).maxDegree = 21
  omega

#print axioms average_exact
#print axioms degree_exact
end Graffiti185.Counterexample
