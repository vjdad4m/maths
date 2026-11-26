import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Finset.Max
import Lean.Elab.Tactic.Omega

/-!
# Written on the Wall II, conjecture 326

If a connected finite simple graph on at least two vertices satisfies
3 times its matching number ≤ the number of edges induced by its
degree-two vertices, then it is well total dominated.

Take a maximum matching in the graph retaining just those induced edges.
The degree sum forces each matched vertex to have two neighbors in
this graph, exactly one of which is matched. If a matched pair had
distinct unmatched neighbors, replacing its edge by two edges would
augment the matching. Thus the pair shares a neighbor and forms a triangle.
All three have degree two in the original graph, so connectivity makes
the original graph complete. Minimal total dominating sets then have size two.

Official catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
Checked with Lean 4.19.0 and Mathlib v4.19.0.
-/

namespace Graffiti326
open Finset SimpleGraph
open scoped BigOperators
set_option linter.unusedSectionVars false
noncomputable section
variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel G.Adj

def HasMatching (G : SimpleGraph V) (k : ℕ) :=
  ∃ f : Fin k × Bool ↪ V, ∀ i, G.Adj (f (i,false)) (f (i,true))

local instance (G : SimpleGraph V) : DecidablePred (HasMatching G) := Classical.decPred _

private def feasibleMatchingSizes (G : SimpleGraph V) : Finset ℕ :=
  (range (Fintype.card V / 2+1)).filter (HasMatching G)

private theorem matchingSizes_nonempty (G : SimpleGraph V) :
    (feasibleMatchingSizes G).Nonempty := by
  use 0
  simp only [feasibleMatchingSizes, mem_filter, mem_range]
  refine ⟨by omega, ⟨⟨fun p => Fin.elim0 p.1, ?_⟩, ?_⟩⟩
  · intro p; exact Fin.elim0 p.1
  · intro i; exact Fin.elim0 i

def matchingNumber (G : SimpleGraph V) : ℕ :=
  (feasibleMatchingSizes G).max' (matchingSizes_nonempty G)

theorem matchingNumber_attained (G : SimpleGraph V) : HasMatching G (matchingNumber G) := by
  exact (Finset.mem_filter.1 (Finset.max'_mem (feasibleMatchingSizes G)
    (matchingSizes_nonempty G))).2

theorem matchingNumber_upper {G : SimpleGraph V} {k : ℕ} (hk : HasMatching G k) :
    k ≤ matchingNumber G := by
  obtain ⟨f,hf⟩ := hk
  have hk' : 2*k ≤ Fintype.card V := by
    simpa [Nat.mul_comm] using Fintype.card_le_of_injective f f.injective
  apply Finset.le_max'
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ⟨f,hf⟩⟩

def support {k : ℕ} (f : Fin k × Bool ↪ V) : Finset V :=
  univ.map f

theorem mem_support {k : ℕ} (f : Fin k × Bool ↪ V) {v : V} :
    v ∈ support f ↔ ∃ i b, f (i,b) = v := by
  simp [support, Prod.exists]

theorem support_card {k : ℕ} (f : Fin k × Bool ↪ V) : (support f).card = 2*k := by
  simp [support, Nat.mul_comm]

theorem matching_extend_support {G : SimpleGraph V} {k : ℕ} {f : Fin k × Bool ↪ V}
    (hf : ∀ i, G.Adj (f (i,false)) (f (i,true))) {x y : V}
    (hx : x ∉ support f) (hy : y ∉ support f) (ha : G.Adj x y) :
    ∃ f' : Fin (k+1) × Bool ↪ V, (∀ i, G.Adj (f' (i,false)) (f' (i,true))) ∧
      support f' ⊆ insert x (insert y (support f)) := by
  let F (i : Fin (k+1)) (b : Bool) :=
    Fin.lastCases (motive := fun _ => V) (if b then y else x) (fun j => f (j,b)) i
  have hX (i : Fin k) (b : Bool) : f (i,b) ∈ support f := (mem_support f).mpr ⟨i,b,rfl⟩
  have hfin : Function.Injective (fun p : Fin (k+1) × Bool => F p.1 p.2) := by
    rintro ⟨i,b⟩ ⟨j,c⟩ he
    change F i b = F j c at he
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j,rfl⟩ | rfl
    · simp only [F, Fin.lastCases_castSucc] at he
      obtain e := f.injective he
      cases e
      rfl
    · simp only [F, Fin.lastCases_castSucc, Fin.lastCases_last] at he
      cases c
      · change f (i,b) = x at he
        exact (hx (he ▸ hX i b)).elim
      · change f (i,b) = y at he
        exact (hy (he ▸ hX i b)).elim
    · simp only [F, Fin.lastCases_castSucc, Fin.lastCases_last] at he
      cases b
      · change x = f (j,c) at he
        exact (hx (he.symm ▸ hX j c)).elim
      · change y = f (j,c) at he
        exact (hy (he.symm ▸ hX j c)).elim
    · simp only [F, Fin.lastCases_last] at he
      cases b <;> cases c <;> simp_all [ha.ne,ha.ne.symm]
  let f' : Fin (k+1) × Bool ↪ V := ⟨fun p => F p.1 p.2,hfin⟩
  refine ⟨f', ?_, ?_⟩
  · intro i
    change G.Adj (F i false) (F i true)
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩ | rfl
    · simpa [F] using hf i
    · simpa [F] using ha
  · intro z hz
    obtain ⟨i,b,rfl⟩ := (mem_support f').mp hz
    change F i b ∈ _
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i,rfl⟩ | rfl
    · simp only [F, Fin.lastCases_castSucc]
      exact mem_insert_of_mem (mem_insert_of_mem (hX i b))
    · cases b <;> simp [F]

theorem matching_extend {G : SimpleGraph V} {k : ℕ} {f : Fin k × Bool ↪ V}
    (hf : ∀ i, G.Adj (f (i,false)) (f (i,true))) {x y : V}
    (hx : x ∉ support f) (hy : y ∉ support f) (ha : G.Adj x y) :
    HasMatching G (k+1) := by
  obtain ⟨f',hf',_⟩ := matching_extend_support hf hx hy ha
  exact ⟨f',hf'⟩

private theorem no_edges_outside {G : SimpleGraph V}
    {f : Fin (matchingNumber G) × Bool ↪ V}
    (hf : ∀ i, G.Adj (f (i,false)) (f (i,true))) {x y : V}
    (hx : x ∉ support f) (hy : y ∉ support f) : ¬ G.Adj x y := by
  intro h
  have h' := matchingNumber_upper (matching_extend hf hx hy h)
  omega

def degTwoGraph (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ G.degree u = 2 ∧ G.degree v = 2
  symm _ _ h := ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless _ h := h.1.ne rfl

/-- The spanning representation retains exactly the edge set induced by
the degree-two vertices; isolates outside that set add no edges. -/
theorem mem_degTwoGraph_edges (G : SimpleGraph V) (u v : V) :
    s(u,v) ∈ (degTwoGraph G).edgeFinset ↔
      G.Adj u v ∧ G.degree u = 2 ∧ G.degree v = 2 := by
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  rfl

theorem degTwoGraph_le (G : SimpleGraph V) : degTwoGraph G ≤ G := fun _ _ h => h.1

theorem degTwoGraph_degree (G : SimpleGraph V) (v : V) : (degTwoGraph G).degree v ≤ 2 := by
  by_cases hd : G.degree v = 2
  · exact ((degTwoGraph G).degree_le_of_le (degTwoGraph_le G)).trans_eq hd
  · have h0 : ¬ ∃ w, (degTwoGraph G).Adj v w := fun ⟨_,h⟩ => hd h.2.1
    have hp := not_congr ((degTwoGraph G).degree_pos_iff_exists_adj v)
    have hz := hp.mpr h0
    omega


def degIn (H : SimpleGraph V) (X : Finset V) (v : V) : ℕ :=
  (X.filter (H.Adj v)).card

private theorem degree_parts (H : SimpleGraph V) (X : Finset V) (v : V) :
    H.degree v = degIn H X v + degIn H (univ \ X) v := by
  have eq₁ : (H.neighborFinset v).filter (· ∈ X) = X.filter (H.Adj v) := by
    ext w
    simp only [mem_filter,mem_neighborFinset]
    exact and_comm
  have eq₂ : (H.neighborFinset v).filter (· ∉ X) = (univ \ X).filter (H.Adj v) := by
    ext w
    simp only [mem_filter,mem_neighborFinset,mem_sdiff,mem_univ,true_and]
    exact and_comm
  have h := filter_card_add_filter_neg_card_eq_card (s := H.neighborFinset v)
    (p := (· ∈ X))
  rw [eq₁,eq₂,card_neighborFinset_eq_degree] at h
  exact h.symm

private theorem cross_degree (H : SimpleGraph V) (X Y : Finset V) :
    ∑ v ∈ X, degIn H Y v = ∑ w ∈ Y, degIn H X w := by
  simp only [degIn,Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : H.Adj a b
  · simp [h,h.symm]
  · have h' : ¬ H.Adj b a := fun e => h e.symm
    simp [h,h']

private theorem matching_internal_one {H : SimpleGraph V} {k : ℕ}
    {f : Fin k × Bool ↪ V} (hf : ∀ i, H.Adj (f (i,false)) (f (i,true)))
    (v : V) (hv : v ∈ support f) : 1 ≤ degIn H (support f) v := by
  obtain ⟨i,b,rfl⟩ := (mem_support f).mp hv
  apply Nat.succ_le_of_lt
  apply Finset.card_pos.mpr
  cases b
  · exact ⟨f (i,true),mem_filter.mpr ⟨(mem_support f).mpr ⟨i,true,rfl⟩,hf i⟩⟩
  · exact ⟨f (i,false),mem_filter.mpr ⟨(mem_support f).mpr ⟨i,false,rfl⟩,(hf i).symm⟩⟩

private theorem extremal_matching_saturated {H : SimpleGraph V}
    (hdeg : ∀ v, H.degree v ≤ 2)
    {f : Fin (matchingNumber H) × Bool ↪ V}
    (hf : ∀ i, H.Adj (f (i,false)) (f (i,true)))
    (hbudget : 3 * matchingNumber H ≤ H.edgeFinset.card) :
    ∀ v ∈ support f, H.degree v = 2 ∧ degIn H (support f) v = 1 := by
  let X := support f
  let Y := univ \ X
  have hpart : Disjoint X Y := by
    apply disjoint_left.mpr
    exact fun v h₁ h₂ => (mem_sdiff.mp h₂).2 h₁
  have hu : X ∪ Y = univ := by
    ext v
    simp [Y,mem_union]
  have hy0 (v : V) (hv : v ∈ Y) : degIn H Y v = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro h
    obtain ⟨u,hu,ha⟩ := (Finset.card_pos.mp h).imp (fun _ hw => mem_filter.mp hw)
    exact no_edges_outside hf (mem_sdiff.mp hv).2 (mem_sdiff.mp hu).2 ha
  have hyn (v : V) (hv : v ∈ Y) : H.degree v = degIn H X v := by
    rw [degree_parts H X v, ← show Y = univ \ X from rfl, hy0 v hv, Nat.add_zero]
  have point (v : V) : H.degree v = degIn H X v + degIn H Y v := degree_parts H X v
  have hsum := H.sum_degrees_eq_twice_card_edges
  rw [← hu, sum_union hpart] at hsum
  have hp : ∑ v ∈ Y, H.degree v = ∑ v ∈ Y, degIn H X v :=
    sum_congr rfl hyn
  rw [hp,← cross_degree H X Y] at hsum
  have hsplit : ∑ v ∈ X, H.degree v =
      (∑ v ∈ X, degIn H X v) + ∑ v ∈ X, degIn H Y v := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun v _ => point v)
  have hd : ∑ v ∈ X, H.degree v ≤ 2*X.card := by
    have h := sum_le_sum (s := X) (fun v _ => hdeg v)
    simpa [Nat.mul_comm] using h
  have hint : X.card ≤ ∑ v ∈ X, degIn H X v := by
    simpa using sum_le_sum (s := X) (fun v hv => matching_internal_one hf v hv)
  have hx : X.card = 2*matchingNumber H := support_card f
  have hdeq : ∑ v ∈ X, H.degree v = 2*X.card := by omega
  have hieq : ∑ v ∈ X, degIn H X v = X.card := by omega
  intro v hv
  constructor
  · by_contra hn
    have huu := hdeg v
    have hlt : H.degree v < 2 := by omega
    have hh := Finset.sum_lt_sum (s := X) (fun u _ => hdeg u) ⟨v,hv,hlt⟩
    have hh' : ∑ v ∈ X, H.degree v < 2*X.card := by simpa [Nat.mul_comm] using hh
    omega
  · by_contra hn
    have huu : 1 ≤ degIn H X v := matching_internal_one hf v hv
    change ¬ degIn H X v = 1 at hn
    have hlt : 1 < degIn H X v := by omega
    have hh := Finset.sum_lt_sum (s := X) (fun u hu => matching_internal_one hf u hu) ⟨v,hv,hlt⟩
    have hh' : X.card < ∑ v ∈ X, degIn H X v := by simpa using hh
    omega

private theorem augment {H : SimpleGraph V} {k : ℕ}
    {f : Fin (k+1) × Bool ↪ V} (hf : ∀ i, H.Adj (f (i,false)) (f (i,true)))
    (i : Fin (k+1)) {x y : V} (hx : x ∉ support f) (hy : y ∉ support f)
    (hxy : x ≠ y) (h₁ : H.Adj (f (i,false)) x) (h₂ : H.Adj (f (i,true)) y) :
    HasMatching H ((k+1)+1) := by
  let f₀ : Fin k × Bool ↪ V := ⟨fun p => f (i.succAbove p.1,p.2), by
    rintro ⟨j,b⟩ ⟨j',b'⟩ h
    have hh := f.injective h
    have h₁ := Fin.succAbove_right_injective (p := i) (congrArg Prod.fst hh)
    have h₂ := congrArg Prod.snd hh
    cases h₁
    cases h₂
    rfl⟩
  have hf₀ (j : Fin k) : H.Adj (f₀ (j,false)) (f₀ (j,true)) := hf (i.succAbove j)
  have hs : support f₀ ⊆ support f := by
    intro z hz
    obtain ⟨j,b,rfl⟩ := (mem_support f₀).mp hz
    exact (mem_support f).mpr ⟨i.succAbove j,b,rfl⟩
  have hNo (b : Bool) : f (i,b) ∉ support f₀ := by
    intro h
    obtain ⟨j,b',hh⟩ := (mem_support f₀).mp h
    have ee := congrArg Prod.fst (f.injective hh)
    exact Fin.succAbove_ne _ _ ee
  obtain ⟨f₁,hf₁,hs₁⟩ := matching_extend_support hf₀ (hNo false) (fun h => hx (hs h)) h₁
  have hu : f (i,true) ∉ support f₁ := by
    intro h
    have hh := hs₁ h
    simp only [mem_insert] at hh
    rcases hh with h | h | h
    · exact (hf i).ne h.symm
    · exact hx (h ▸ (mem_support f).mpr ⟨i,true,rfl⟩)
    · exact hNo true h
  have hY : y ∉ support f₁ := by
    intro h
    have hh := hs₁ h
    simp only [mem_insert] at hh
    rcases hh with h | h | h
    · exact hy (h.symm ▸ (mem_support f).mpr ⟨i,false,rfl⟩)
    · exact hxy h.symm
    · exact hy (hs h)
  exact matching_extend hf₁ hu hY h₂

private theorem no_long_augment {H : SimpleGraph V} {k : ℕ} {f : Fin k × Bool ↪ V}
    (hk : k = matchingNumber H) (hf : ∀ i, H.Adj (f (i,false)) (f (i,true)))
    (i : Fin k) {x y : V} (hx : x ∉ support f) (hy : y ∉ support f)
    (h₁ : H.Adj (f (i,false)) x) (h₂ : H.Adj (f (i,true)) y) : x = y := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ k =>
    by_contra hne
    have h := matchingNumber_upper (augment hf i hx hy hne h₁ h₂)
    omega


private theorem one_le_matching_of_adj {H : SimpleGraph V} {x y : V} (h : H.Adj x y) :
    1 ≤ matchingNumber H := by
  apply matchingNumber_upper
  let f (p : Fin 1 × Bool) := if p.2 then y else x
  have hi : Function.Injective f := by
    rintro ⟨i,b⟩ ⟨j,c⟩ he
    have hij : i=j := Subsingleton.elim _ _
    subst j
    cases b <;> cases c <;> simp_all [f,h.ne,h.ne.symm]
  exact ⟨⟨f,hi⟩,fun _ => by simpa [f] using h⟩

private theorem outside_neighbor {H : SimpleGraph V} (X : Finset V) (v : V)
    (hd : H.degree v = 2) (hi : degIn H X v = 1) : ∃ u, u ∉ X ∧ H.Adj v u := by
  have hpart := degree_parts H X v
  have h : 0 < degIn H (univ \ X) v := by omega
  obtain ⟨u,hu⟩ := Finset.card_pos.mp h
  obtain ⟨hu,had⟩ := mem_filter.mp hu
  exact ⟨u,(mem_sdiff.mp hu).2,had⟩

private theorem two_neighbors_exact {G : SimpleGraph V} {x a b : V}
    (hd : G.degree x = 2) (ha : G.Adj x a) (hb : G.Adj x b) (hab : a≠b) :
    ∀ u, G.Adj x u → u=a ∨ u=b := by
  have hs : ({a,b} : Finset V) ⊆ G.neighborFinset x := by
    intro u hu
    simp only [mem_insert,mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact (G.mem_neighborFinset _ _).mpr ha
    · exact (G.mem_neighborFinset _ _).mpr hb
  have he := Finset.eq_of_subset_of_card_le hs (by simp [hab,hd])
  intro u hu
  have hv := (G.mem_neighborFinset _ _).mpr hu
  rw [← he] at hv
  simpa using hv

private theorem closed_set_of_connected {G : SimpleGraph V} (hc : G.Connected)
    (S : Set V) {r : V} (hr : r ∈ S)
    (hclose : ∀ a ∈ S, ∀ b, G.Adj a b → b ∈ S) :
    ∀ v, v ∈ S := by
  intro v
  obtain ⟨p⟩ := hc r v
  have aux : ∀ {a b : V}, G.Walk a b → a ∈ S → b ∈ S := by
    intro a b p ha
    induction p with
    | nil => exact ha
    | cons had q ih => exact ih (hclose _ ha _ had)
  exact aux p hr

private theorem complete_of_closed_triangle {G : SimpleGraph V} (hc : G.Connected)
    {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hda : G.degree a = 2) (hdb : G.degree b = 2) (hdc : G.degree c = 2) :
    ∀ x y, x ≠ y → G.Adj x y := by
  let S : Set V := {a,b,c}
  have hcover : ∀ v, v ∈ S := by
    apply closed_set_of_connected hc S (r := a) (by simp [S])
    intro u hu v hv
    simp only [S,Set.mem_insert_iff,Set.mem_singleton_iff] at hu ⊢
    rcases hu with rfl | rfl | rfl
    · rcases two_neighbors_exact hda hab hac hbc.ne v hv with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rcases two_neighbors_exact hdb hab.symm hbc hac.ne v hv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rcases two_neighbors_exact hdc hac.symm hbc.symm hab.ne v hv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  intro x y h
  have hx := hcover x
  have hy := hcover y
  simp only [S,Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact (h rfl).elim
  · exact hab
  · exact hac
  · exact hab.symm
  · exact (h rfl).elim
  · exact hbc
  · exact hac.symm
  · exact hbc.symm
  · exact (h rfl).elim

private theorem complete_of_budget {G : SimpleGraph V} (hc : G.Connected)
    (hn : 2 ≤ Fintype.card V) (hbudget : 3*matchingNumber G ≤ (degTwoGraph G).edgeFinset.card) :
    ∀ x y, x ≠ y → G.Adj x y := by
  let H := degTwoGraph G
  have hs : matchingNumber H ≤ matchingNumber G := by
    obtain ⟨f,hf⟩ := matchingNumber_attained H
    exact matchingNumber_upper ⟨f,fun i => degTwoGraph_le G (hf i)⟩
  haveI : Nonempty V := hc.nonempty
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨w,hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
  have had : ∃ u, G.Adj v u := by
    obtain ⟨p⟩ := hc v w
    cases p with
    | nil => exact (hw rfl).elim
    | cons ha _ => exact ⟨_,ha⟩
  obtain ⟨u,hu⟩ := had
  have hpos := one_le_matching_of_adj hu
  have hHpos : 0 < H.edgeFinset.card := by change 0 < (degTwoGraph G).edgeFinset.card; omega
  obtain ⟨e,he⟩ := Finset.card_pos.mp hHpos
  have hHE : ∃ x y, H.Adj x y := by
    induction e using Sym2.inductionOn with
    | _ x y => exact ⟨x,y, (SimpleGraph.mem_edgeFinset.mp he)⟩
  obtain ⟨x,y,hxy⟩ := hHE
  have hm := one_le_matching_of_adj hxy
  obtain ⟨f,hf⟩ := matchingNumber_attained H
  have i : Fin (matchingNumber H) := ⟨0,by omega⟩
  have hh : 3 * matchingNumber H ≤ H.edgeFinset.card := Nat.le_trans (Nat.mul_le_mul_left 3 hs) hbudget
  have hsat := extremal_matching_saturated (degTwoGraph_degree G) hf hh
  let a := f (i,false)
  let b := f (i,true)
  have hab : H.Adj a b := hf i
  have ha := hsat a ((mem_support f).mpr ⟨i,false,rfl⟩)
  have hb := hsat b ((mem_support f).mpr ⟨i,true,rfl⟩)
  obtain ⟨c,hcX,hac⟩ := outside_neighbor (support f) a ha.1 ha.2
  obtain ⟨d,hdX,hbd⟩ := outside_neighbor (support f) b hb.1 hb.2
  have he := no_long_augment rfl hf i hcX hdX hac hbd
  rw [← he] at hbd
  exact complete_of_closed_triangle hc hab.1 hac.1 hbd.1 hab.2.1 hab.2.2 hac.2.2

def TotalDominates (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ u ∈ D, G.Adj v u

def WellTotalDominated (G : SimpleGraph V) : Prop :=
  ∀ D, TotalDominates G D → (∀ E ⊆ D, TotalDominates G E → D ⊆ E) →
     ∀ E, TotalDominates G E → D.card ≤ E.card

private theorem complete_well_total_dominated {G : SimpleGraph V} [Nonempty V]
    (hG : ∀ x y, x ≠ y → G.Adj x y) : WellTotalDominated G := by
  intro D hd hm E hE
  have large (S : Finset V) (h : TotalDominates G S) :
      ∃ a ∈ S, ∃ b ∈ S, a ≠ b := by
    let v : V := Classical.choice ‹Nonempty V›
    obtain ⟨a,ha,_⟩ := h v
    obtain ⟨b,hb,he⟩ := h a
    exact ⟨a,ha,b,hb,he.ne⟩
  obtain ⟨a,ha,b,hb,hab⟩ := large D hd
  let F : Finset V := {a,b}
  have hF : F ⊆ D := by
    intro v hv
    simp only [F,mem_insert,mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact ha
    · exact hb
  have htd : TotalDominates G F := by
    intro v
    by_cases he : v=a
    · exact ⟨b,by simp [F],hG v b (he ▸ hab)⟩
    · exact ⟨a,by simp [F],hG v a he⟩
  have hD : D.card ≤ 2 := by simpa [F,hab] using card_le_card (hm F hF htd)
  have h₂ := Finset.one_lt_card.mpr (large E hE)
  omega

theorem conjecture326 (G : SimpleGraph V) (hc : G.Connected) (hn : 2 ≤ Fintype.card V)
    (hbudget : 3 * matchingNumber G ≤ (degTwoGraph G).edgeFinset.card) :
    WellTotalDominated G := by
  haveI : Nonempty V := hc.nonempty
  exact complete_well_total_dominated (complete_of_budget hc hn hbudget)

#print axioms conjecture326

#print axioms no_edges_outside
#print axioms degTwoGraph_degree
end
end Graffiti326
