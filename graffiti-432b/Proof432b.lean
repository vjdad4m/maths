import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Lattice
import Lean.Elab.Tactic.Omega

namespace GraffitiPendant
open Finset SimpleGraph
open Classical
noncomputable section
variable {V : Type*} (G : SimpleGraph V)

def Pendant (x : V) : Prop := ∃! y, G.Adj x y

def Support (s : V) : Prop := ∃ l, Pendant G l ∧ G.Adj l s

def Dominates (D : Finset V) : Prop := ∀ x, x ∈ D ∨ ∃ y ∈ D, G.Adj x y

variable [Fintype V]

def outsideSupports : Finset V := univ.filter (fun x => ¬Support G x)

@[simp] theorem mem_outside {x : V} : x ∈ outsideSupports G ↔ ¬Support G x := by
  simp [outsideSupports]

/-- Connectedness rules out a component consisting of a single isolated edge. -/
theorem pendant_not_support (h : G.Connected) (hn : 2 < Fintype.card V)
    {v : V} (pv : Pendant G v) : ¬Support G v := by
  classical
  rintro ⟨l,pl,lv⟩
  have closed : ∀ x, x = v ∨ x = l := by
    intro x
    have r := (G.reachable_iff_reflTransGen v x).mp (h v x)
    induction r with
    | refl => exact Or.inl rfl
    | tail _ e ih =>
      rcases ih with rfl | rfl
      · exact Or.inr (pv.unique e lv.symm)
      · exact Or.inl (pl.unique e lv)
  have sub : (univ : Finset V) ⊆ {v,l} := by
    intro x _
    simpa using closed x
  have bound := card_le_card sub
  have pair := card_insert_le v ({l} : Finset V)
  simp only [card_univ,card_singleton] at bound pair
  omega

end
end GraffitiPendant

/-! Ermelinda DeLaVina, Written on the Wall II, Graffiti.pc #432b (December 8, 2010). -/
namespace Graffiti432b
open GraffitiPendant Finset SimpleGraph
open Classical
noncomputable section
variable {V : Type*} (G : SimpleGraph V)

def Independent (A : Finset V) : Prop := ∀ a ∈ A, ∀ b ∈ A, ¬G.Adj a b

def independentDomination : ℕ :=
  sInf {n | ∃ D : Finset V, Independent G D ∧ Dominates G D ∧ D.card = n}

def Bipartite : Prop := ∃ c : V → Bool, ∀ u v, G.Adj u v → c u ≠ c v

def bipartiteIndicator : ℤ := if Bipartite G then 1 else 0

private theorem number_le {A : Finset V} (ind : Independent G A) (dom : Dominates G A) :
    independentDomination G ≤ A.card := Nat.sInf_le ⟨A,ind,dom,rfl⟩

variable [Fintype V]

def evenSide (v : V) : Finset V := univ.filter (fun w => G.dist v w % 2 = 0)
def oddSide (v : V) : Finset V := univ.filter (fun w => G.dist v w % 2 = 1)

def difference (v : V) : ℤ := ((evenSide G v).card : ℤ) - (oddSide G v).card

def minimumDifference [Nonempty V] : ℤ :=
  (univ.image (difference G)).min' (univ_nonempty.image _)

private theorem exists_independent_dominating : ∃ A : Finset V, Independent G A ∧ Dominates G A := by
  classical
  let family := univ.filter (Independent G)
  have empty : Independent G ∅ := by simp [Independent]
  obtain ⟨A,ha,maximal⟩ := exists_max_image family card
    ⟨∅,mem_filter.mpr ⟨mem_univ _,empty⟩⟩
  have ind := (mem_filter.mp ha).2
  refine ⟨A,ind,fun x => ?_⟩
  by_contra! bad
  have larger : Independent G (insert x A) := by
    intro a ha b hb
    rcases mem_insert.mp ha with rfl | ma <;> rcases mem_insert.mp hb with rfl | mb
    · exact G.loopless _
    · exact bad.2 _ mb
    · exact fun e => bad.2 _ ma e.symm
    · exact ind _ ma _ mb
  have bound := maximal _ (mem_filter.mpr ⟨mem_univ _,larger⟩)
  simp [card_insert_of_not_mem bad.1] at bound

/-- Replace each support in an independent set by one of its pendant neighbors. -/
private theorem independent_card_bound (h : G.Connected) (hn : 2 < Fintype.card V)
    {A : Finset V} (ind : Independent G A) : A.card ≤ (outsideSupports G).card := by
  classical
  let f := fun a => if s : Support G a then s.choose else a
  have maps (a : V) : f a ∈ outsideSupports G := by
    apply (mem_outside G).mpr
    by_cases s : Support G a
    · simpa [f,s] using pendant_not_support G h hn s.choose_spec.1
    · simp [f,s]
  apply card_le_card_of_injOn f (fun a _ => maps a)
  intro a ha b hb eq
  by_cases sa : Support G a <;> by_cases sb : Support G b
  · simp only [f,dif_pos sa,dif_pos sb] at eq
    exact sa.choose_spec.1.unique sa.choose_spec.2 (eq ▸ sb.choose_spec.2)
  · simp only [f,dif_pos sa,dif_neg sb] at eq
    exact (ind b hb a ha (eq ▸ sa.choose_spec.2)).elim
  · simp only [f,dif_neg sa,dif_pos sb] at eq
    exact (ind a ha b hb (eq ▸ sb.choose_spec.2)).elim
  · simpa only [f,dif_neg sa,dif_neg sb] using eq

private theorem same_other_color {a b c : Bool} (ab : a ≠ b) (ac : a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

private theorem step_parity (a m b : Bool) (n : ℕ) (am : a ≠ m)
    (ih : n % 2 = 0 ↔ m = b) : (n + 1) % 2 = 0 ↔ a = b := by
  cases a <;> cases m <;> cases b <;> simp_all <;> omega

omit [Fintype V] in
private theorem walk_parity {c : V → Bool} (proper : ∀ a b, G.Adj a b → c a ≠ c b)
    {a b : V} (p : G.Walk a b) :
    (p.length % 2 = 0 ↔ c a = c b) := by
  induction p with
  | nil => simp
  | @cons a m b e p ih =>
    exact step_parity _ _ _ _ (proper a m e) ih

private theorem parity_bound [Nontrivial V] (h : G.Connected) (hn : 2 < Fintype.card V)
    (bip : Bipartite G) (v : V) :
    (independentDomination G : ℤ) ≤ (outsideSupports G).card + difference G v := by
  classical
  obtain ⟨c,proper⟩ := bip
  have par (w : V) : G.dist v w % 2 = 0 ↔ c v = c w := by
    obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist v w
    rw [← hp]
    exact walk_parity G proper p
  have evenMem (w : V) : w ∈ evenSide G v ↔ c v = c w := by simp [evenSide,par]
  have oddMem (w : V) : w ∈ oddSide G v ↔ c v ≠ c w := by
    simp only [oddSide,mem_filter,mem_univ,true_and]
    change G.dist v w % 2 = 1 ↔ ¬(c v = c w)
    rw [← par w]
    omega
  have indE : Independent G (evenSide G v) := by
    intro a ha b hb e
    exact proper a b e (((evenMem a).mp ha).symm.trans ((evenMem b).mp hb))
  have indO : Independent G (oddSide G v) := by
    intro a ha b hb e
    have na := (oddMem a).mp ha
    have nb := (oddMem b).mp hb
    have ne := proper a b e
    exact ne (same_other_color na nb)
  have domE : Dominates G (evenSide G v) := by
    intro a
    by_cases inside : a ∈ evenSide G v
    · exact Or.inl inside
    right
    obtain ⟨b,nb⟩ := exists_ne a
    obtain ⟨p⟩ := h a b
    have edge := p.adj_snd (Walk.not_nil_of_ne nb.symm)
    refine ⟨_,(evenMem p.snd).mpr ?_,edge⟩
    have ne := proper _ _ edge
    have na := (evenMem a).not.mp inside
    exact same_other_color (Ne.symm na) ne
  have small := number_le G indE domE
  have oddBound := independent_card_bound G h hn indO
  unfold difference
  omega

theorem catalogue432b [Nonempty V] (h : G.Connected) (hn : 3 < Fintype.card V) :
    (independentDomination G : ℤ) ≤ (outsideSupports G).card +
      minimumDifference G * bipartiteIndicator G := by
  classical
  by_cases bip : Bipartite G
  · simp only [bipartiteIndicator,if_pos bip,mul_one]
    letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have mem : minimumDifference G ∈ univ.image (difference G) := min'_mem _ _
    obtain ⟨v,_,eq⟩ := mem_image.mp mem
    rw [← eq]
    exact parity_bound G h (by omega) bip v
  · simp only [bipartiteIndicator,if_neg bip,Int.mul_zero,Int.add_zero]
    obtain ⟨A,ind,dom⟩ := exists_independent_dominating G
    exact_mod_cast (number_le G ind dom).trans (independent_card_bound G h (by omega) ind)

#print axioms catalogue432b
end
end Graffiti432b
