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

/-! Ermelinda DeLaVina, Written on the Wall II, Graffiti.pc #397c (January 2010). -/
namespace Graffiti397c
open GraffitiPendant Finset SimpleGraph
open Classical
noncomputable section
variable {V : Type*} (G : SimpleGraph V)

def square : SimpleGraph V where
  Adj u v := u ≠ v ∧ 0 < G.dist u v ∧ G.dist u v ≤ 2
  symm := by intro u v h; rw [G.dist_comm]; exact ⟨h.1.symm,h.2⟩
  loopless := fun _ h => h.1 rfl

def TwoDominates (D : Finset V) : Prop :=
  ∀ s, s ∈ D ∨ ∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ G.Adj s a ∧ G.Adj s b

def dominationNumber : ℕ := sInf {k | ∃ D : Finset V, Dominates G D ∧ D.card = k}
def twoDominationNumber : ℕ := sInf {k | ∃ D : Finset V, TwoDominates G D ∧ D.card = k}

/-- Move a selected pendant onto its support. Every other selected vertex stays put. -/
private def move (t : V) : V := if h : Pendant G t then h.choose else t

private theorem move_pendant {l s : V} (pl : Pendant G l) (ls : G.Adj l s) :
    move G l = s := by
  rw [move,dif_pos pl]
  exact (pl.choose_spec.2 s ls).symm

private theorem near_pendant (h : G.Connected) {l s t : V}
    (pl : Pendant G l) (ls : G.Adj l s) (d : G.dist l t ≤ 2) :
    t = l ∨ t = s ∨ G.Adj s t := by
  obtain ⟨p,hp⟩ := h.exists_walk_length_eq_dist l t
  have bound : p.length ≤ 2 := hp.trans_le d
  cases p with
  | nil => exact Or.inl rfl
  | cons e q =>
    have eq := pl.unique e ls
    subst_vars
    have small : q.length + 1 ≤ 2 := bound
    by_cases zero : q.length = 0
    · exact Or.inr (Or.inl (q.eq_of_length_eq_zero zero).symm)
    · exact Or.inr (Or.inr (q.adj_of_length_eq_one (by omega)))

variable [Fintype V]

theorem lift_square_dominating_set (h : G.Connected) (hn : 2 < Fintype.card V)
    {T : Finset V} (dom : Dominates (square G) T) :
    ∃ D : Finset V, TwoDominates G D ∧ D.card ≤ (outsideSupports G).card + T.card := by
  classical
  let D := outsideSupports G ∪ T.image (move G)
  have includeOutside {x : V} (n : ¬Support G x) : x ∈ D :=
    mem_union_left _ ((mem_outside G).mpr n)
  have includeMoved {t : V} (ht : t ∈ T) : move G t ∈ D :=
    mem_union_right _ (mem_image_of_mem _ ht)
  refine ⟨D,?_,(card_union_le ..).trans (Nat.add_le_add_left card_image_le _)⟩
  intro s
  by_cases inD : s ∈ D
  · exact Or.inl inD
  right
  have sup : Support G s := Classical.byContradiction (fun no => inD (includeOutside no))
  obtain ⟨l,pl,ls⟩ := sup
  have hl : l ∈ D := includeOutside (pendant_not_support G h hn pl)
  have lout : l ∉ T := fun ht => inD (move_pendant G pl ls ▸ includeMoved ht)
  obtain ⟨t,ht,near⟩ := (dom l).resolve_left lout
  rcases near_pendant G h pl ls near.2.2 with rfl | rfl | st
  · exact (lout ht).elim
  · have ps : ¬Pendant G t := fun p => pendant_not_support G h hn p ⟨l,pl,ls⟩
    have inside := includeMoved ht
    rw [move,dif_neg ps] at inside
    exact (inD inside).elim
  · have tin : t ∈ D := by
      by_cases pt : Pendant G t
      · exact includeOutside (pendant_not_support G h hn pt)
      · simpa [move,pt] using includeMoved ht
    exact ⟨l,hl,t,tin,fun e => lout (e ▸ ht),ls.symm,st⟩

theorem catalogue397c (h : G.Connected) (hn : 2 < Fintype.card V) :
    twoDominationNumber G ≤ (outsideSupports G).card + dominationNumber (square G) := by
  have available : {n | ∃ T : Finset V, Dominates (square G) T ∧ T.card = n}.Nonempty :=
    ⟨_,univ,(fun v => Or.inl (mem_univ v)),rfl⟩
  obtain ⟨T,dom,size⟩ := Nat.sInf_mem available
  obtain ⟨D,two,bound⟩ := lift_square_dominating_set G h hn dom
  change T.card = dominationNumber (square G) at size
  rw [size] at bound
  exact (Nat.sInf_le (s := {k | ∃ S : Finset V, TwoDominates G S ∧ S.card = k})
    ⟨D,two,rfl⟩).trans bound

#print axioms catalogue397c
end
end Graffiti397c
