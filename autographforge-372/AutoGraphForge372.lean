import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega

/-! AutoGraphForge line 372, ID f799b678. Colors are singleton labels as in GraphCalc. -/
namespace AutoGraphForge372
open SimpleGraph Finset
open scoped BigOperators
variable {U : Type*} [Fintype U] (G : SimpleGraph U)

def ClawFree := ∀ v a b c : U, G.Adj v a → G.Adj v b → G.Adj v c →
  a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

def Roman (f : U → Fin 3) : Prop := ∀ v, f v=0 → ∃ u, G.Adj v u ∧ f u=2
noncomputable def romanNumber := sInf {n | ∃ f : U → Fin 3, Roman G f ∧ ∑ v, (f v:ℕ) = n}
def Rainbow (g : U → Fin 3) : Prop :=
  ∀ v, g v=0 → ∀ c : Fin 3, c ≠ 0 → ∃ w, G.Adj v w ∧ g w=c
def weight (g : U → Fin 3) := (univ.filter (fun v => g v ≠ 0)).card
noncomputable def rainbowNumber := sInf {n | ∃ g : U → Fin 3, weight g=n ∧ Rainbow G g}

theorem convert [DecidableRel G.Adj] (deg : ∀ v, G.degree v ≤ 2) {f : U → Fin 3}
    (roman : Roman G f) : ∃ g : U → Fin 3, Rainbow G g ∧ weight g ≤ ∑ v, (f v:ℕ) := by
  classical
  let owner (v : U) := if h : f v=0 then (roman v h).choose else v
  let Z := univ.filter (fun v => f v=0)
  let D (x : U) := Z.filter (fun v => owner v=x)
  have child {x v : U} (h : v ∈ D x) : f v=0 ∧ owner v=x ∧ G.Adj x v ∧ f x=2 := by
    obtain ⟨hz,e⟩ := mem_filter.mp h
    have fv := (mem_filter.mp hz).2
    have spec := (roman v fv).choose_spec
    simp only [owner,dif_pos fv] at e
    exact ⟨fv,(mem_filter.mp h).2,e ▸ spec.1.symm,e ▸ spec.2⟩
  have cap (x : U) : (D x).card ≤ 2 :=
    (card_le_card (show D x ⊆ G.neighborFinset x from
      fun v hv => (G.mem_neighborFinset x v).mpr (child hv).2.2.1)).trans (deg x)
  have local_colors (x : U) : ∃ p : U → Fin 3, (∀ v, p v ≠ 0) ∧
      ((D x).card=2 → ∀ c : Fin 3, c ≠ 0 → ∃ v ∈ D x, p v=c) := by
    by_cases two : (D x).card=2
    · obtain ⟨a,b,ne,eq⟩ := card_eq_two.mp two
      refine ⟨fun v => if v=a then 1 else 2,fun v => by change (if v=a then (1:Fin 3) else 2) ≠ 0; split <;> decide,?_⟩
      intro _ c hc
      have cases' : c=1 ∨ c=2 := by omega
      rcases cases' with rfl | rfl
      · exact ⟨a,by simp [eq],by simp⟩
      · exact ⟨b,by simp [eq],by simp [ne.symm]⟩
    · exact ⟨fun _ => 1,fun _ => (by decide : (1:Fin 3) ≠ 0),fun bad => (two bad).elim⟩
  choose p nonzero both using local_colors
  let g (v : U) : Fin 3 := if f v=0 then p (owner v) v else if (D v).card=2 then 0 else 1
  refine ⟨g,?_,?_⟩
  · intro x hx c hc
    have fx : f x ≠ 0 := by
      intro e
      exact nonzero (owner x) x (by simpa [g,e] using hx)
    have two : (D x).card=2 := by simpa [g,fx] using hx
    obtain ⟨v,hv,pc⟩ := both x two c hc
    obtain ⟨fv,ox,adj,_⟩ := child hv
    exact ⟨v,adj, by simpa [g,fv,ox] using pc⟩
  · have per (x : U) : (if g x ≠ 0 then 1 else 0) + (D x).card ≤
        (f x:ℕ) + (if f x=0 then 1 else 0) := by
      by_cases high : f x=2
      · have low : f x ≠ 0 := by omega
        by_cases two : (D x).card=2
        · simp [g,high,two]
        · have bound := cap x
          simp [g,high,two]
          omega
      · have no : D x=∅ := eq_empty_iff_forall_not_mem.mpr (fun _ h => high (child h).2.2.2)
        by_cases zero : f x=0
        · simp [g,zero,no,nonzero]
        · have one : f x=1 := by omega
          simp [g,one,no]
    have total := sum_le_sum (s := (univ : Finset U)) (fun x _ => per x)
    simp only [sum_add_distrib] at total
    have count : ∑ x, (D x).card = Z.card := by
      simpa [D] using sum_card_fiberwise_eq_card_filter Z univ owner
    rw [count,sum_boole,sum_boole] at total
    exact Nat.le_of_add_le_add_right total

theorem row372 [DecidableRel G.Adj] (claw : ClawFree G) (tri : G.CliqueFree 3) :
    rainbowNumber G ≤ romanNumber G := by
  classical
  have degree (v : U) : G.degree v ≤ 2 := by
    by_contra! high
    obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := two_lt_card_iff.mp high
    have no_triangle (x y : U) (vx : G.Adj v x) (vy : G.Adj v y) : ¬G.Adj x y := by
      intro xy
      have clique : G.IsNClique 3 {v,x,y} := by
        rw [isNClique_iff]
        refine ⟨?_,by simp [vx.ne,vy.ne,xy.ne]⟩
        intro i hi j hj ne
        simp only [coe_insert,coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hi hj
        rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> first | contradiction | assumption | exact vx.symm | exact vy.symm | exact xy.symm
      exact tri _ clique
    have va := (G.mem_neighborFinset v _).mp ha
    have vb := (G.mem_neighborFinset v _).mp hb
    have vc := (G.mem_neighborFinset v _).mp hc
    exact (claw v a b c va vb vc ab ac bc).elim (no_triangle _ _ va vb)
      (fun h => h.elim (no_triangle _ _ va vc) (no_triangle _ _ vb vc))
  let sizes := {k | ∃ f : U → Fin 3, Roman G f ∧ ∑ v, (f v:ℕ) = k}
  have ex : sizes.Nonempty := ⟨_,fun _ => 1,fun _ bad => False.elim ((by decide : (1:Fin 3) ≠ 0) bad),rfl⟩
  obtain ⟨f,hr,cost⟩ := Nat.sInf_mem ex
  obtain ⟨g,hg,bound⟩ := convert G degree hr
  change ∑ v, (f v:ℕ) = romanNumber G at cost
  exact (Nat.sInf_le (s := {n | ∃ g : U → Fin 3, weight g=n ∧ Rainbow G g}) ⟨g,rfl,hg⟩).trans
    (bound.trans_eq cost)

#print axioms convert
#print axioms row372
end AutoGraphForge372

