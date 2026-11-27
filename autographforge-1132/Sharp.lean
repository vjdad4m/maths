import Row1132
import Mathlib.Data.Fintype.Sum

namespace OuterCliques1132
open Finset SimpleGraph HallRainbow1121 AutoGraphForge370
namespace Sharp

/-- K_{m+2,2} with the edge from left vertex zero to the second hub removed. -/
abbrev V (m : ℕ) := Fin (m+2) ⊕ Bool

private def relation {m : ℕ} : V m → V m → Prop
  | .inl i, .inr b | .inr b, .inl i => i ≠ 0 ∨ b = false
  | _, _ => False

def graph (m : ℕ) : SimpleGraph (V m) where
  Adj := relation
  symm := by rintro (i|b) (j|c) <;> simp [relation]
  loopless := by rintro (i|b) <;> simp [relation]

instance (m : ℕ) : DecidableRel (graph m).Adj := by
  rintro (i|b) (j|c) <;> unfold graph <;> dsimp only [relation] <;> infer_instance

variable (m : ℕ)
private def seeds : Finset (V m) := {Sum.inl 0,Sum.inr true}

private theorem connected : (graph m).Connected := by
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨Sum.inr false, ?_⟩
  rintro (i|b)
  · exact (show (graph m).Adj (.inr false) (.inl i) from Or.inr rfl).reachable
  · cases b
    · exact Reachable.rfl
    · let j : Fin (m+2) := ⟨1,by omega⟩
      have edge₁ : (graph m).Adj (.inr false) (.inl j) := Or.inr rfl
      have edge₂ : (graph m).Adj (.inl j) (.inr true) := Or.inl (by
        intro eq
        have := congrArg Fin.val eq
        simp [j] at this)
      exact edge₁.reachable.trans edge₂.reachable

private theorem feasible : OuterDominating (graph m) (seeds m) := by
  constructor
  · rintro (i|b) hx
    · have hi : i ≠ 0 := by simpa [seeds] using hx
      exact ⟨.inr true,by simp [seeds],Or.inl hi⟩
    · cases b
      · exact ⟨.inl 0,by simp [seeds],Or.inr rfl⟩
      · simp [seeds] at hx
  · apply (connected_iff_exists_forall_reachable _).mpr
    let center : ↥((seeds m : Set (V m))ᶜ) := ⟨.inr false,by simp [seeds]⟩
    refine ⟨center,?_⟩
    rintro ⟨(i|b),hx⟩
    · exact (show ((graph m).induce _).Adj center ⟨.inl i,hx⟩ from Or.inr rfl).reachable
    · cases b
      · exact Reachable.rfl
      · simp [seeds] at hx

private theorem edges : (graph m).edgeFinset.card = 2*m + 3 := by
  classical
  let leftRight (p : Fin (m+2) × Bool) : Sym2 (V m) := s(Sum.inl p.1,Sum.inr p.2)
  let index := (univ : Finset (Fin (m+2) × Bool)).erase (0,true)
  have inj : Function.Injective leftRight := by
    rintro ⟨i,b⟩ ⟨j,c⟩ eq
    rcases Sym2.eq_iff.mp eq with ⟨h,h'⟩ | ⟨h,_⟩
    · exact Prod.ext (Sum.inl.inj h) (Sum.inr.inj h')
    · cases h
  have indexed : (graph m).edgeFinset = index.image leftRight := by
    ext e
    refine Sym2.inductionOn e (fun x y => ?_)
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, mem_image]
    constructor
    · intro adj
      cases x with
      | inl i =>
        cases y with
        | inl j => exact adj.elim
        | inr b =>
          refine ⟨(i,b),mem_erase.mpr ⟨?_,mem_univ _⟩,rfl⟩
          rintro h
          cases h
          exact adj.elim (fun q => q rfl) Bool.noConfusion
      | inr b =>
        cases y with
        | inr c => exact adj.elim
        | inl i =>
          refine ⟨(i,b),mem_erase.mpr ⟨?_,mem_univ _⟩,Sym2.eq_swap⟩
          rintro h
          cases h
          exact adj.elim (fun q => q rfl) Bool.noConfusion
    · rintro ⟨⟨i,b⟩,hp,he⟩
      have neq := (mem_erase.mp hp).1
      have ok : i ≠ 0 ∨ b = false := by
        by_cases hz : i = 0
        · subst i
          cases b
          · exact Or.inr rfl
          · exact (neq rfl).elim
        · exact Or.inl hz
      rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> exact ok
  rw [indexed,card_image_of_injective _ inj]
  simp [index, Fintype.card_prod]
  omega

/-- The large independent side requires a different clique label at each vertex. -/
private theorem lower : m+2 ≤ vertexCliqueCover (graph m) := by
  classical
  let G := graph m
  have att : Gᶜ.Colorable (vertexCliqueCover G) :=
    Nat.sInf_mem (s := {n | Gᶜ.Colorable n}) ⟨_,Gᶜ.colorable_of_fintype⟩
  obtain ⟨col⟩ := att
  have inj : Function.Injective (fun i : Fin (m+2) => col (Sum.inl i)) := by
    intro i j eq
    by_contra ne
    apply col.valid ((G.compl_adj _ _).mpr ⟨fun e => ne (Sum.inl.inj e),fun h => h.elim⟩) eq
  simpa using Fintype.card_le_of_injective _ inj

/-- For each cycle rank m the example attains the additive correction exactly. -/
theorem sharp_family :
    (graph m).Connected ∧ Fintype.card (V m) = m+4 ∧ (graph m).edgeFinset.card = 2*m+3 ∧
    outerNumber (graph m) = some 2 ∧ vertexCliqueCover (graph m) = m+2 := by
  classical
  have order : Fintype.card (V m) = m+4 := by simp [V]
  have one : (seeds m).card = 2 := by simp [seeds]
  have ex : ∃ k, ∃ D : Finset (V m), OuterDominating (graph m) D ∧ D.card = k :=
    ⟨2,seeds m,feasible m,one⟩
  have value : outerNumber (graph m) = some (Nat.find ex) := by
    simp only [outerNumber,dif_pos ex]
  have small : Nat.find ex ≤ 2 := Nat.find_min' ex ⟨seeds m,feasible m,one⟩
  have bound := numerical_cycle_rank (graph m) (connected m) value
  rw [order,edges] at bound
  have lo := lower m
  have eq : Nat.find ex = 2 := by omega
  exact ⟨connected m,order,edges m,by rwa [eq] at value,by omega⟩

#print axioms sharp_family
end Sharp
end OuterCliques1132
