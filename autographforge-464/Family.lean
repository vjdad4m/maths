import HallRainbow
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Tactic.FinCases

namespace PlanarRainbow464
open SimpleGraph Finset HallRainbow1121
abbrev Core (m : ℕ) := Bool ⊕ Fin m
abbrev Leaf (m : ℕ) := Fin m × Bool
abbrev V (m : ℕ) := Core m ⊕ Leaf m
abbrev hub {m : ℕ} (b : Bool) : V m := .inl (.inl b)
abbrev center {m : ℕ} (i : Fin m) : V m := .inl (.inr i)
abbrev leaf {m : ℕ} (i : Fin m) (b : Bool) : V m := .inr (i,b)

def incident {m : ℕ} : Core m → Leaf m → Prop
  | .inl _, _ => True
  | .inr i, p => i = p.1

def edge {m : ℕ} : V m → V m → Prop
  | .inl c, .inr p | .inr p, .inl c => incident c p
  | _, _ => False

def graph (m : ℕ) : SimpleGraph (V m) where
  Adj := edge
  symm := by rintro (a|a) (b|b) h <;> exact h
  loopless := by rintro (a|a) <;> exact id

theorem order (m : ℕ) : Fintype.card (V m) = 3*m+2 := by
  simp [V,Core,Leaf,Fintype.card_prod]; omega

theorem connected {m : ℕ} (hm : 0<m) : (graph m).Connected := by
  let z : Fin m := ⟨0,hm⟩
  have toHub (v : V m) : (graph m).Reachable v (hub false) := by
    rcases v with ((b|i)|p)
    · exact (show (graph m).Adj (hub b) (leaf z false) from trivial).reachable.trans
        (show (graph m).Adj (leaf z false) (hub false) from trivial).reachable
    · exact (show (graph m).Adj (center i) (leaf i false) from rfl).reachable.trans
        (show (graph m).Adj (leaf i false) (hub false) from trivial).reachable
    · exact (show (graph m).Adj (.inr p) (hub false) from trivial).reachable
  exact ⟨fun a b => (toHub a).trans (toHub b).symm⟩

theorem bipartite (m : ℕ) : (graph m).Colorable 2 := by
  let part : V m → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)
  refine ⟨Coloring.mk part ?_⟩
  rintro (a|a) (b|b) h <;> first | exact h.elim | exact (by decide : (0 : Fin 2) ≠ 1) | exact (by decide : (1 : Fin 2) ≠ 0)

theorem k4free (m : ℕ) : (graph m).CliqueFree 4 := by
  exact (bipartite m).cliqueFree (by decide)

private def mark {m : ℕ} : V m → Fin 4
  | .inl (.inl false) => 1
  | .inl (.inl true) => 2
  | .inl (.inr _) => 3
  | .inr _ => 0

private theorem mark_ok (m : ℕ) : Rainbow (graph m) (@mark m) := by
  rintro ((b|i)|⟨i,b⟩) zero c hc
  · cases b <;> simp [mark] at zero
  · simp [mark] at zero
  · fin_cases c
    · exact (hc rfl).elim
    · exact ⟨hub false,trivial,rfl⟩
    · exact ⟨hub true,trivial,rfl⟩
    · exact ⟨center i,rfl,rfl⟩

private theorem mark_cost (m : ℕ) : weight (@mark m) = m+2 := by
  classical
  have marked : univ.filter (fun v : V m => mark v ≠ 0) =
      (univ : Finset (Core m)).image Sum.inl := by
    ext v
    rcases v with ((b|i)|p)
    · cases b <;> simp [mark]
    · simp [mark]
    · simp [mark]
  rw [weight,marked,card_image_of_injective _ Sum.inl_injective,card_univ]
  simp [Core,Nat.add_comm]

/-- A zero cannot see three singleton labels at just two vertices. -/
private theorem two_insufficient {U : Type*} {G : SimpleGraph U} {f : U → Fin 4}
    (hf : Rainbow G f) (v a b : U) (zero : f v=0)
    (two : ∀ u, G.Adj v u → f u ≠ 0 → u=a ∨ u=b) : False := by
  obtain ⟨u,hu,cu⟩ := hf v zero 1 (by decide)
  obtain ⟨w,hw,cw⟩ := hf v zero 2 (by decide)
  obtain ⟨x,hx,cx⟩ := hf v zero 3 (by decide)
  have pu := two u hu (by rw [cu]; decide)
  have pw := two w hw (by rw [cw]; decide)
  have px := two x hx (by rw [cx]; decide)
  rcases pu with e|e <;> rcases pw with e'|e' <;> rcases px with e''|e'' <;> simp_all

theorem rainbow_exact {m : ℕ} (hm : 2 ≤ m) : rainbowNumber (graph m) 3 = m+2 := by
  classical
  let sizes := {n | ∃ f : V m → Fin 4, weight f = n ∧ Rainbow (graph m) f}
  have good : m+2 ∈ sizes := ⟨mark,mark_cost m,mark_ok m⟩
  obtain ⟨f,cost,hf⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨_,good⟩)
  have gray (i : Fin m) : f (center i) ≠ 0 := by
    intro zero
    apply two_insufficient hf (center i) (leaf i false) (leaf i true) zero
    rintro (c|⟨j,b⟩) adj _
    · exact adj.elim
    · change i=j at adj
      subst j; cases b <;> simp
  have lower : m+2 ≤ weight f := by
    by_cases hubs : ∀ b, f (hub b) ≠ 0
    · have h : (univ : Finset (Core m)).card ≤ weight f := by
        apply card_le_card_of_injOn Sum.inl ?_ Sum.inl_injective.injOn
        rintro (b|i) _ <;> apply mem_filter.mpr
        · exact ⟨mem_univ _,hubs b⟩
        · exact ⟨mem_univ _,gray i⟩
      simpa [Core,Nat.add_comm] using h
    · push_neg at hubs
      obtain ⟨b,hb⟩ := hubs
      have colored (p : Leaf m) : f (.inr p) ≠ 0 := by
        intro zero
        apply two_insufficient hf (.inr p) (hub (!b)) (center p.1) zero
        rintro ((c|i)|q) adj nz
        · cases b <;> cases c <;> simp_all
        · change i=p.1 at adj
          exact Or.inr (congrArg center adj)
        · exact adj.elim
      have h : (univ : Finset (Leaf m)).card ≤ weight f := by
        apply card_le_card_of_injOn Sum.inr ?_ Sum.inr_injective.injOn
        exact fun p _ => mem_filter.mpr ⟨mem_univ _,colored p⟩
      simp [Leaf,Fintype.card_prod] at h
      omega
  exact le_antisymm (Nat.sInf_le good) (lower.trans_eq cost)

theorem cover_exact {m : ℕ} (hm : 2 ≤ m) : vertexCliqueCover (graph m) = 2*m := by
  classical
  let i0 : Fin m := ⟨0,by omega⟩
  let i1 : Fin m := ⟨1,by omega⟩
  let rep : Core m → Leaf m := fun c => match c with
    | .inl false => (i0,true) | .inl true => (i1,true) | .inr i => (i,false)
  have h01 : i0 ≠ i1 := fun e => Nat.zero_ne_one (congrArg Fin.val e)
  have inj : Function.Injective rep := by
    rintro (b|i) (b'|j) h
    · cases b <;> cases b' <;> simp_all [rep]
    · cases b <;> simp [rep] at h
    · cases b' <;> simp [rep] at h
    · simpa [rep] using h
  have incidentRep (c : Core m) : incident c (rep c) := by
    cases c with | inl b => trivial | inr i => rfl
  let slot : V m → Leaf m := Sum.elim rep id
  have proper {v w : V m} (h : (graph m)ᶜ.Adj v w) : slot v ≠ slot w := by
    obtain ⟨ne,no⟩ := ((graph m).compl_adj _ _).mp h
    rintro eq
    rcases v with c|x <;> rcases w with d|y
    · exact ne (congrArg Sum.inl (inj eq))
    · change rep c=y at eq
      exact no (eq ▸ incidentRep c)
    · change x=rep d at eq
      exact no (eq.symm ▸ incidentRep d)
    · exact ne (congrArg Sum.inr eq)
  let col : (graph m)ᶜ.Coloring (Leaf m) := Coloring.mk slot proper
  have upper : (graph m)ᶜ.Colorable (2*m) := by
    simpa [Leaf,Fintype.card_prod,Nat.mul_comm] using col.colorable
  have att : (graph m)ᶜ.Colorable (vertexCliqueCover (graph m)) :=
    Nat.sInf_mem (s := {n | (graph m)ᶜ.Colorable n}) ⟨_,upper⟩
  obtain ⟨g⟩ := att
  have embeds : Function.Injective (fun p : Leaf m => g (Sum.inr p)) := by
    intro p q eq
    by_contra ne
    exact g.valid (((graph m).compl_adj _ _).mpr ⟨fun e => ne (Sum.inr.inj e),id⟩) eq
  exact le_antisymm (Nat.sInf_le upper) (by simpa [Leaf,Fintype.card_prod,Nat.mul_comm] using Fintype.card_le_of_injective _ embeds)
end PlanarRainbow464
