import FourRingCyclicGeometry
import FourRingThreeConnected
import Lean.Elab.Tactic.Omega

namespace KelmansCactus.AtomicBridge.HandleExtension
open SimpleGraph Finset FourRingCutAux
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

variable {V : Type*} {G : SimpleGraph V}

structure Edges (G : SimpleGraph V) where
  a : Bool → V
  b : Bool → V
  edge : ∀ s, G.Adj (a s) (b s)
  separated : ∀ {s t : Bool} {x : V}, (x=a s ∨ x=b s) →
    (x=a t ∨ x=b t) → s=t

namespace Edges
variable (E : Edges G)

def Ends (s : Bool) (x : V) : Prop := x=E.a s ∨ x=E.b s

def PairFor (s : Bool) (x y : V) : Prop :=
  (x=E.a s ∧ y=E.b s) ∨ (x=E.b s ∧ y=E.a s)

def Removed (x y : V) : Prop := ∃ s, E.PairFor s x y

theorem pair_symm {s : Bool} {x y : V} (h : E.PairFor s x y) : E.PairFor s y x := by
  unfold PairFor at *
  tauto

theorem pair_ends {s : Bool} {x y : V} (h : E.PairFor s x y) : E.Ends s x ∧ E.Ends s y := by
  unfold PairFor Ends at *
  tauto

theorem pair_adj {s : Bool} {x y : V} (h : E.PairFor s x y) : G.Adj x y := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact E.edge s
  · exact (E.edge s).symm

theorem pair_neighbor_unique {s : Bool} {x y z : V}
    (h : E.PairFor s x y) (h' : E.PairFor s x z) : y=z := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · rcases h' with ⟨_,rfl⟩|⟨hh,_⟩
    · rfl
    · exact ((E.edge s).ne hh).elim
  · rcases h' with ⟨hh,_⟩|⟨_,rfl⟩
    · exact ((E.edge s).ne hh.symm).elim
    · rfl

def deleteChosen : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ¬ E.Removed x y
  symm := by
    intro x y h
    exact ⟨h.1.symm, fun ⟨s,hs⟩ => h.2 ⟨s,E.pair_symm hs⟩⟩
  loopless := fun _ h => G.loopless _ h.1

/-- Replace each chosen edge by a two-edge path and join the new vertices. -/
def host : SimpleGraph (V ⊕ Bool) where
  Adj x y := match x,y with
    | .inl x, .inl y => E.deleteChosen.Adj x y
    | .inl x, .inr s | .inr s, .inl x => E.Ends s x
    | .inr s, .inr t => s≠t
  symm := by
    intro x y h
    cases x <;> cases y
    · exact E.deleteChosen.symm h
    · exact h
    · exact h
    · exact Ne.symm h
  loopless := by
    intro x h
    cases x
    · exact E.deleteChosen.loopless _ h
    · exact h rfl

instance [DecidableRel G.Adj] : DecidableRel E.host.Adj := by
  classical
  exact fun _ _ => Classical.propDecidable _

def Old : Set (V ⊕ Bool) := {x | ∃ v, x=Sum.inl v}

def deleted_iso : E.deleteChosen ≃g E.host.induce (Old (V:=V)) where
  toEquiv :=
    { toFun := fun v => ⟨Sum.inl v,⟨v,rfl⟩⟩
      invFun := fun x => Classical.choose x.prop
      left_inv := fun v => Sum.inl.inj ((Classical.choose_spec
        (show Sum.inl v ∈ Old (V:=V) from ⟨v,rfl⟩)).symm)
      right_inv := fun x => Subtype.ext (Classical.choose_spec x.prop).symm }
  map_rel_iff' := by intro a b; rfl

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private def neighborLift (x y : V) : V ⊕ Bool := by
  classical
  exact if h : E.Removed x y then Sum.inr (Classical.choose h) else Sum.inl y

theorem degree_old (x : V) : E.host.degree (Sum.inl x) = G.degree x := by
  classical
  rw [← E.host.card_neighborFinset_eq_degree,← G.card_neighborFinset_eq_degree]
  symm
  apply Finset.card_bij (fun y _ => E.neighborLift x y)
  · intro y hy
    apply (E.host.mem_neighborFinset _ _).mpr
    have e := (G.mem_neighborFinset _ _).mp hy
    unfold neighborLift
    split
    · rename_i h
      exact (E.pair_ends (Classical.choose_spec h)).1
    · rename_i h
      exact ⟨e,h⟩
  · intro y _ z _ h
    unfold neighborLift at h
    split at h <;> split at h
    · rename_i hy hz
      have e := Sum.inr.inj h
      have hz' := Classical.choose_spec hz
      rw [← e] at hz'
      exact E.pair_neighbor_unique (Classical.choose_spec hy) hz'
    · cases h
    · cases h
    · exact Sum.inl.inj h
  · rintro (y|s) hy
    · have hh : G.Adj x y ∧ ¬ E.Removed x y := (E.host.mem_neighborFinset _ _).mp hy
      exact ⟨y,(G.mem_neighborFinset _ _).mpr hh.1,by simp [neighborLift,hh.2]⟩
    · have hxs : E.Ends s x := (E.host.mem_neighborFinset _ _).mp hy
      have hex : ∃ y, E.PairFor s x y := by
        rcases hxs with ha|hb
        · exact ⟨E.b s, Or.inl ⟨ha,rfl⟩⟩
        · exact ⟨E.a s, Or.inr ⟨hb,rfl⟩⟩
      obtain ⟨y,hy'⟩ := hex
      have h : E.Removed x y := ⟨s,hy'⟩
      refine ⟨y,(G.mem_neighborFinset _ _).mpr (E.pair_adj hy'),?_⟩
      have h' := (E.pair_ends (Classical.choose_spec h)).1
      have eq := E.separated h' hxs
      unfold neighborLift
      rw [dif_pos h,eq]

theorem degree_new (s : Bool) : E.host.degree (Sum.inr s) = 3 := by
  classical
  rw [← E.host.card_neighborFinset_eq_degree]
  have h : E.host.neighborFinset (Sum.inr s) =
      ({Sum.inl (E.a s),Sum.inl (E.b s),Sum.inr (!s)} : Finset (V ⊕ Bool)) := by
    ext x
    rw [E.host.mem_neighborFinset]
    cases x with
    | inl x =>
      change E.Ends s x ↔ _
      simp [Ends]
    | inr t =>
      change s≠t ↔ _
      cases s <;> cases t <;> simp
  rw [h]
  have hn : Sum.inl (E.a s) ≠ (Sum.inl (E.b s) : V ⊕ Bool) :=
    fun e => (E.edge s).ne (Sum.inl.inj e)
  simp [hn]

theorem cubic (h : ∀ v,G.degree v=3) : ∀ x,E.host.degree x=3 := by
  rintro (a|s)
  · exact (E.degree_old a).trans (h a)
  · exact E.degree_new s

#print axioms deleted_iso
#print axioms cubic
end Edges
end
end KelmansCactus.AtomicBridge.HandleExtension
