import CambyCycleDecomp133
import C7MultiWeightedGlobal133
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

namespace Graffiti133P5Radius
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Camby
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def tags (H : Hole G 5) (x : V) : Finset (Fin 5) :=
  Finset.univ.filter (fun i=>G.Adj x (H.c i))

@[simp] theorem mem_tags (H : Hole G 5) (x : V) (i : Fin 5) :
    i∈tags H x ↔ G.Adj x (H.c i) := by simp [tags]

def tagAllowed (A : Finset (Fin 5)) : Prop :=
  ∀ i∈A,∀ j∈A,i ≠ j → ¬∃ k,Cyclic i k ∧ Cyclic j k

instance (A : Finset (Fin 5)) : Decidable (tagAllowed A) := by unfold tagAllowed; infer_instance

theorem allowed_tag_form :
    ∀ A : Finset (Fin 5),A.Nonempty→tagAllowed A →
      (∃ i : Fin 5,A={i}) ∨ (∃ i : Fin 5,A={i,i+1}) := by decide

theorem tags_allowed (H : Hole G 5) (h4 : FourCycleFree G) (x : V) (out : Outside H.c x) :
    tagAllowed (tags H x) := by
  intro a am b bm ne
  rintro ⟨k,ak,bk⟩
  exact ne (H.inj (h4 x (H.c k) (H.c a) (H.c b) (out k)
    ((mem_tags H x a).mp am) (((H.adj a k).mpr ak).symm)
    ((mem_tags H x b).mp bm) (((H.adj b k).mpr bk).symm)))

def siteArc (t : Fin 5) (i : Fin 4) : Fin 5 := t + Fin.castLE (by decide) i

theorem arc_geometry : ∀ t : Fin 5,
    Function.Injective (siteArc t) ∧ siteArc t 0=t ∧
    (∀ a b : Fin 4,a<b → (Cyclic (siteArc t a) (siteArc t b) ↔ a.val+1=b.val)) := by decide

theorem singleton_tag_gives_p5 (H : Hole G 5) (x : V) (out : Outside H.c x)
    (t : Fin 5) (prof : tags H x={t}) : ∃ p : Fin 5→V,InducedPath G p := by
  let f (a : Fin 5) := if h : a.val=0 then x else H.c (siteArc t ⟨a.val-1,by have := a.isLt; omega⟩)
  refine ⟨f,?_,?_⟩
  · dsimp only [f]
    intro a b eq
    by_cases az : a.val=0 <;> by_cases bz : b.val=0
    · exact Fin.ext (az.trans bz.symm)
    · simp only [dif_pos az,dif_neg bz] at eq
      exact (out _ eq).elim
    · simp only [dif_neg az,dif_pos bz] at eq
      exact (out _ eq.symm).elim
    · simp only [dif_neg az,dif_neg bz] at eq
      have h : a.val-1=b.val-1 := congrArg (fun i : Fin 4=>i.val) ((arc_geometry t).1 (H.inj eq))
      exact Fin.ext (by omega)
  dsimp only [f]
  intro a b ab
  have lt : a.val<b.val := ab
  have bz : b.val≠0 := by omega
  by_cases az : a.val=0
  · rw [dif_pos az,dif_neg bz,←mem_tags,prof,Finset.mem_singleton]
    have eq0 (k : Fin 4) : siteArc t k=t↔k=0 := by
      exact ⟨fun e=>(arc_geometry t).1 (e.trans (arc_geometry t).2.1.symm),
        fun e=>(congrArg (siteArc t) e).trans (arc_geometry t).2.1⟩
    rw [eq0]
    constructor
    · intro h
      have hh := congrArg (fun i : Fin 4=>i.val) h
      change b.val-1=0 at hh
      omega
    · intro h
      apply Fin.ext
      change b.val-1=0
      omega
  · rw [dif_neg az,dif_neg bz,H.adj]
    exact ((arc_geometry t).2.2 _ _ (by change a.val-1<b.val-1; omega)).trans
      ⟨fun q=>by change a.val-1+1=b.val-1 at q; omega,
       fun q=>by change a.val-1+1=b.val-1; omega⟩

theorem opposed_pairs_force_p5 (H : Hole G 5) (h4 : FourCycleFree G)
    (x y : V) (xo : Outside H.c x) (yo : Outside H.c y)
    (xp : tags H x={0,1}) (yp : tags H y={3,4}) : ∃ p : Fin 5→V,InducedPath G p := by
  have A (i : Fin 5) : G.Adj x (H.c i) ↔ i=0 ∨ i=1 := by
    rw [←mem_tags,xp,Finset.mem_insert,Finset.mem_singleton]
  have B (i : Fin 5) : G.Adj y (H.c i) ↔ i=3 ∨ i=4 := by
    rw [←mem_tags,yp,Finset.mem_insert,Finset.mem_singleton]
  have xy : x≠y := by
    intro e
    have h := (B 0).mp (e ▸ (A 0).mpr (Or.inl rfl))
    exact h.elim (by decide) (by decide)
  have no : ¬G.Adj x y := by
    intro e
    have hit := h4 x (H.c 4) (H.c 0) y (xo 4)
      ((A 0).mpr (Or.inl rfl)) ((H.adj 4 0).mpr (by decide)) e ((B 4).mpr (Or.inr rfl)).symm
    exact yo 0 hit.symm
  let f : Fin 5→V := ![x,H.c 1,H.c 2,H.c 3,y]
  have same (i j : Fin 5) : H.c i=H.c j ↔ i=j := H.inj.eq_iff
  have xon (i : Fin 5) : H.c i≠x := (xo i).symm
  have yon (i : Fin 5) : H.c i≠y := (yo i).symm
  have noyx : ¬G.Adj y x := fun h=>no h.symm
  have AX (i : Fin 5) : G.Adj (H.c i) x ↔ i=0 ∨ i=1 := (G.adj_comm _ _).trans (A i)
  have BY (i : Fin 5) : G.Adj (H.c i) y ↔ i=3 ∨ i=4 := (G.adj_comm _ _).trans (B i)
  refine ⟨f,?_,?_⟩
  · intro a b e
    fin_cases a <;> fin_cases b <;> simp [f,same,xy,xy.symm,xo,yo,xon,yon] at e ⊢ <;> first | exact xo _ e | exact yo _ e
  · intro a b lt
    fin_cases a <;> fin_cases b <;>
      simp [f,A,B,AX,BY,no,noyx,H.adj,Cyclic] at lt ⊢ <;> decide

#print axioms singleton_tag_gives_p5
#print axioms opposed_pairs_force_p5
end Graffiti133P5Radius
