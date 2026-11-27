import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! Structural excerpt of the checked Graffiti.pc #137 formalization.
The original file continues with the path-cover inequality. The present
module retains its proof that connectedness of G and its complement forces
an induced path on four vertices. See README.md for the exact source. -/
namespace Graffiti137
open Finset SimpleGraph
open Classical
noncomputable section
variable {V : Type*} (G : SimpleGraph V)

def Consecutive {n : ℕ} (i j : Fin n) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

private instance {n : ℕ} (i j : Fin n) : Decidable (Consecutive i j) := by
  unfold Consecutive
  infer_instance

def InducedPath (n : ℕ) : Prop :=
  ∃ f : Fin n ↪ V, ∀ i j, G.Adj (f i) (f j) ↔ Consecutive i j

private theorem pathOfFour {a b c d : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d)
    (ac : ¬G.Adj a c) (ad : ¬G.Adj a d) (bd : ¬G.Adj b d) : InducedPath G 4 := by
  let f : Fin 4 → V := ![a,b,c,d]
  have hba := ab.symm
  have hcb := bc.symm
  have hdc := cd.symm
  have hca : ¬G.Adj c a := fun h => ac h.symm
  have hda : ¬G.Adj d a := fun h => ad h.symm
  have hdb : ¬G.Adj d b := fun h => bd h.symm
  have rel (i j : Fin 4) : G.Adj (f i) (f j) ↔ Consecutive i j := by
    fin_cases i <;> fin_cases j <;> simp [f, Consecutive, *]
  have rows : ∀ i j : Fin 4, i ≠ j → ∃ k, ¬(Consecutive i k ↔ Consecutive j k) := by decide
  refine ⟨⟨f,?_⟩,rel⟩
  intro i j e
  by_contra ne
  obtain ⟨k,h⟩ := rows i j ne
  exact h ((rel i k).symm.trans (e ▸ rel j k))

private theorem crossing (h : G.Connected) (P : V → Prop) {a b : V} (ha : P a) (hb : ¬P b) :
    ∃ u v, P u ∧ ¬P v ∧ G.Adj u v := by
  by_contra no
  apply hb
  clear hb
  have r := (G.reachable_iff_reflTransGen a b).mp (h a b)
  induction r with
  | refl => exact ha
  | tail _ edge ih =>
    by_contra hv
    exact no ⟨_,_,ih,hv,edge⟩

private def Cut (S : Finset V) (P : V → Prop) :=
  (∃ u ∈ S, P u) ∧ (∃ v ∈ S, ¬P v) ∧
    ∀ a ∈ S, ∀ b ∈ S, P a → ¬P b → ¬G.Adj a b

private theorem flipCut {S : Finset V} {P : V → Prop} (c : Cut G S P) :
    Cut G S (fun v => ¬P v) := by
  obtain ⟨yes,no,sep⟩ := c
  refine ⟨no,?_,?_⟩
  · simpa using yes
  · intro a ha b hb na nnb e
    exact sep b hb a ha (not_not.mp nnb) na e.symm

-- Put a missed vertex on the P side. If the other side sees x, separate
-- the vertices on the P side which miss x. An edge crossing that new cut
-- completes the induced path a-b-x-c.
private theorem extendCut {S : Finset V} {x u : V} {P : V → Prop}
    (cut : Cut G S P) (hu : u ∈ S) (pu : P u) (xu : ¬G.Adj u x)
    (hx : x ∉ S) (no : ¬InducedPath G 4) :
    ∃ Q, Cut G (insert x S) Q := by
  obtain ⟨_,⟨v,hv,pv⟩,sep⟩ := cut
  by_cases sees : ∃ c ∈ S, ¬P c ∧ G.Adj x c
  · obtain ⟨c,hc,pc,xc⟩ := sees
    let Q := fun a => a ∈ S ∧ P a ∧ ¬G.Adj a x
    refine ⟨Q,⟨u,mem_insert_of_mem hu,hu,pu,xu⟩,⟨x,mem_insert_self ..,fun h => hx h.1⟩,?_⟩
    intro a _ b hb qa qb ab
    rcases qa with ⟨ha,pa,ax⟩
    rcases mem_insert.mp hb with rfl | hb
    · exact ax ab
    by_cases pb : P b
    · have bx : G.Adj b x := by
        by_contra h
        exact qb ⟨hb,pb,h⟩
      exact no (pathOfFour G ab bx xc ax (sep a ha c hc pa pc) (sep b hb c hc pb pc))
    · exact sep a ha b hb pa pb ab
  · let Q := fun a => a = x ∨ P a
    refine ⟨Q,⟨x,mem_insert_self ..,Or.inl rfl⟩,⟨v,mem_insert_of_mem hv,?_⟩,?_⟩
    · rintro (rfl | h)
      · exact hx hv
      · exact pv h
    · intro a ha b hb qa qb ab
      have nb : ¬P b := fun p => qb (Or.inr p)
      have hb' : b ∈ S := (mem_insert.mp hb).resolve_left (fun e => qb (Or.inl e))
      rcases mem_insert.mp ha with rfl | ha
      · exact sees ⟨b,hb',nb,ab⟩
      · rcases qa with rfl | pa
        · exact sees ⟨b,hb',nb,ab⟩
        · exact sep a ha b hb' pa nb ab

variable [Fintype V]

/-- The connected/co-connected characterization, in the direction needed for #137. -/
theorem four_of_connected_complement [Nontrivial V] (h : G.Connected) (hc : Gᶜ.Connected) :
    InducedPath G 4 := by
  classical
  by_contra no
  obtain ⟨u,v,ne⟩ := exists_pair_ne V
  obtain ⟨a,b,abEq,bne,ab⟩ := crossing Gᶜ hc (· = u) rfl (Ne.symm ne)
  obtain ⟨nab,miss⟩ := (G.compl_adj a b).mp ab
  let family := univ.filter (fun S : Finset V => ∃ P, Cut G S P)
  have seed : Cut G {a,b} (· = a) := by
    refine ⟨⟨a,by simp,rfl⟩,⟨b,by simp,nab.symm⟩,?_⟩
    intro i _ j hj hi hjn
    subst i
    rcases mem_insert.mp hj with rfl | hj
    · exact (hjn rfl).elim
    · exact (mem_singleton.mp hj) ▸ miss
  obtain ⟨S,hs,largest⟩ := exists_max_image family card
    ⟨{a,b},mem_filter.mpr ⟨mem_univ _,_,seed⟩⟩
  obtain ⟨P,cut⟩ := (mem_filter.mp hs).2
  obtain ⟨i,hi,pi⟩ := cut.1
  obtain ⟨j,hj,pj⟩ := cut.2.1
  obtain ⟨k,l,pk,pl,kl⟩ := crossing G h P pi pj
  have outside : ∃ w, w ∉ S := by
    by_contra! all
    exact cut.2.2 k (all k) l (all l) pk pl kl
  obtain ⟨w,hw⟩ := outside
  obtain ⟨t,x,ht,hx,tx⟩ := crossing Gᶜ hc (· ∈ S) hi hw
  have miss' := ((G.compl_adj t x).mp tx).2
  have bigger : ∃ Q, Cut G (insert x S) Q := by
    by_cases pt : P t
    · exact extendCut G cut ht pt miss' hx no
    · exact extendCut G (flipCut G cut) ht pt miss' hx no
  have bound := largest _ (mem_filter.mpr ⟨mem_univ _,bigger⟩)
  rw [card_insert_of_not_mem hx] at bound
  omega


end
end Graffiti137
