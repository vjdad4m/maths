import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! Ermelinda DeLaVina, Written on the Wall II, Graffiti.pc #137 (July 12, 2005).
The path-order encoding follows the workspace verification of #314 and the
ordinary disjoint path-cover encoding follows its verification of #372. -/
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

def pathOrder := sSup {n | InducedPath G n}

def HasPathCover (p : ℕ) : Prop :=
  ∃ lengths : Fin p → ℕ, ∃ coord : (Σ i : Fin p, Fin (lengths i + 1)) ≃ V,
    ∀ i (j : Fin (lengths i)), G.Adj (coord ⟨i,j.castSucc⟩) (coord ⟨i,j.succ⟩)

def coverNumber := sInf {p | HasPathCover G p}

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
  simp [card_insert_of_not_mem hx] at bound

private theorem singletonCover : HasPathCover G (Fintype.card V) := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · exact (Equiv.sigmaUnique (Fin (Fintype.card V)) (fun _ => Fin 1)).trans (Fintype.equivFin V).symm
  · intro i j
    exact Fin.elim0 j

private theorem minCover : HasPathCover G (coverNumber G) := by
  have non : {n | HasPathCover G n}.Nonempty := ⟨_,singletonCover G⟩
  exact Nat.sInf_mem non

theorem cover_pos [Nonempty V] : 0 < coverNumber G := by
  by_contra! h
  have e : coverNumber G = 0 := by omega
  obtain ⟨_,coord,_⟩ := e ▸ minCover G
  obtain ⟨w,_⟩ := coord.surjective (Classical.arbitrary V)
  exact Fin.elim0 w.1

omit [Fintype V] in
private theorem connected_of_one_cover (one : HasPathCover G 1) : G.Connected := by
  obtain ⟨len,f,edges⟩ := one
  let g := fun j : Fin (len 0 + 1) => f ⟨0,j⟩
  have reach (j : Fin (len 0 + 1)) : G.Reachable (g 0) (g j) := by
    induction j using Fin.induction with
    | zero => rfl
    | succ j ih => exact ih.trans (edges 0 j).reachable
  apply (connected_iff_exists_forall_reachable G).mpr
  refine ⟨g 0,fun v => ?_⟩
  obtain ⟨⟨i,j⟩,rfl⟩ := f.surjective v
  have eq : i = 0 := Subsingleton.elim _ _
  subst i
  exact reach j

private theorem orderBound : BddAbove {n | InducedPath G n} := by
  refine ⟨Fintype.card V,?_⟩
  rintro n ⟨f,_⟩
  simpa using Fintype.card_le_of_injective f f.injective

omit [Fintype V] in
private theorem two_of_edge {a b : V} (ab : G.Adj a b) : InducedPath G 2 := by
  let f : Fin 2 → V := ![a,b]
  have ba := ab.symm
  have ne := ab.ne
  have neq := ne.symm
  refine ⟨⟨f,?_⟩,?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [f, ne, neq]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [f, Consecutive, ab, ba]

theorem catalogue137_product [Nontrivial V] (h : G.Connected) :
    4 ≤ pathOrder G * coverNumber Gᶜ := by
  obtain ⟨u,v,ne⟩ := exists_pair_ne V
  obtain ⟨_,_,_,_,edge⟩ := crossing G h (· = u) rfl (Ne.symm ne)
  have two : 2 ≤ pathOrder G := le_csSup (orderBound G) (two_of_edge G edge)
  have pos := cover_pos Gᶜ
  by_cases e : coverNumber Gᶜ = 1
  · rw [e, Nat.mul_one]
    have one : HasPathCover Gᶜ 1 := e ▸ minCover Gᶜ
    exact le_csSup (orderBound G) (four_of_connected_complement G h (connected_of_one_cover Gᶜ one))
  · exact le_trans (by decide : 4 ≤ 2 * 2) (Nat.mul_le_mul two (by omega))

theorem catalogue137 [Nontrivial V] (h : G.Connected) :
    (4 : ℝ) / coverNumber Gᶜ ≤ pathOrder G := by
  apply (div_le_iff₀ (by exact_mod_cast cover_pos Gᶜ)).mpr
  exact_mod_cast catalogue137_product G h

/-- The literal one-vertex domain has positive denominator and fails. -/
theorem catalogue137_singleton [Unique V] :
    G.Connected ∧ pathOrder G = 1 ∧ coverNumber Gᶜ = 1 ∧
      ¬ ((4 : ℝ) / coverNumber Gᶜ ≤ pathOrder G) := by
  have cardV : Fintype.card V = 1 := Fintype.card_unique
  have cov : coverNumber Gᶜ = 1 := by
    have le : coverNumber Gᶜ ≤ Fintype.card V := Nat.sInf_le (singletonCover Gᶜ)
    have pos := cover_pos Gᶜ
    omega
  have single : InducedPath G 1 := by
    refine ⟨⟨fun _ => default,fun _ _ _ => Subsingleton.elim _ _⟩,?_⟩
    intro i j
    fin_cases i
    fin_cases j
    simp [Consecutive]
  have ord : pathOrder G = 1 := by
    apply le_antisymm
    · apply csSup_le'
      rintro n ⟨f,_⟩
      simpa [cardV] using Fintype.card_le_of_injective f f.injective
    · exact le_csSup (orderBound G) single
  have con : G.Connected := (connected_iff_exists_forall_reachable G).mpr
    ⟨default,fun w => (Subsingleton.elim default w) ▸ (Reachable.refl (G := G) default)⟩
  refine ⟨con,ord,cov,?_⟩
  simp [ord,cov]

#print axioms four_of_connected_complement
#print axioms catalogue137_product
#print axioms catalogue137
#print axioms catalogue137_singleton
end
end Graffiti137
