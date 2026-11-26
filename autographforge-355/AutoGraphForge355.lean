import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Tauto

/-! Standalone for Lean 4.19.0 and Mathlib v4.19.0. -/

/-! Lean 4.19.0 / Mathlib 4.19.0. This standalone replay includes the helper namespaces from Graffiti.pc #137, #432b and #326. -/

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

/-! Ján Pastorek, AutoGraphForge, commit 4d1a8afc99447cacd2328cca20e47b6493e8dbc5,
normalised survivor file line 378, raw touch rank 389, ID 3f33df08. -/
namespace AutoGraphForge378
open Finset SimpleGraph Graffiti432b GraffitiPendant
open Classical
noncomputable section
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Source predicate from LeanProject/GraphInvariants.lean (P4-free). -/
def Cograph := ∀ a b c d : V, G.Adj a b → G.Adj b c → G.Adj c d →
  ¬G.Adj a c → ¬G.Adj b d → G.Adj a d

/-- Exactly a matching whose uncovered vertices span no edge, so that
no additional edge can be inserted. -/
def HasMaximalMatching (k : ℕ) : Prop :=
  ∃ f : Fin k × Bool ↪ V, (∀ i, G.Adj (f (i,false)) (f (i,true))) ∧
    ∀ u ∉ Graffiti326.support f, ∀ v ∉ Graffiti326.support f, ¬G.Adj u v

def minMaximalMatching : ℕ := sInf {k | HasMaximalMatching G k}

private theorem minimum_attained : HasMaximalMatching G (minMaximalMatching G) := by
  obtain ⟨f,edges⟩ := Graffiti326.matchingNumber_attained G
  have ex : {k | HasMaximalMatching G k}.Nonempty := by
    refine ⟨_,f,edges,?_⟩
    intro u hu v hv e
    have impossible := Graffiti326.matchingNumber_upper (Graffiti326.matching_extend edges hu hv e)
    omega
  exact Nat.sInf_mem ex

omit [Fintype V] in
private theorem no_four (cg : Cograph G) : ¬Graffiti137.InducedPath G 4 := by
  rintro ⟨f,rel⟩
  have edge := cg (f 0) (f 1) (f 2) (f 3)
    ((rel 0 1).mpr (by decide)) ((rel 1 2).mpr (by decide)) ((rel 2 3).mpr (by decide))
    (fun e => (by decide : ¬Graffiti137.Consecutive (0 : Fin 4) 2) ((rel 0 2).mp e))
    (fun e => (by decide : ¬Graffiti137.Consecutive (1 : Fin 4) 3) ((rel 1 3).mp e))
  exact (by decide : ¬Graffiti137.Consecutive (0 : Fin 4) 3) ((rel 0 3).mp edge)

/-- Full adjacency between the two sides ensures that an independent
dominating set of the selected nonempty side dominates the whole join. -/
theorem dominated_side {S : Finset V} (non : S.Nonempty)
    (cross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y) :
    ∃ D : Finset V, D ⊆ S ∧ Independent G D ∧ Dominates G D := by
  classical
  let fam := univ.filter (fun D : Finset V => D ⊆ S ∧ Independent G D)
  have seed : ∅ ∈ fam := by simp [fam,Independent]
  obtain ⟨D,hd,largest⟩ := exists_max_image fam card ⟨_,seed⟩
  obtain ⟨sub,ind⟩ := (mem_filter.mp hd).2
  have within (x : V) (xs : x ∈ S) : x ∈ D ∨ ∃ y ∈ D, G.Adj x y := by
    by_contra! bad
    have bigger : Independent G (insert x D) := by
      intro a ha b hb
      rcases mem_insert.mp ha with rfl | ma <;> rcases mem_insert.mp hb with rfl | mb
      · exact G.loopless _
      · exact bad.2 _ mb
      · exact fun e => bad.2 _ ma e.symm
      · exact ind _ ma _ mb
    have bound := largest _ (mem_filter.mpr ⟨mem_univ _,insert_subset xs sub,bigger⟩)
    simp [card_insert_of_not_mem bad.1] at bound
  obtain ⟨s,hs⟩ := non
  have hasD : D.Nonempty := by
    rcases within s hs with h | ⟨y,hy,_⟩
    · exact ⟨s,h⟩
    · exact ⟨y,hy⟩
  obtain ⟨y,hy⟩ := hasD
  refine ⟨D,sub,ind,fun x => ?_⟩
  by_cases xs : x ∈ S
  · exact within x xs
  · exact Or.inr ⟨y,hy,(cross y (sub hy) x xs).symm⟩

private theorem count_covered {k : ℕ} {f : Fin k × Bool ↪ V}
    (edges : ∀ i, G.Adj (f (i,false)) (f (i,true)))
    {D : Finset V} (ind : Independent G D) (sub : D ⊆ Graffiti326.support f) :
    D.card ≤ k := by
  classical
  have coverage (x : ↥D) := (Graffiti326.mem_support f).mp (sub x.property)
  choose index side eq using coverage
  have inj : Function.Injective index := by
    intro x y same
    by_contra ne
    have neq : x.val ≠ y.val := fun e => ne (Subtype.ext e)
    have opposite : side x ≠ side y := by
      intro he
      exact neq ((eq x).symm.trans (by rw [same,he,eq]))
    have hxy : G.Adj x.val y.val := by
      rw [← eq x,← eq y,← same]
      cases hx : side x <;> cases hy : side y
      · exact (opposite (hx.trans hy.symm)).elim
      · exact edges _
      · exact (edges _).symm
      · exact (opposite (hx.trans hy.symm)).elim
    exact ind _ x.property _ y.property hxy
  simpa using Fintype.card_le_of_injective index inj

theorem join_bound {S : Finset V} (non : S.Nonempty) (other : Sᶜ.Nonempty)
    (cross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y) :
    independentDomination G ≤ minMaximalMatching G := by
  classical
  obtain ⟨f,edges,maximal⟩ := minimum_attained G
  have lift (T : Finset V) (nt : T.Nonempty) (sub : T ⊆ Graffiti326.support f)
      (cut : ∀ x ∈ T, ∀ y ∉ T, G.Adj x y) : independentDomination G ≤ minMaximalMatching G := by
    obtain ⟨D,dt,ind,dom⟩ := dominated_side G nt cut
    exact (Nat.sInf_le (s := {n | ∃ A : Finset V, Independent G A ∧ Dominates G A ∧ A.card = n})
      ⟨D,ind,dom,rfl⟩).trans (count_covered G edges ind (dt.trans sub))
  by_cases sub : S ⊆ Graffiti326.support f
  · exact lift S non sub cross
  · obtain ⟨x,xs,xout⟩ := Finset.not_subset.mp sub
    apply lift Sᶜ other
    · intro y hy
      exact Classical.byContradiction (fun yout =>
        maximal x xout y yout (cross x xs y (mem_compl.mp hy)))
    · intro y hy z hz
      exact (cross z (by simpa using hz) y (mem_compl.mp hy)).symm

theorem cograph_join (h : G.Connected) (non : 2 ≤ Fintype.card V) (cg : Cograph G) :
    ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧ ∀ x ∈ S, ∀ y ∉ S, G.Adj x y := by
  classical
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp non
  have fail : ¬Gᶜ.Preconnected := fun pre =>
    no_four G cg (Graffiti137.four_of_connected_complement G h ⟨pre⟩)
  change ¬∀ a b, Gᶜ.Reachable a b at fail
  push_neg at fail
  obtain ⟨a,b,apart⟩ := fail
  let S := univ.filter (fun v => Gᶜ.Reachable a v)
  have mem (x : V) : x ∈ S ↔ Gᶜ.Reachable a x := by simp [S]
  refine ⟨S,⟨a,(mem a).mpr .rfl⟩,⟨b,mem_compl.mpr ((mem b).not.mpr apart)⟩,?_⟩
  intro x hx y hy
  by_contra no
  have ne : x ≠ y := fun eq => hy (eq ▸ hx)
  exact hy ((mem y).mpr (((mem x).mp hx).trans (((G.compl_adj x y).mpr ⟨ne,no⟩).reachable)))

theorem survivor_line378 (h : G.Connected) (non : 2 ≤ Fintype.card V) (cg : Cograph G) :
    independentDomination G ≤ minMaximalMatching G := by
  obtain ⟨S,hs,hc,cross⟩ := cograph_join G h non cg
  exact join_bound G hs hc cross

#print axioms join_bound
#print axioms survivor_line378
end
end AutoGraphForge378

/-!
# Written on the Wall II 372

Jonas J. Gebendorfer resolved the defined domain in October 2026.
The proof below uses a two-coloring after deleting the unique edge between
the two covering paths to treat equality in the degree-incidence bound.
-/

namespace Graffiti372

open Finset SimpleGraph
open scoped BigOperators
open Classical

noncomputable section

variable {V : Type*} [Fintype V]

def TotalDominates (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v, ∃ w ∈ D, G.Adj v w

def IsVertexCover (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ∈ C ∨ v ∈ C

def totalDominationNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}

def vertexCoverNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ C : Finset V, IsVertexCover G C ∧ C.card = k}

/-- A cover by p ordered nonempty vertex-disjoint paths. The equivalence
gives every vertex exactly one pair consisting of its path and its position.
Path i has (lengths i + 1) vertices and each consecutive pair is an edge. -/
def HasPathCover (G : SimpleGraph V) (p : ℕ) : Prop :=
  ∃ lengths : Fin p → ℕ, ∃ coord : (Σ i : Fin p, Fin (lengths i + 1)) ≃ V,
    ∀ i (j : Fin (lengths i)), G.Adj (coord ⟨i,j.castSucc⟩) (coord ⟨i,j.succ⟩)

def pathCoverNumber (G : SimpleGraph V) : ℕ :=
  sInf {p | HasPathCover G p}

theorem singletonPathCover (G : SimpleGraph V) : HasPathCover G (Fintype.card V) := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · exact (Equiv.sigmaUnique (Fin (Fintype.card V)) (fun _ => Fin 1)).trans (Fintype.equivFin V).symm
  · intro i j
    exact Fin.elim0 j

theorem minPathCover (G : SimpleGraph V) : HasPathCover G (pathCoverNumber G) := by
  have h : {p | HasPathCover G p}.Nonempty := ⟨_, singletonPathCover G⟩
  exact Nat.sInf_mem h

theorem minTotalDominates {G : SimpleGraph V} (hT : G.IsTree) (hn : 2 < Fintype.card V) :
    ∃ D : Finset V, TotalDominates G D ∧ D.card = totalDominationNumber G := by
  have ht : {k | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}.Nonempty := by
    refine ⟨_, univ, ?_, rfl⟩
    intro v
    have hV : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    letI := hV
    obtain ⟨w,hw⟩ := exists_ne v
    obtain ⟨p⟩ := hT.isConnected v w
    exact ⟨p.snd, mem_univ _, p.adj_snd (Walk.not_nil_of_ne hw.symm)⟩
  exact Nat.sInf_mem ht

theorem minVertexCover (G : SimpleGraph V) :
    ∃ C : Finset V, IsVertexCover G C ∧ C.card = vertexCoverNumber G := by
  have h : {k | ∃ C : Finset V, IsVertexCover G C ∧ C.card = k}.Nonempty :=
    ⟨_,univ,(fun _ _ _ => Or.inl (mem_univ _)),rfl⟩
  exact Nat.sInf_mem h

omit [Fintype V] in
theorem vertexCoverNumber_le_card {G : SimpleGraph V} {C : Finset V} (hC : IsVertexCover G C) :
    vertexCoverNumber G ≤ C.card :=
  Nat.sInf_le ⟨C,hC,rfl⟩

private theorem edge_cover_large_path_count {G : SimpleGraph V} (hT : G.IsTree)
    {D : Finset V} (hD : TotalDominates G D) :
    ∃ C : Finset V, IsVertexCover G C ∧ C.card ≤ 2 * D.card := by
  choose f hf hAdj using hD
  let U := Dᶜ
  let E := U.image (fun v => s(v, f v))
  have hE : E ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨v,_,rfl⟩ := mem_image.mp he
    exact mem_edgeFinset.mpr ((mem_edgeSet G).mpr (hAdj v))
  have hcard : E.card = U.card := by
    apply Finset.card_image_of_injOn
    intro v hv w _ he
    rcases Sym2.eq_iff.mp he with h | h
    · exact h.1
    · exact (mem_compl.mp hv (h.1.symm ▸ hf w)).elim
  let R := G.edgeFinset \ E
  have hR : R.card ≤ D.card := by
    have hm := hT.card_edgeFinset
    have hU : U.card + D.card = Fintype.card V := Finset.card_compl_add_card D
    have hp : R.card + E.card = G.edgeFinset.card := Finset.card_sdiff_add_card_eq_card hE
    omega
  let endpoint (e : Sym2 V) : V :=
    Classical.choose (show ∃ v, v ∈ e from Sym2.ind (fun u v => ⟨u, by simp⟩) e)
  have hEndpoint (e : Sym2 V) : endpoint e ∈ e := Classical.choose_spec _
  let C := D ∪ R.image endpoint
  refine ⟨C, ?_, ?_⟩
  · intro u v h
    by_cases hu : u ∈ D
    · exact Or.inl (mem_union_left _ hu)
    by_cases hv : v ∈ D
    · exact Or.inr (mem_union_left _ hv)
    have hr : s(u,v) ∈ R := by
      refine mem_sdiff.mpr ⟨mem_edgeFinset.mpr ((mem_edgeSet G).mpr h), ?_⟩
      intro he
      obtain ⟨w,_,hw⟩ := mem_image.mp he
      rcases Sym2.eq_iff.mp hw with h' | h'
      · exact hv (h'.2 ▸ hf w)
      · exact hu (h'.2 ▸ hf w)
    have hE : endpoint s(u,v) ∈ C := mem_union_right _ (mem_image_of_mem _ hr)
    have hh := hEndpoint s(u,v)
    simp only [Sym2.mem_iff] at hh
    rcases hh with h' | h'
    · exact Or.inl (h' ▸ hE)
    · exact Or.inr (h' ▸ hE)
  · have hc : C.card ≤ D.card + (R.image endpoint).card := card_union_le _ _
    have hi := card_image_le (s := R) (f := endpoint)
    omega

section PathEdges

variable {p : ℕ} {lengths : Fin p → ℕ}
variable (coord : (Σ i : Fin p, Fin (lengths i + 1)) ≃ V)

private def indexOf (v : V) : Fin p := (coord.symm v).1
private def position (v : V) : ℕ := (coord.symm v).2.val

private def pathEdge (j : Σ i : Fin p, Fin (lengths i)) : Sym2 V :=
  s(coord ⟨j.1,j.2.castSucc⟩, coord ⟨j.1,j.2.succ⟩)

omit [Fintype V] in
private theorem pathEdge_injective : Function.Injective (pathEdge coord) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ h
  simp only [pathEdge, Sym2.eq_iff, Equiv.apply_eq_iff_eq] at h
  rcases h with h | h
  · have hi : i = k := congrArg Sigma.fst h.1
    subst k
    have hj := congrArg (fun x : Σ i : Fin p, Fin (lengths i + 1) => x.2.val) h.1
    exact Sigma.ext rfl (heq_of_eq (Fin.ext hj))
  · have h₁ := congrArg (fun x : Σ i : Fin p, Fin (lengths i + 1) => x.2.val) h.1
    have h₂ := congrArg (fun x : Σ i : Fin p, Fin (lengths i + 1) => x.2.val) h.2
    change j.val = l.val + 1 at h₁
    change j.val + 1 = l.val at h₂
    omega

private def pathEdges : Finset (Sym2 V) :=
  univ.image (pathEdge coord)

private def pathForest : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (pathEdges coord : Set (Sym2 V))

private theorem pathEdges_subset {G : SimpleGraph V}
    (hG : ∀ i (j : Fin (lengths i)), G.Adj (coord ⟨i,j.castSucc⟩) (coord ⟨i,j.succ⟩)) :
    pathEdges coord ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨⟨i,j⟩,_,rfl⟩ := mem_image.mp he
  exact mem_edgeFinset.mpr ((mem_edgeSet G).mpr (hG i j))

private theorem pathEdges_card :
    (pathEdges coord).card + p = Fintype.card V := by
  have he := Fintype.card_congr coord
  rw [Fintype.card_sigma] at he
  simp only [Fintype.card_fin] at he
  unfold pathEdges
  rw [card_image_of_injective _ (pathEdge_injective coord), card_univ, Fintype.card_sigma]
  simpa [sum_add_distrib, sum_const, nsmul_eq_mul] using he

omit [Fintype V] in
private theorem pathForest_adj_iff (u v : V) :
    (pathForest coord).Adj u v ↔ s(u,v) ∈ pathEdges coord := by
  rw [pathForest, fromEdgeSet_adj]
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  obtain ⟨⟨i,j⟩,_,hj⟩ := mem_image.mp h
  intro hEq
  have hd : (pathEdge coord ⟨i,j⟩).IsDiag := by rw [hj,hEq]; simp
  have hh : coord ⟨i,j.castSucc⟩ = coord ⟨i,j.succ⟩ := by simpa [pathEdge] using hd
  have hz := congrArg (fun a : Σ i : Fin p, Fin (lengths i + 1) => a.2.val) (coord.injective hh)
  change j.val = j.val + 1 at hz
  omega

omit [Fintype V] in
private theorem position_at (a : Σ i : Fin p, Fin (lengths i + 1)) :
    position coord (coord a) = a.2.val :=
  congrArg (fun a : Σ i : Fin p, Fin (lengths i + 1) => a.2.val) (coord.symm_apply_apply a)

omit [Fintype V] in
private theorem pathForest_coords {u v : V} (h : (pathForest coord).Adj u v) :
    indexOf coord u = indexOf coord v ∧
      (position coord u + 1 = position coord v ∨ position coord v + 1 = position coord u) := by
  obtain ⟨⟨i,j⟩,_,he⟩ := mem_image.mp ((pathForest_adj_iff coord u v).mp h)
  simp only [pathEdge, Sym2.eq_iff] at he
  rcases he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · rw [← h₁, ← h₂]
    exact ⟨by simp [indexOf], Or.inl (by rw [position_at, position_at]; rfl)⟩
  · rw [← h₁, ← h₂]
    exact ⟨by simp [indexOf], Or.inr (by rw [position_at, position_at]; rfl)⟩

private theorem pathForest_degree_le (v : V) : (pathForest coord).degree v ≤ 2 := by
  let N := (pathForest coord).neighborFinset v
  let f := position coord
  have hi : Set.InjOn f (N : Set V) := by
    intro u hu w hw hwEq
    have h1 := (pathForest_coords coord ((mem_neighborFinset _ _ _).mp hu)).1
    have h2 := (pathForest_coords coord ((mem_neighborFinset _ _ _).mp hw)).1
    obtain ⟨⟨i,j⟩,rfl⟩ := coord.surjective u
    obtain ⟨⟨k,l⟩,rfl⟩ := coord.surjective w
    have he : i = k := by
      have hh := h1.symm.trans h2
      simpa only [indexOf, Equiv.symm_apply_apply] using hh
    subst k
    have hj : j.val = l.val := by
      simpa only [f, position_at] using hwEq
    exact congrArg coord (Sigma.ext rfl (heq_of_eq (Fin.ext hj)))
  have hs : N.image f ⊆ {position coord v - 1, position coord v + 1} := by
    intro k hk
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hk
    have h := (pathForest_coords coord ((mem_neighborFinset _ _ _).mp hw)).2
    simp only [mem_insert, mem_singleton]
    change position coord w = _ ∨ position coord w = _
    omega
  have hN : (N.image f).card = N.card := Finset.card_image_of_injOn hi
  change N.card ≤ 2
  rw [← hN]
  exact (Finset.card_le_card hs).trans card_le_two

omit [Fintype V] in
private def pathCoordHom {G : SimpleGraph V}
    (hG : ∀ i (j : Fin (lengths i)), G.Adj (coord ⟨i,j.castSucc⟩) (coord ⟨i,j.succ⟩))
    (i : Fin p) : pathGraph (lengths i + 1) →g G where
  toFun j := coord ⟨i,j⟩
  map_rel' := by
    intro a b hab
    rw [pathGraph_adj] at hab
    have hforward (a b : Fin (lengths i + 1)) (hab : a.val + 1 = b.val) :
        G.Adj (coord ⟨i,a⟩) (coord ⟨i,b⟩) := by
      let j : Fin (lengths i) := ⟨a.val, by have := b.isLt; omega⟩
      have ha : j.castSucc = a := Fin.ext rfl
      have hb : j.succ = b := Fin.ext hab
      rw [← ha, ← hb]
      exact hG i j
    exact hab.elim (hforward a b) (fun h => (hforward b a h).symm)

omit [Fintype V] in
private theorem pathCoordHom_injective {G : SimpleGraph V}
    (hG : ∀ i (j : Fin (lengths i)), G.Adj (coord ⟨i,j.castSucc⟩) (coord ⟨i,j.succ⟩))
    (i : Fin p) : Function.Injective (pathCoordHom coord hG i) := by
  intro a b h
  have he : (⟨i,a⟩ : Σ i, Fin (lengths i + 1)) = ⟨i,b⟩ := coord.injective h
  have hv := congrArg (fun a : Σ i, Fin (lengths i + 1) => a.2.val) he
  exact Fin.ext hv

omit [Fintype V] in
private theorem pathForest_same_index_connected {u v : V}
    (h : indexOf coord u = indexOf coord v) : (pathForest coord).Reachable u v := by
  obtain ⟨⟨i,j⟩,rfl⟩ := coord.surjective u
  obtain ⟨⟨k,l⟩,rfl⟩ := coord.surjective v
  have hik : i = k := by simpa only [indexOf, Equiv.symm_apply_apply] using h
  subst k
  have hPath (i : Fin p) (j : Fin (lengths i)) :
      (pathForest coord).Adj (coord ⟨i,j.castSucc⟩) (coord ⟨i,j.succ⟩) := by
    apply (pathForest_adj_iff coord _ _).mpr
    exact mem_image_of_mem (pathEdge coord) (mem_univ (⟨i,j⟩ : Σ i, Fin (lengths i)))
  obtain ⟨w⟩ := pathGraph_preconnected (lengths i + 1) j l
  exact (w.map (pathCoordHom coord hPath i)).reachable

omit [Fintype V] in
private theorem pathForest_coloring (off : Fin p → ℕ) {u v : V}
    (ha : (pathForest coord).Adj u v) :
    (position coord u + off (indexOf coord u)) % 2 ≠
      (position coord v + off (indexOf coord v)) % 2 := by
  obtain ⟨hi,hp⟩ := pathForest_coords coord ha
  rw [hi]
  omega

end PathEdges

/-- The same path cover expressed using Mathlib's simple paths. Every vertex
belongs to the support of exactly one path. -/
def HasWalkPathCover (G : SimpleGraph V) (p : ℕ) : Prop :=
  ∃ start finish : Fin p → V, ∃ paths : ∀ i, G.Path (start i) (finish i),
    ∀ v, ∃! i, v ∈ (paths i).val.support

omit [Fintype V] in
private theorem pathWalk_contains {n : ℕ} {a b : Fin n} (w : (pathGraph n).Walk a b)
    (k : Fin n) (ha : a.val ≤ k.val) (hb : k.val ≤ b.val) : k ∈ w.support := by
  induction w with
  | @nil v =>
    have h : k = v := Fin.ext (by omega)
    simp [h]
  | @cons u x v h w ih =>
    rw [Walk.support_cons, List.mem_cons]
    by_cases hx : k = u
    · exact Or.inl hx
    · have hne : k.val ≠ u.val := fun h' => hx (Fin.ext h')
      have h := pathGraph_adj.mp h
      exact Or.inr (ih (by omega) hb)

omit [Fintype V] in
theorem hasPathCover_iff_hasWalkPathCover (G : SimpleGraph V) (p : ℕ) :
    HasPathCover G p ↔ HasWalkPathCover G p := by
  constructor
  · rintro ⟨lengths,coord,hG⟩
    let path (i : Fin p) : (pathGraph (lengths i + 1)).Path 0 (Fin.last (lengths i)) :=
      ((pathGraph_preconnected (lengths i + 1) _ _).some).toPath
    let f := pathCoordHom coord hG
    let paths (i : Fin p) := (path i).map (f i) (pathCoordHom_injective coord hG i)
    have hMem (i : Fin p) (v : V) :
        v ∈ (paths i).val.support ↔ ∃ j, coord ⟨i,j⟩ = v := by
      change v ∈ ((path i).val.map (f i)).support ↔ _
      rw [Walk.support_map,List.mem_map]
      constructor
      · rintro ⟨j,_,hj⟩
        exact ⟨j,hj⟩
      · rintro ⟨j,hj⟩
        have hj' : j.val ≤ (Fin.last (lengths i)).val := Nat.le_of_lt_succ j.isLt
        exact ⟨j,pathWalk_contains (path i).val j (Nat.zero_le _) hj',hj⟩
    refine ⟨fun i => f i 0,fun i => f i (Fin.last (lengths i)),paths,?_⟩
    intro v
    obtain ⟨⟨i,j⟩,rfl⟩ := coord.surjective v
    refine ⟨i,(hMem _ _).mpr ⟨j,rfl⟩,?_⟩
    intro k hk
    obtain ⟨l,hl⟩ := (hMem _ _).mp hk
    exact congrArg Sigma.fst (coord.injective hl)
  · rintro ⟨start,finish,paths,hMem⟩
    let lengths (i : Fin p) := (paths i).val.length
    let f (u : Σ i : Fin p, Fin (lengths i + 1)) : V :=
      (paths u.1).val.getVert u.2.val
    have hInj : Function.Injective f := by
      rintro ⟨i,j⟩ ⟨k,l⟩ h
      have h₁ : f ⟨i,j⟩ ∈ (paths i).val.support := Walk.getVert_mem_support _ _
      have h₂ : f ⟨i,j⟩ ∈ (paths k).val.support := h.symm ▸ Walk.getVert_mem_support _ _
      have hi : i = k := (hMem _).unique h₁ h₂
      subst k
      have hVal : j.val = l.val := (paths i).property.getVert_injOn
        (Nat.le_of_lt_succ j.isLt) (Nat.le_of_lt_succ l.isLt) h
      exact Sigma.ext rfl (heq_of_eq (Fin.ext hVal))
    have hSurj : Function.Surjective f := by
      intro v
      obtain ⟨i,hi,_⟩ := hMem v
      obtain ⟨j,hj,hj'⟩ := Walk.mem_support_iff_exists_getVert.mp hi
      exact ⟨⟨i,⟨j,Nat.lt_succ_of_le hj'⟩⟩,hj⟩
    refine ⟨lengths,Equiv.ofBijective f ⟨hInj,hSurj⟩,?_⟩
    intro i j
    exact (paths i).val.adj_getVert_succ j.isLt

omit [Fintype V] in
theorem pathCoverNumber_eq_walk (G : SimpleGraph V) :
    pathCoverNumber G = sInf {p | HasWalkPathCover G p} := by
  unfold pathCoverNumber
  congr 1
  ext p
  exact hasPathCover_iff_hasWalkPathCover G p


section TwoPaths

omit [Fintype V] in
private def Bicolors (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → (u ∈ A ↔ v ∉ A)

omit [Fintype V] in
private def IsAddedEdge (G H : SimpleGraph V) (s t : V) : Prop :=
  s ≠ t ∧ ¬ H.Adj s t ∧ ∀ u v, G.Adj u v ↔ H.Adj u v ∨ s(u,v) = s(s,t)

private def neighborCount (G : SimpleGraph V) (S : Finset V) (v : V) : ℕ :=
  (S.filter (G.Adj v)).card

private theorem neighborCount_univ (G : SimpleGraph V) (v : V) :
    neighborCount G univ v = G.degree v := by
  rw [neighborCount, degree, neighborFinset_eq_filter]

omit [Fintype V] in
private theorem sum_neighborCount_comm (G : SimpleGraph V) (A B : Finset V) :
    (∑ v ∈ A, neighborCount G B v) = ∑ w ∈ B, neighborCount G A w := by
  have hfilter (S : Finset V) (v : V) :
      neighborCount G S v = ∑ w ∈ S, if G.Adj v w then 1 else 0 :=
    (Finset.sum_boole (α := ℕ) (G.Adj v) S).symm
  simp_rw [hfilter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  exact Finset.sum_congr rfl fun v _ => by simp only [G.adj_comm v w]

omit [Fintype V] in
private theorem neighborCount_add_at {G H : SimpleGraph V} {u w : V}
    (hs : ∀ x, G.Adj u x ↔ H.Adj u x ∨ x = w) (hn : ¬ H.Adj u w)
    (S : Finset V) :
    neighborCount G S u = neighborCount H S u + (if w ∈ S then 1 else 0) := by
  unfold neighborCount
  by_cases hw : w ∈ S
  · have he : S.filter (G.Adj u) = insert w (S.filter (H.Adj u)) := by
      ext x
      simp only [mem_filter, mem_insert, hs]
      constructor
      · rintro ⟨h₁,h₂ | rfl⟩
        · exact Or.inr ⟨h₁,h₂⟩
        · exact Or.inl rfl
      · rintro (rfl | h)
        · exact ⟨hw, Or.inr rfl⟩
        · exact ⟨h.1, Or.inl h.2⟩
    rw [he, if_pos hw, card_insert_of_not_mem]
    simp [hn]
  · have he : S.filter (G.Adj u) = S.filter (H.Adj u) := by
      ext x
      simp only [mem_filter, hs]
      constructor
      · rintro ⟨h₁,h₂ | rfl⟩
        · exact ⟨h₁,h₂⟩
        · exact (hw h₁).elim
      · exact fun h => ⟨h.1,Or.inl h.2⟩
    rw [he, if_neg hw, add_zero]

omit [Fintype V] in
private theorem neighborCount_add_edge {G H : SimpleGraph V} {s t : V}
    (he : IsAddedEdge G H s t) (S : Finset V) (v : V) :
    neighborCount G S v = neighborCount H S v +
      (if v = s ∧ t ∈ S then 1 else 0) + (if v = t ∧ s ∈ S then 1 else 0) := by
  obtain ⟨hst,hn,he⟩ := he
  by_cases hs : v = s
  · subst v
    have hRel (x : V) : G.Adj s x ↔ H.Adj s x ∨ x = t := by
      rw [he, Sym2.eq_iff]
      simp [hst]
    rw [neighborCount_add_at hRel hn]
    simp [hst]
  by_cases ht : v = t
  · subst v
    have hRel (x : V) : G.Adj t x ↔ H.Adj t x ∨ x = s := by
      rw [he, Sym2.eq_iff]
      simp [hst.symm]
    rw [neighborCount_add_at hRel (fun h => hn h.symm)]
    simp [hst.symm]
  have hRel (x : V) : G.Adj v x ↔ H.Adj v x := by
    rw [he, Sym2.eq_iff]
    simp [hs, ht]
  simp only [neighborCount, hs, ht, false_and, if_false, add_zero]
  exact congrArg Finset.card (filter_congr (fun x _ => hRel x))

private theorem sum_degrees_add_edge {G H : SimpleGraph V} {s t : V}
    (he : IsAddedEdge G H s t) (D : Finset V) :
    (∑ v ∈ D, G.degree v) = (∑ v ∈ D, H.degree v) +
      (if s ∈ D then 1 else 0) + (if t ∈ D then 1 else 0) := by
  have hh (v : V) := neighborCount_add_edge he univ v
  simp only [neighborCount_univ, mem_univ, and_true] at hh
  simp_rw [hh, sum_add_distrib, sum_ite_eq']

omit [Fintype V] in
private theorem neighborCount_of_total {G : SimpleGraph V} {D : Finset V}
    (hD : TotalDominates G D) (v : V) : 1 ≤ neighborCount G D v := by
  obtain ⟨w,hD,hw⟩ := hD v
  exact card_pos.mpr ⟨w,mem_filter.mpr ⟨hD,hw⟩⟩

private theorem bicolors_compl {G : SimpleGraph V} {A : Finset V} (h : Bicolors G A) :
    Bicolors G Aᶜ := by
  intro u v huv
  simp only [mem_compl, not_not]
  have h' := h huv
  tauto

private theorem small_cover_of_bicolors {G : SimpleGraph V} {A : Finset V}
    (h : Bicolors G A) (k : ℕ) (hk : Fintype.card V ≤ 2*k+1) :
    ∃ C : Finset V, IsVertexCover G C ∧ C.card ≤ k := by
  have hc : Aᶜ.card + A.card = Fintype.card V := card_compl_add_card A
  by_cases hA : A.card ≤ k
  · refine ⟨A,?_,hA⟩
    intro u v huv
    have h' := h huv
    tauto
  · refine ⟨Aᶜ,?_,by omega⟩
    intro u v huv
    simp only [mem_compl]
    have h' := h huv
    tauto

private theorem neighborCount_opposite {H : SimpleGraph V} {A : Finset V}
    (hA : Bicolors H A) (S : Finset V) {v : V} (hv : v ∈ A) :
    neighborCount H (S ∩ Aᶜ) v = neighborCount H S v := by
  unfold neighborCount
  congr 1
  ext w
  simp only [mem_filter, mem_inter, mem_compl]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,(hA h.2).mp hv⟩,h.2⟩⟩

private theorem neighborCount_on_opposite {H : SimpleGraph V} {A : Finset V}
    (hA : Bicolors H A) {v : V} (hv : v ∈ Aᶜ) :
    neighborCount H A v = H.degree v := by
  have h := neighborCount_opposite (bicolors_compl hA) univ hv
  simpa only [compl_compl, univ_inter, neighborCount_univ] using h

private theorem critical_cover {G H : SimpleGraph V} {s t : V}
    (he : IsAddedEdge G H s t) {D A : Finset V} (hs : s ∈ D) (ht : t ∈ D)
    (hOne : ∀ v, neighborCount G D v = 1) (hTwo : ∀ v ∈ D, H.degree v = 2)
    (hA : Bicolors H A) (hsA : s ∈ A) (htA : t ∈ A) :
    IsVertexCover G A ∧ A.card = D.card := by
  let E : Finset V := {s,t}
  let B := Aᶜ
  let X := D ∩ A
  let Y := D ∩ B
  have hEc : E.card = 2 := by simp [E,he.1]
  have hEA : E ⊆ A := by simpa only [E, insert_subset_iff, singleton_subset_iff] using And.intro hsA htA
  have hEX : E ⊆ X := by
    apply subset_inter
    · simpa only [E, insert_subset_iff, singleton_subset_iff] using And.intro hs ht
    · exact hEA
  have hCount (v : V) : neighborCount H D v = if v ∉ E then 1 else 0 := by
    have hh := neighborCount_add_edge he D v
    rw [hOne v] at hh
    by_cases hv : v = s
    · subst v
      simp only [true_and, hs, ht, if_true, he.1, false_and, if_false, add_zero] at hh
      simp only [E,mem_insert, mem_singleton, true_or, not_true, if_false]
      omega
    by_cases hv' : v = t
    · subst v
      simp only [true_and, hs, ht, if_true, he.1.symm, false_and, if_false, add_zero] at hh
      simp only [E,mem_insert, mem_singleton, or_true, not_true, if_false]
      omega
    · simp [E,hv,hv'] at hh ⊢
      exact hh.symm
  have hX (v : V) (hv : v ∈ A) : neighborCount H Y v = if v ∉ E then 1 else 0 :=
    (neighborCount_opposite hA D hv).trans (hCount v)
  have hY (v : V) (hv : v ∈ B) : neighborCount H X v = 1 := by
    have h := neighborCount_opposite (bicolors_compl hA) D hv
    rw [compl_compl] at h
    rw [h,hCount]
    exact if_pos fun hv' => (mem_compl.mp hv) (hEA hv')
  have hsSum (S : Finset V) : (∑ v ∈ S, if v ∉ E then 1 else 0) = (S \ E).card := by
    have hFilter : S.filter (fun v => v ∉ E) = S \ E := by
      ext v
      simp
    simp only [Finset.sum_boole, hFilter, Nat.cast_id]
  have hXY : X.card = Y.card + 2 := by
    have hx : (∑ v ∈ X, neighborCount H Y v) = (X \ E).card := by
      rw [← hsSum X]
      exact Finset.sum_congr rfl (fun v hv => hX v (mem_inter.mp hv).2)
    have hy : (∑ v ∈ Y, neighborCount H X v) = Y.card := by
      calc
        _ = ∑ _v ∈ Y, (1 : ℕ) := Finset.sum_congr rfl (fun v hv => hY v (mem_inter.mp hv).2)
        _ = _ := by simp
    have hCross := hx.symm.trans ((sum_neighborCount_comm H X Y).trans hy)
    calc
      X.card = (X \ E).card + E.card := (card_sdiff_add_card_eq_card hEX).symm
      _ = Y.card + 2 := by rw [hCross, hEc]
  have hAY : A.card = 2 * Y.card + 2 := by
    have hCross := sum_neighborCount_comm H A Y
    rw [Finset.sum_congr rfl hX, hsSum A] at hCross
    have hAll (v : V) (hv : v ∈ Y) : neighborCount H A v = 2 :=
      (neighborCount_on_opposite hA (mem_inter.mp hv).2).trans
        (hTwo v (mem_inter.mp hv).1)
    rw [Finset.sum_congr rfl hAll, sum_const, Nat.nsmul_eq_mul] at hCross
    have hC := card_sdiff_add_card_eq_card hEA
    omega
  have hParts : X.card + Y.card = D.card := by
    have hY' : Y = D \ A := by
      ext v
      simp [Y,B]
    rw [hY']
    exact card_inter_add_card_sdiff D A
  refine ⟨?_,by omega⟩
  intro u v huv
  rcases (he.2.2 _ _).mp huv with h | h
  · have hh := hA h
    tauto
  · rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl hsA
    · exact Or.inl htA

private theorem cover_of_added_edge {G H : SimpleGraph V} {s t : V}
    (he : IsAddedEdge G H s t) (hdeg : ∀ v, H.degree v ≤ 2)
    {U A : Finset V} (hU : Bicolors G U) (hA : Bicolors H A) (hsA : s ∈ A) (htA : t ∈ A)
    {D : Finset V} (hD : TotalDominates G D) :
    ∃ C : Finset V, IsVertexCover G C ∧ C.card ≤ D.card := by
  by_cases hsmall : Fintype.card V ≤ 2*D.card+1
  · exact small_cover_of_bicolors hU D.card hsmall
  have hL : Fintype.card V ≤ ∑ v, neighborCount G D v := by
    simpa only [sum_const, card_univ, Nat.nsmul_eq_mul, Nat.mul_one] using
      (sum_le_sum (s := (univ : Finset V)) (g := neighborCount G D)
        (f := fun _ => 1) fun v _ => neighborCount_of_total hD v)
  have hMid : (∑ v, neighborCount G D v) = ∑ v ∈ D, G.degree v := by
    rw [sum_neighborCount_comm G univ D]
    simp_rw [neighborCount_univ]
  have hR : (∑ v ∈ D, H.degree v) ≤ 2 * D.card := by
    calc
      _ ≤ ∑ _v ∈ D, (2 : ℕ) := sum_le_sum (fun v _ => hdeg v)
      _ = _ := by simp [Nat.nsmul_eq_mul, Nat.mul_comm]
  have hh := sum_degrees_add_edge he D
  have hTight : s ∈ D ∧ t ∈ D := by
    by_cases hs : s ∈ D <;> by_cases ht : t ∈ D <;> simp [hs,ht] at hh ⊢ <;> omega
  obtain ⟨hs,ht⟩ := hTight
  simp [hs,ht] at hh
  have hOne (v : V) : neighborCount G D v = 1 := by
    by_cases hne : neighborCount G D v = 1
    · exact hne
    have hlt : 1 < neighborCount G D v := lt_of_le_of_ne (neighborCount_of_total hD v) (Ne.symm hne)
    have hsum := sum_lt_sum (s := (univ : Finset V))
      (f := fun _ => 1) (g := neighborCount G D)
      (fun w _ => neighborCount_of_total hD w) ⟨v,mem_univ _,hlt⟩
    simp only [sum_const, card_univ, Nat.nsmul_eq_mul, Nat.mul_one] at hsum
    omega
  have hTwo (v : V) (hv : v ∈ D) : H.degree v = 2 := by
    by_cases hne : H.degree v = 2
    · exact hne
    have hlt : H.degree v < 2 := lt_of_le_of_ne (hdeg v) hne
    have hsum : (∑ w ∈ D, H.degree w) < ∑ _w ∈ D, (2 : ℕ) :=
      sum_lt_sum (fun w _ => hdeg w) ⟨v,hv,hlt⟩
    rw [sum_const,Nat.nsmul_eq_mul] at hsum
    omega
  obtain ⟨hCover,hcard⟩ := critical_cover he hs ht hOne hTwo hA hsA htA
  exact ⟨A,hCover,hcard.le⟩

end TwoPaths

private theorem cover_of_two_paths {G : SimpleGraph V} (hT : G.IsTree)
    (hP : HasPathCover G 2) {D : Finset V} (hD : TotalDominates G D) :
    ∃ C : Finset V, IsVertexCover G C ∧ C.card ≤ D.card := by
  obtain ⟨lengths,coord,hadj⟩ := hP
  let H := pathForest coord
  let R := G.edgeFinset \ pathEdges coord
  have hsub := pathEdges_subset coord hadj
  have hR : R.card = 1 := by
    have hc := pathEdges_card coord
    have hr : R.card + (pathEdges coord).card = G.edgeFinset.card :=
      card_sdiff_add_card_eq_card hsub
    have hg := hT.card_edgeFinset
    omega
  obtain ⟨e,he⟩ := card_eq_one.mp hR
  revert he
  refine Sym2.ind ?_ e
  intro s t he
  have hstR : s(s,t) ∈ R := by rw [he]; exact mem_singleton_self _
  have hstEdge := mem_sdiff.mp hstR
  have hst : G.Adj s t := (mem_edgeSet G).mp (mem_edgeFinset.mp hstEdge.1)
  have hRel (u v : V) : G.Adj u v ↔ H.Adj u v ∨ s(u,v) = s(s,t) := by
    rw [pathForest_adj_iff]
    constructor
    · intro h
      by_cases hp : s(u,v) ∈ pathEdges coord
      · exact Or.inl hp
      · have hR' : s(u,v) ∈ R := mem_sdiff.mpr ⟨mem_edgeFinset.mpr ((mem_edgeSet G).mpr h),hp⟩
        rw [he] at hR'
        exact Or.inr (mem_singleton.mp hR')
    · rintro (hp | hp)
      · exact (mem_edgeSet G).mp (mem_edgeFinset.mp (hsub hp))
      · exact (mem_edgeSet G).mp (mem_edgeFinset.mp (hp.symm ▸ hstEdge.1))
  have hAdded : IsAddedEdge G H s t :=
    ⟨hst.ne,fun h => hstEdge.2 ((pathForest_adj_iff coord _ _).mp h),hRel⟩
  have hIndex : indexOf coord s ≠ indexOf coord t := by
    intro hi
    have hbridge := (isAcyclic_iff_forall_adj_isBridge.mp hT.IsAcyclic) hst
    have hmono : H ≤ G \ SimpleGraph.fromEdgeSet {s(s,t)} := by
      intro u v hv
      refine ⟨(hRel _ _).mpr (Or.inl hv), ?_⟩
      intro hh
      have heq := Set.mem_singleton_iff.mp (fromEdgeSet_adj _ |>.mp hh).1
      have hh' := (pathForest_adj_iff coord _ _).mp hv
      exact hstEdge.2 (heq ▸ hh')
    exact (isBridge_iff.mp hbridge).2 ((pathForest_same_index_connected coord hi).mono hmono)
  let offset (b : ℕ) (i : Fin 2) : ℕ :=
    if i = indexOf coord s then position coord s else position coord t + b
  let colors (b : ℕ) : Finset V :=
    univ.filter (fun v => (position coord v + offset b (indexOf coord v)) % 2 = 0)
  have hs (b : ℕ) : s ∈ colors b := by
    simp only [colors,offset,mem_filter,mem_univ,true_and,if_true]
    omega
  have ht (b : ℕ) : t ∈ colors b ↔ b % 2 = 0 := by
    simp only [colors,offset,mem_filter,mem_univ,true_and,if_neg hIndex.symm]
    omega
  have hA (b : ℕ) : Bicolors H (colors b) := by
    intro u v huv
    have hn := pathForest_coloring coord (offset b) huv
    simp only [colors,mem_filter,mem_univ,true_and]
    omega
  have hU : Bicolors G (colors 1) := by
    intro u v huv
    rcases (hRel _ _).mp huv with h | h
    · exact hA 1 h
    · have hs' := hs 1
      have ht' : t ∉ colors 1 := fun hh => (by decide : ¬1 % 2 = 0) ((ht 1).mp hh)
      rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · simp [hs',ht']
      · simp [hs',ht']
  exact cover_of_added_edge hAdded (pathForest_degree_le coord) hU (hA 0) (hs 0)
    ((ht 0).mpr (by decide)) hD

/-- Cross-multiplied catalogue conjecture on its defined domain. -/
theorem conjecture372_mul (G : SimpleGraph V) (hT : G.IsTree) (hn : 2 < Fintype.card V)
    (hp : 2 ≤ pathCoverNumber G) :
    vertexCoverNumber G ≤ (pathCoverNumber G - 1) * totalDominationNumber G := by
  obtain ⟨D,hD,hcard⟩ := minTotalDominates hT hn
  by_cases hTwo : pathCoverNumber G = 2
  · have hP := minPathCover G
    rw [hTwo] at hP
    obtain ⟨C,hC,hbound⟩ := cover_of_two_paths hT hP hD
    have hh := (vertexCoverNumber_le_card hC).trans hbound
    simpa [hTwo,hcard] using hh
  · obtain ⟨C,hC,hbound⟩ := edge_cover_large_path_count hT hD
    have hh := (vertexCoverNumber_le_card hC).trans hbound
    rw [hcard] at hh
    exact hh.trans (Nat.mul_le_mul_right _ (by omega))

/-- Catalogue conjecture #372 with exact real division and p(T) ≥ 2. -/
theorem conjecture372 (G : SimpleGraph V) (hT : G.IsTree) (hn : 2 < Fintype.card V)
    (hp : 2 ≤ pathCoverNumber G) :
    (vertexCoverNumber G : ℝ) / ((pathCoverNumber G : ℝ) - 1) ≤
      (totalDominationNumber G : ℝ) := by
  have h1 : 1 ≤ pathCoverNumber G := by omega
  have hpos : (0 : ℝ) < ((pathCoverNumber G : ℝ) - 1) := by
    rw [← Nat.cast_one, ← Nat.cast_sub h1, Nat.cast_pos]
    omega
  rw [div_le_iff₀ hpos, ← Nat.cast_one, ← Nat.cast_sub h1, mul_comm, ← Nat.cast_mul, Nat.cast_le]
  exact conjecture372_mul G hT hn hp

#print axioms hasPathCover_iff_hasWalkPathCover
#print axioms conjecture372_mul
#print axioms conjecture372

end
end Graffiti372

/-! Ján Pastorek, normalized survivor line 355, raw rank 371, commit
4d1a8afc99447cacd2328cca20e47b6493e8dbc5. This proof includes disconnected graphs. -/
namespace AutoGraphForge355
open Finset SimpleGraph GraffitiPendant Graffiti432b AutoGraphForge378 Graffiti372
variable {V : Type*} (G : SimpleGraph V)

/-- Every independent dominator covers every edge in a triangle-free cograph. -/
theorem cover_of_independent_dominating (cg : Cograph G)
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj a c)
    {D : Finset V} (ind : Independent G D) (dom : Dominates G D) : IsVertexCover G D := by
  intro x y xy
  by_contra! miss
  obtain ⟨u,ud,xu⟩ := (dom x).resolve_left miss.1
  obtain ⟨v,vd,yv⟩ := (dom y).resolve_left miss.2
  exact ind u ud v vd (cg u x y v xu.symm xy yv (tri u x y xu.symm xy) (tri x y v xy yv))

/-- The source's Colorable 2 unfolds to a homomorphism into the complete graph on Fin 2. -/
theorem survivor_line355 [Fintype V] (n : 2 ≤ Fintype.card V)
    (bip : Nonempty (G →g (⊤ : SimpleGraph (Fin 2)))) (cg : Cograph G) :
    vertexCoverNumber G ≤ independentDomination G := by
  classical
  obtain ⟨c⟩ := bip
  have tri (x y z : V) (a : G.Adj x y) (b : G.Adj y z) (d : G.Adj x z) : False := by
    have i : c x ≠ c y := c.map_adj a
    have j : c y ≠ c z := c.map_adj b
    have k : c x ≠ c z := c.map_adj d
    omega
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp n
  obtain ⟨D,_,ind,dom⟩ := dominated_side G (S := univ) univ_nonempty
    (fun _ _ y hy => (hy (mem_univ y)).elim)
  have ex : {k | ∃ A : Finset V, Independent G A ∧ Dominates G A ∧ A.card = k}.Nonempty :=
    ⟨_,D,ind,dom,rfl⟩
  obtain ⟨A,hi,hd,size⟩ := Nat.sInf_mem ex
  change A.card = independentDomination G at size
  rw [← size]
  exact vertexCoverNumber_le_card (cover_of_independent_dominating G cg tri hi hd)

#print axioms survivor_line355
end AutoGraphForge355
