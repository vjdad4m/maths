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

/-! Ján Pastorek, AutoGraphForge, commit 4d1a8afc99447cacd2328cca20e47b6493e8dbc5.
Normalised list line 379 (raw rank 390), record 35796bcc. -/
namespace AutoGraphForge379
open Finset SimpleGraph Graffiti432b AutoGraphForge378
open Classical
noncomputable section
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- In the subgraph that remains, every component has at most half the
remaining order, rounded up. This includes the empty remaining graph. -/
def Balanced (R : Finset V) : Prop :=
  ∀ x : R, (univ.filter (fun y : R => (G.induce (R : Set V)).Reachable x y)).card ≤ (R.card + 1) / 2

/-- Minimize the number deleted over all balanced remaining graphs. -/
def wellSplitting : ℕ := sInf {k | ∃ R : Finset V, Balanced G R ∧ Rᶜ.card = k}

theorem join_bound {S : Finset V} (hs : S.Nonempty) (hc : Sᶜ.Nonempty)
    (cross : ∀ x ∈ S, ∀ y ∉ S, G.Adj x y) :
    independentDomination G ≤ wellSplitting G := by
  classical
  have empty : Balanced G ∅ := fun x => False.elim (Finset.not_mem_empty x.1 x.2)
  have ex : {k | ∃ R : Finset V, Balanced G R ∧ Rᶜ.card = k}.Nonempty :=
    ⟨_,∅,empty,rfl⟩
  obtain ⟨R,balanced,cost⟩ := Nat.sInf_mem ex
  change Rᶜ.card = wellSplitting G at cost
  have small (T : Finset V) (non : T.Nonempty) (gone : T ⊆ Rᶜ)
      (complete : ∀ x ∈ T, ∀ y ∉ T, G.Adj x y) : independentDomination G ≤ wellSplitting G := by
    obtain ⟨D,sub,ind,dom⟩ := dominated_side G non complete
    rw [← cost]
    exact (Nat.sInf_le (s := {n | ∃ A : Finset V, Independent G A ∧
      GraffitiPendant.Dominates G A ∧ A.card = n}) ⟨D,ind,dom,rfl⟩).trans (card_le_card (sub.trans gone))
  by_cases gone : S ⊆ Rᶜ
  · exact small S hs gone cross
  by_cases gone' : Sᶜ ⊆ Rᶜ
  · apply small Sᶜ hc gone'
    intro x hx y hy
    exact (cross y (by simpa using hy) x (mem_compl.mp hx)).symm
  obtain ⟨x,xs,xr'⟩ := Finset.not_subset.mp gone
  obtain ⟨y,ys',yr'⟩ := Finset.not_subset.mp gone'
  have xr : x ∈ R := by simpa using xr'
  have yr : y ∈ R := by simpa using yr'
  have ys : y ∉ S := mem_compl.mp ys'
  let H := G.induce (R : Set V)
  let a : R := ⟨x,xr⟩
  let b : R := ⟨y,yr⟩
  have ab : H.Adj a b := cross x xs y ys
  have reachable (z : R) : H.Reachable a z := by
    by_cases zs : z.val ∈ S
    · have bz : H.Adj b z := (cross z.val zs y ys).symm
      exact ab.reachable.trans bz.reachable
    · exact (show H.Adj a z from cross x xs z.val zs).reachable
  have all : univ.filter (fun z : R => H.Reachable a z) = univ := by
    ext z
    simp [reachable]
  have bound := balanced a
  change (univ.filter (fun z : R => H.Reachable a z)).card ≤ _ at bound
  rw [all,card_univ,Fintype.card_coe] at bound
  have large : 1 < R.card := one_lt_card_iff.mpr ⟨x,y,xr,yr,fun e => ys (e ▸ xs)⟩
  omega

theorem survivor_line379 (h : G.Connected) (non : 2 ≤ Fintype.card V) (cg : Cograph G) :
    independentDomination G ≤ wellSplitting G := by
  obtain ⟨S,hs,hc,cross⟩ := cograph_join G h non cg
  exact join_bound G hs hc cross

#print axioms join_bound
#print axioms survivor_line379
end
end AutoGraphForge379
