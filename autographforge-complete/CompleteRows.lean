import Mathlib.Data.Multiset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Powerset

/-! Ján Pastorek's normalized AutoGraphForge rows on complete graphs. -/
namespace Graffiti326
open Finset
def support {V : Type*} {k : ℕ} (f : Fin k × Bool ↪ V) : Finset V := univ.map f
theorem mem_support {V : Type*} {k : ℕ} (f : Fin k × Bool ↪ V) {v : V} :
    v ∈ support f ↔ ∃ i b, f (i,b) = v := by
  simp [support, Prod.exists]
end Graffiti326

namespace AutoGraphForge378
open SimpleGraph Graffiti326
variable {V : Type*} (G : SimpleGraph V)
def HasMaximalMatching (k : ℕ) : Prop :=
  ∃ f : Fin k × Bool ↪ V, (∀ i, G.Adj (f (i,false)) (f (i,true))) ∧
    ∀ u ∉ support f, ∀ v ∉ support f, ¬G.Adj u v
noncomputable def minMaximalMatching := sInf {k | HasMaximalMatching G k}
end AutoGraphForge378

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

def feasibleMatchingSizes (G : SimpleGraph V) : Finset ℕ :=
  (range (Fintype.card V / 2+1)).filter (HasMatching G)

theorem matchingSizes_nonempty (G : SimpleGraph V) :
    (feasibleMatchingSizes G).Nonempty := by
  use 0
  simp only [feasibleMatchingSizes, mem_filter, mem_range]
  refine ⟨by omega, ⟨⟨fun p => Fin.elim0 p.1, ?_⟩, ?_⟩⟩
  · intro p; exact Fin.elim0 p.1
  · intro i; exact Fin.elim0 i

def matchingNumber (G : SimpleGraph V) : ℕ :=
  (feasibleMatchingSizes G).max' (matchingSizes_nonempty G)

end
end Graffiti326

namespace CompleteRows
open SimpleGraph Finset AutoGraphForge378 Graffiti326
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
section Rule
variable {U : Type*} [Fintype U] [DecidableEq U] (G : SimpleGraph U) [DecidableRel G.Adj]

def step (k : ℕ) (S : Finset U) : Finset U :=
  S ∪ univ.filter (fun w => w ∉ S ∧ ∃ v ∈ S, G.Adj v w ∧ (G.neighborFinset v \ S).card ≤ k)

def full (k : ℕ) (S : Finset U) : Prop := (step G k)^[Fintype.card U] S = univ
noncomputable def optimum (k : ℕ) (Q : Finset U → Prop) :=
  sInf {r | ∃ S, S.card = r ∧ full G k S ∧ Q S}

def isolateFree (S : Finset U) := ∀ v ∈ S, ∃ w ∈ S, G.Adj v w
def seedConnected (S : Finset U) := (G.induce (S : Set U)).Connected
noncomputable abbrev forcing (k : ℕ) := optimum G k (fun _ => True)
noncomputable abbrev total := optimum G 1 (isolateFree G)
noncomputable abbrev connectedForcing := optimum G 1 (seedConnected G)

/-- At k=1 this is exactly the singleton-neighbor step of the published exporter. -/
theorem step_one (S : Finset U) : step G 1 S =
    S ∪ univ.filter (fun w => w ∉ S ∧ ∃ v ∈ S, G.neighborFinset v \ S = {w}) := by
  ext w
  simp only [step,mem_union,mem_filter,mem_univ,true_and]
  apply or_congr_right
  constructor
  · rintro ⟨out,v,hv,adj,count⟩
    have sub : {w} ⊆ G.neighborFinset v \ S := singleton_subset_iff.mpr
      (mem_sdiff.mpr ⟨(mem_neighborFinset G v w).mpr adj,out⟩)
    exact ⟨out,v,hv,(eq_of_subset_of_card_le sub (by simpa using count)).symm⟩
  · rintro ⟨out,v,hv,one⟩
    have mem : w ∈ G.neighborFinset v \ S := by simp [one]
    exact ⟨out,v,hv,(mem_neighborFinset G v w).mp (mem_sdiff.mp mem).1,by simp [one]⟩
end Rule

def Eulerian {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ ∀ v, Even (G.degree v)

def meanDegree {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] : ℚ :=
  ((∑ v, G.degree v : ℕ) : ℚ) / Fintype.card U

/-- Consecutive indices of a simple cycle in either direction, including its closing edge. -/
def consecutive {k : ℕ} (i j : Fin k) : Prop :=
  i.val+1 = j.val ∨ j.val+1 = i.val ∨
    (i.val=0 ∧ j.val+1=k) ∨ (j.val=0 ∧ i.val+1=k)

/-- The usual forbidden-induced-cycle definition of a chordal graph. -/
def Chordal {U : Type*} (G : SimpleGraph U) : Prop :=
  ∀ k, 4 ≤ k → ¬∃ f : Fin k ↪ U, ∀ i j, G.Adj (f i) (f j) ↔ consecutive i j


abbrev clique (n : ℕ) : SimpleGraph (Fin n) := ⊤

private theorem whites {n : ℕ} (S : Finset (Fin n)) {v} (hv : v ∈ S) :
    (clique n).neighborFinset v \ S = univ \ S := by
  ext w
  simp only [mem_sdiff,mem_neighborFinset,mem_univ,true_and]
  exact ⟨And.right,fun hw => ⟨fun e => hw (e ▸ hv),hw⟩⟩

private theorem minimum_seeds {n k : ℕ} {S : Finset (Fin n)} (good : full (clique n) k S) :
    n-k ≤ S.card := by
  by_contra! low
  have count : (univ \ S).card = n - S.card := by simp [card_sdiff]
  have stuck : step (clique n) k S = S := by
    ext w
    constructor
    · rintro h
      obtain old | added := mem_union.mp h
      · exact old
      obtain ⟨_,v,hv,_,cap⟩ := (mem_filter.mp added).2
      rw [whites S hv,count] at cap
      omega
    · exact mem_union_left _
  have same : (step (clique n) k)^[Fintype.card (Fin n)] S = S :=
    Function.iterate_fixed stuck _
  rw [full,same] at good
  simp [good] at low
  omega

/-- The same optimum holds for any seed restriction accepting all sets of size n-k. -/
theorem clique_forcing {n k : ℕ} (hk : k < n) (Q : Finset (Fin n) → Prop)
    (accept : ∀ S : Finset (Fin n), S.card=n-k → Q S) :
    optimum (clique n) k Q = n-k := by
  obtain ⟨S,_,size⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := n-k) (by simp)
  obtain ⟨v,hv⟩ := card_pos.mp (show 0 < S.card by omega)
  have round : step (clique n) k S = univ := by
    apply eq_univ_of_forall
    intro w
    by_cases hw : w ∈ S
    · exact mem_union_left _ hw
    · refine mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hw,v,hv,fun e => hw (e ▸ hv),?_⟩)
      rw [whites S hv,card_sdiff (subset_univ S),size]
      simp
      omega
  have all : full (clique n) k S := by
    unfold full
    rw [Fintype.card_fin]
    obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    have iter (r : ℕ) : (step (clique n) k)^[r+1] S = univ := by
      rw [Function.iterate_succ_apply,round]
      exact Function.iterate_fixed (show step (clique n) k univ = univ by simp [step]) _
    exact ht.symm ▸ iter t
  let costs := {r | ∃ D : Finset (Fin n), D.card=r ∧ full (clique n) k D ∧ Q D}
  have hit : n-k ∈ costs := ⟨S,size,all,accept S size⟩
  obtain ⟨D,eq,good,_⟩ := Nat.sInf_mem (show costs.Nonempty from ⟨_,hit⟩)
  exact Nat.le_antisymm (Nat.sInf_le (s := costs) hit) ((minimum_seeds good).trans_eq eq)

theorem clique_forcing_values {n : ℕ} (hn : 3 ≤ n) :
    forcing (clique n) 1 = n-1 ∧ forcing (clique n) 2 = n-2 ∧ total (clique n) = n-1 := by
  refine ⟨clique_forcing (by omega) _ (fun _ _ => trivial),
    clique_forcing (by omega) _ (fun _ _ => trivial),clique_forcing (by omega) _ ?_⟩
  intro S size v hv
  have two : 1 < S.card := by omega
  obtain ⟨a,ha,b,hb,ne⟩ := one_lt_card.mp two
  by_cases va : v=a
  · exact ⟨b,hb,va ▸ ne⟩
  · exact ⟨a,ha,va⟩

private def paired (m : ℕ) : Fin m × Bool ↪ Fin (2*m+1) where
  toFun p := ⟨2*p.1.val + (if p.2 then 1 else 0),by split <;> omega⟩
  inj' := by
    rintro ⟨i,a⟩ ⟨j,b⟩ eq
    have h := congrArg Fin.val eq
    change 2*i.val+(if a then 1 else 0) = 2*j.val+(if b then 1 else 0) at h
    apply Prod.ext
    · apply Fin.ext
      change i.val = j.val
      cases a <;> cases b <;> simp at h <;> omega
    · cases a <;> cases b <;> simp_all <;> omega

private theorem near_perfect (m : ℕ) : HasMaximalMatching (clique (2*m+1)) m := by
  refine ⟨paired m,fun i => (paired m).injective.ne (by simp),?_⟩
  have covered {v : Fin (2*m+1)} (lt : v.val < 2*m) : v ∈ support (paired m) := by
    let i : Fin m := ⟨v.val/2,by omega⟩
    refine (Graffiti326.mem_support _).mpr ⟨i,decide (v.val%2=1),Fin.ext ?_⟩
    change 2*(v.val/2)+(if decide (v.val%2=1) then 1 else 0) = v.val
    split_ifs <;> simp_all <;> omega
  intro v hv w hw edge
  apply edge
  apply Fin.ext
  have x := mt covered hv
  have y := mt covered hw
  omega

theorem minimum_maximal_clique (m : ℕ) : minMaximalMatching (clique (2*m+1)) = m := by
  let costs := {k | HasMaximalMatching (clique (2*m+1)) k}
  obtain ⟨f,_,maximal⟩ := Nat.sInf_mem (show costs.Nonempty from ⟨m,near_perfect m⟩)
  apply le_antisymm (Nat.sInf_le (s := costs) (near_perfect m))
  have rest : (univ \ support f).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_contra ne
    exact maximal x (mem_sdiff.mp hx).2 y (mem_sdiff.mp hy).2 ne
  rw [card_sdiff (subset_univ _)] at rest
  simp [Graffiti326.support,Fintype.card_prod] at rest
  change m ≤ sInf costs
  omega

/-- A dominating family in the line graph, encoded by ordered endpoints of its edges.
A graph edge is dominated precisely when it shares an endpoint with a chosen edge. -/
def EdgeDominatingFamily {U : Type*} (H : SimpleGraph U) (k : ℕ) : Prop :=
  ∃ a b : Fin k → U, (∀ i, H.Adj (a i) (b i)) ∧ ∀ x y, H.Adj x y →
    ∃ i, x=a i ∨ x=b i ∨ y=a i ∨ y=b i

theorem line_graph_minimum (m : ℕ) :
    sInf {k | EdgeDominatingFamily (clique (2*m+1)) k} =
      minMaximalMatching (clique (2*m+1)) := by
  classical
  rw [minimum_maximal_clique]
  let costs := {k | EdgeDominatingFamily (clique (2*m+1)) k}
  obtain ⟨f,adj,maximal⟩ := near_perfect m
  have hit : m ∈ costs := by
    refine ⟨fun i => f (i,false),fun i => f (i,true),adj,fun x y xy => ?_⟩
    have endpoints : x ∈ Graffiti326.support f ∨ y ∈ Graffiti326.support f := by
      by_contra! neither
      exact maximal x neither.1 y neither.2 xy
    rcases endpoints with hx | hy
    · obtain ⟨i,b,eq⟩ := (Graffiti326.mem_support _).mp hx
      cases b
      · exact ⟨i,Or.inl eq.symm⟩
      · exact ⟨i,Or.inr (Or.inl eq.symm)⟩
    · obtain ⟨i,b,eq⟩ := (Graffiti326.mem_support _).mp hy
      cases b
      · exact ⟨i,Or.inr (Or.inr (Or.inl eq.symm))⟩
      · exact ⟨i,Or.inr (Or.inr (Or.inr eq.symm))⟩
  obtain ⟨a,b,_,dom⟩ := Nat.sInf_mem (show costs.Nonempty from ⟨_,hit⟩)
  let S := univ.image a ∪ univ.image b
  have ct : S.card ≤ 2*(sInf costs) := by
    have le := card_union_le (univ.image a) (univ.image b)
    have ha := card_image_le (f := a) (s := univ)
    have hb := card_image_le (f := b) (s := univ)
    simp only [card_univ,Fintype.card_fin] at ha hb
    dsimp [S]
    omega
  have rem : (univ \ S).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    by_contra ne
    obtain ⟨i,h|h|h|h⟩ := dom x y ne
    all_goals (subst_vars; simp [S] at *)
  rw [card_sdiff (subset_univ S),card_univ,Fintype.card_fin] at rem
  apply le_antisymm (Nat.sInf_le (s := costs) hit)
  change m ≤ sInf costs
  omega

def ClawFree {U : Type*} (H : SimpleGraph U) := ∀ v a b c : U,
  H.Adj v a → H.Adj v b → H.Adj v c → a ≠ b → a ≠ c → b ≠ c →
  H.Adj a b ∨ H.Adj a c ∨ H.Adj b c

noncomputable def diameter {U : Type*} [Fintype U] (H : SimpleGraph U) :=
  univ.sup (fun v => univ.sup (H.dist v))

noncomputable def subTotal {U : Type*} [Fintype U] (H : SimpleGraph U) [DecidableRel H.Adj] :=
  sInf {k | Fintype.card U ≤ (((univ.val.map (fun v => H.degree v)).sort (· ≥ ·)).take k).sum}

def EdgeCover {U : Type*} (H : SimpleGraph U) (S : Finset (Sym2 U)) : Prop :=
  ↑S ⊆ H.edgeSet ∧ ∀ v : U, ∃ e ∈ S, v ∈ e
noncomputable def edgeCoverNumber {U : Type*} (H : SimpleGraph U) :=
  sInf {k | ∃ S : Finset (Sym2 U), S.card=k ∧ EdgeCover H S}

noncomputable def chi {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {k | Nonempty (H →g (⊤ : SimpleGraph (Fin k)))}

theorem complete_chromatic (n : ℕ) : chi (clique n) = n := by
  let costs := {k | Nonempty (clique n →g (⊤ : SimpleGraph (Fin k)))}
  have fit : n ∈ costs := ⟨⟨id,fun h => h⟩⟩
  obtain ⟨f⟩ := Nat.sInf_mem (show costs.Nonempty from ⟨_,fit⟩)
  have inj : Function.Injective f := by
    intro x y e
    by_contra ne
    exact (f.map_rel (show (clique n).Adj x y from ne)) e
  exact Nat.le_antisymm (Nat.sInf_le (s := costs) fit) (by simpa [chi,costs] using Fintype.card_le_of_injective _ inj)

private abbrev V := Fin 21
private abbrev G := clique 21
private theorem nt : 2 ≤ Fintype.card V := by decide
private theorem reg : G.IsRegularOfDegree 20 := by intro v; simp [clique]
private theorem conn : G.Connected := by
  refine ⟨fun v w => ?_⟩
  by_cases eq : v=w
  · subst w; exact .refl _
  · exact (show G.Adj v w from eq).reachable
private theorem eu : Eulerian G := ⟨conn,fun v => by rw [reg v]; decide⟩
private theorem claw : ClawFree G := fun _ _ _ _ _ _ _ ne _ _ => Or.inl ne
private theorem chord : Chordal G := by
  rintro k hk ⟨f,iff⟩
  let a : Fin k := ⟨0,by omega⟩
  let c : Fin k := ⟨2,by omega⟩
  have ne : a ≠ c := fun h => by have := congrArg Fin.val h; simp [a,c] at this
  have e : G.Adj (f a) (f c) := f.injective.ne ne
  have wrong := (iff a c).mp e
  simp [consecutive,a,c] at wrong
  omega

private theorem mm : minMaximalMatching G = 10 := minimum_maximal_clique 10
private theorem maximum_matching_bound : matchingNumber G ≤ 10 := by
  classical
  unfold matchingNumber
  have mem := Finset.max'_mem (feasibleMatchingSizes G) (matchingSizes_nonempty G)
  have le := (mem_range.mp (mem_filter.mp mem).1)
  exact Nat.le_of_lt_succ le

private theorem diameter_bound : diameter G ≤ 1 := by
  apply Finset.sup_le
  intro v _
  apply Finset.sup_le
  intro w _
  by_cases eq : v=w
  · subst w
    rw [dist_self]
    decide
  · exact (dist_eq_one_iff_adj.mpr (show G.Adj v w from eq)).le

private def covering : Finset (Sym2 V) :=
  (univ.image (fun i : Fin 10 => s(paired 10 (i,false),paired 10 (i,true)))) ∪ {s(19,20)}

private theorem edge_cover_bound : edgeCoverNumber G ≤ 11 := by
  refine Nat.sInf_le (s := {k | ∃ S : Finset (Sym2 V), S.card=k ∧ EdgeCover G S})
    ⟨covering,by decide,?_,?_⟩
  · exact (show ∀ e ∈ covering, e ∈ G.edgeSet by decide)
  · decide

private theorem subtotal_bound : subTotal G ≤ 2 := by
  apply Nat.sInf_le (s := {k | Fintype.card V ≤
    (((univ.val.map (fun v => G.degree v)).sort (· ≥ ·)).take k).sum})
  change 21 ≤ ((((univ : Finset V).val.map (fun v => G.degree v)).sort (· ≥ ·)).take 2).sum
  rw [show (fun v : V => G.degree v) = (fun _ => 20) from funext reg, Multiset.map_const']
  change 21 ≤ (((Multiset.replicate 21 20).sort (· ≥ ·)).take 2).sum
  rw [← Multiset.coe_replicate,Multiset.coe_sort,List.mergeSort_eq_self (· ≥ ·) (by simp [List.sorted_replicate])]
  decide
private theorem avg : meanDegree G = 20 := by
  unfold meanDegree
  rw [show (∑ v : V, G.degree v) = 420 by decide,show Fintype.card V = 21 by decide]
  norm_num
private theorem delta : G.minDegree = 20 := by
  exact le_antisymm ((G.minDegree_le_degree 0).trans_eq (reg 0))
    (G.le_minDegree_of_forall_le_degree _ fun v => (reg v).ge)
private theorem maxdeg : G.maxDegree = 20 := by
  exact le_antisymm (G.maxDegree_le_of_forall_degree_le _ fun v => (reg v).le)
    ((reg 0).symm.trans_le (G.degree_le_maxDegree 0))
private theorem z : forcing G 1 = 20 := (clique_forcing_values (n := 21) (by decide)).1
private theorem two : forcing G 2 = 19 := (clique_forcing_values (n := 21) (by decide)).2.1
private theorem t : total G = 20 := (clique_forcing_values (n := 21) (by decide)).2.2

theorem row1974_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → H.Connected → (∃ d, H.IsRegularOfDegree d) → (minMaximalMatching H : ℤ) ≤ 2*(diameter H : ℤ)+7) := by
  intro claim
  have bad := claim V G nt conn ⟨20,reg⟩
  rw [mm] at bad
  have h := diameter_bound
  omega

theorem row2348_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Chordal H → Eulerian H → (total H : ℚ) ≤ (8/9 : ℚ)*forcing H 1+14/9) := by
  intro claim
  have bad := claim V G nt chord eu
  rw [t,z] at bad
  norm_num at bad

theorem row2355_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → ClawFree H → Eulerian H → (minMaximalMatching H : ℚ) ≤ (2/3 : ℚ)*edgeCoverNumber H+4/3) := by
  intro claim
  have bad := claim V G nt claw eu
  rw [mm] at bad
  have bound : (edgeCoverNumber G : ℚ) ≤ 11 := by exact_mod_cast edge_cover_bound
  norm_num at bad
  linarith

theorem row2400_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → ClawFree H → Eulerian H → minMaximalMatching H ≤ 3*subTotal H) := by
  intro claim
  have bad := claim V G nt claw eu
  rw [mm] at bad
  have h := subtotal_bound
  omega

theorem row2425_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Eulerian H → (forcing H 2 : ℚ) ≤ (5/12 : ℚ)*H.minDegree+43/6) := by
  intro claim
  have bad := claim V G nt eu
  rw [two,delta] at bad
  norm_num at bad

theorem row2526_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → ClawFree H → Eulerian H → (minMaximalMatching H : ℚ) ≤ (11/18 : ℚ)*matchingNumber H+7/3) := by
  intro claim
  have bad := claim V G nt claw eu
  rw [mm] at bad
  have bound : (matchingNumber G : ℚ) ≤ 10 := by exact_mod_cast maximum_matching_bound
  norm_num at bad
  linarith

theorem row2572_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Chordal H → Eulerian H → (total H : ℚ) ≤ (2/3 : ℚ)*forcing H 2+16/3) := by
  intro claim
  have bad := claim V G nt chord eu
  rw [t,two] at bad
  norm_num at bad

theorem row2578_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → ClawFree H → Eulerian H → (forcing H 2 : ℚ) ≤ (1/2 : ℚ)*H.minDegree+6) := by
  intro claim
  have bad := claim V G nt claw eu
  rw [two,delta] at bad
  norm_num at bad

theorem row2579_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Chordal H → Eulerian H → (forcing H 2 : ℚ) ≤ (1/2 : ℚ)*H.minDegree+6) := by
  intro claim
  have bad := claim V G nt chord eu
  rw [two,delta] at bad
  norm_num at bad

theorem row2596_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → (chi H : ℚ) ≤ (6/7 : ℚ)*meanDegree H+24/7) := by
  intro claim
  have bad := claim V G nt 
  rw [complete_chromatic,avg] at bad
  norm_num at bad

theorem row2603_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Chordal H → Eulerian H → (total H : ℚ) ≤ (4/5 : ℚ)*H.maxDegree+14/5) := by
  intro claim
  have bad := claim V G nt chord eu
  rw [t,maxdeg] at bad
  norm_num at bad

#print axioms clique_forcing_values
#print axioms minimum_maximal_clique
#print axioms line_graph_minimum
#print axioms row1974_false
#print axioms row2348_false
#print axioms row2355_false
#print axioms row2400_false
#print axioms row2425_false
#print axioms row2526_false
#print axioms row2572_false
#print axioms row2578_false
#print axioms row2579_false
#print axioms row2596_false
#print axioms row2603_false
end CompleteRows
