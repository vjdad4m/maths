import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Powerset

/-! Twelve inequalities from Ján Pastorek’s AutoGraphForge. The biclique, matching,
regularity and class lemmas below reproduce the published line 1883 formalization.
The new forcing argument handles every positive threshold below the part size. -/
namespace AutoGraphForge373
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
/-- Same predicate as upstream IsCographClass and published line 378. -/
def Cograph := ∀ a b c d : V, G.Adj a b → G.Adj b c → G.Adj c d →
  ¬G.Adj a c → ¬G.Adj b d → G.Adj a d

end AutoGraphForge373

namespace AutoGraphForge1080
open Finset SimpleGraph AutoGraphForge373
open Classical
noncomputable section
abbrev Vertex (n : ℕ) := Bool × Fin n

def biclique (n : ℕ) : SimpleGraph (Vertex n) where
  Adj x y := x.1 ≠ y.1
  symm := fun _ _ h => h.symm
  loopless := fun _ => not_ne_iff.mpr rfl

theorem biclique_class (n : ℕ) : Cograph (biclique n) ∧
    Nonempty (biclique n →g (⊤ : SimpleGraph (Fin 2))) := by
  have chain : ∀ a b c d : Bool, a ≠ b → b ≠ c → c ≠ d → a ≠ d := by decide
  refine ⟨fun a b c d ab bc cd _ _ => chain a.1 b.1 c.1 d.1 ab bc cd, ?_⟩
  let sideColor (b : Bool) : Fin 2 := if b then 1 else 0
  have proper : ∀ a b, a ≠ b → sideColor a ≠ sideColor b := by decide
  exact ⟨⟨fun x => sideColor x.1, fun {x y} e => proper x.1 y.1 e⟩⟩


end
end AutoGraphForge1080
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

namespace AutoGraphForge1883
open SimpleGraph Finset Graffiti326 AutoGraphForge378 AutoGraphForge1080
open AutoGraphForge373
variable {n k : ℕ}

/-- An edge of Kₙ,ₙ is specified by its left and right indices. The closed
line-graph neighborhood of an edge consists of exactly its row and column. -/
def DominatesEdges (left right : Fin k → Fin n) : Prop :=
  ∀ a b, (∃ i, left i = a) ∨ (∃ i, right i = b)

private theorem edge_domination_lower {left right : Fin k → Fin n}
    (covers : DominatesEdges left right) : n ≤ k := by
  classical
  have surj : Function.Surjective left ∨ Function.Surjective right := by
    by_cases h : Function.Surjective left
    · exact Or.inl h
    · obtain ⟨a,ha⟩ : ∃ a, ¬∃ i, left i = a := by simpa [Function.Surjective] using h
      exact Or.inr (fun b => (covers a b).resolve_left ha)
  rcases surj with h | h <;> simpa using Fintype.card_le_of_surjective _ h

/-- Every maximal matching saturates both parts. -/
theorem maximal_size {k : ℕ} (M : HasMaximalMatching (biclique n) k) : k = n := by
  classical
  obtain ⟨f,edges,maximal⟩ := M
  let index (b : Bool) (i : Fin k) : Fin n :=
    if (f (i,false)).1 = b then (f (i,false)).2 else (f (i,true)).2
  have covered {b : Bool} {a : Fin n} (h : (b,a) ∈ support f) : ∃ i, index b i = a := by
    obtain ⟨i,t,eq⟩ := (mem_support f).mp h
    refine ⟨i,?_⟩
    cases t with
    | false =>
      have side : (f (i,false)).1 = b := congrArg Prod.fst eq
      simpa only [index,if_pos side] using (show (f (i,false)).2 = a from congrArg Prod.snd eq)
    | true =>
      have side : (f (i,false)).1 ≠ b := fun bad => (edges i) (bad.trans (congrArg Prod.fst eq).symm)
      simpa only [index,if_neg side] using (show (f (i,true)).2 = a from congrArg Prod.snd eq)
  have dom : DominatesEdges (index false) (index true) := by
    intro a b
    by_cases ha : (false,a) ∈ support f
    · exact Or.inl (covered ha)
    by_cases hb : (true,b) ∈ support f
    · exact Or.inr (covered hb)
    exact (maximal _ ha _ hb (show false ≠ true by decide)).elim
  have lo := edge_domination_lower dom
  have hi := Fintype.card_le_of_injective f f.injective
  change Fintype.card (Fin k × Bool) ≤ Fintype.card (Bool × Fin n) at hi
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hi
  omega

theorem matching_exact (n : ℕ) : minMaximalMatching (biclique n) = n := by
  let diag : Fin n × Bool ↪ Vertex n := (Equiv.prodComm (Fin n) Bool).toEmbedding
  have both (v : Vertex n) : v ∈ support diag :=
    (mem_support diag).mpr ⟨v.2,v.1,rfl⟩
  have hit : HasMaximalMatching (biclique n) n :=
    ⟨diag,fun _ => Bool.false_ne_true,fun u hu => (hu (both u)).elim⟩
  exact maximal_size (Nat.sInf_mem (show {k | HasMaximalMatching (biclique n) k}.Nonempty from ⟨n,hit⟩))

private def edgeAt (i j : Fin n) : (biclique n).edgeSet :=
  ⟨s((false,i),(true,j)),show false ≠ true by decide⟩

private theorem edge_indexed (e : (biclique n).edgeSet) :
    ∃ i j, e = edgeAt i j := by
  obtain ⟨e,he⟩ := e
  induction e using Sym2.ind with
  | h x y =>
    obtain ⟨a,i⟩ := x
    obtain ⟨b,j⟩ := y
    change a ≠ b at he
    cases a <;> cases b
    · exact (he rfl).elim
    · exact ⟨i,j,rfl⟩
    · exact ⟨j,i,Subtype.ext Sym2.eq_swap⟩
    · exact (he rfl).elim

private theorem share_endpoint (i j a b : Fin n) :
    (∃ v, v ∈ (edgeAt i j).val ∧ v ∈ (edgeAt a b).val) ↔ i = a ∨ j = b := by
  simp [edgeAt,Sym2.mem_iff,or_and_right,Prod.mk.injEq]

/-- The closed-neighborhood domination predicate of the source line graph,
over the actual Mathlib edge set. Equality of edges allows the selected edge
itself in the closed neighborhood. -/
def EdgeDominating {V : Type*} (G : SimpleGraph V) (es : Fin k → G.edgeSet) : Prop :=
  ∀ e : G.edgeSet, ∃ i v, v ∈ (es i).val ∧ v ∈ e.val

theorem source_minimum (n : ℕ) :
    sInf {k | ∃ es : Fin k → (biclique n).edgeSet, EdgeDominating (biclique n) es} =
      minMaximalMatching (biclique n) := by
  rw [matching_exact]
  let sizes := {k | ∃ es : Fin k → (biclique n).edgeSet, EdgeDominating (biclique n) es}
  have hit : n ∈ sizes := by
    refine ⟨fun i => edgeAt i i, ?_⟩
    intro e
    obtain ⟨a,b,rfl⟩ := edge_indexed e
    exact ⟨a,(share_endpoint a a a b).mpr (Or.inl rfl)⟩
  obtain ⟨es,dom⟩ := Nat.sInf_mem (show sizes.Nonempty from ⟨n,hit⟩)
  choose left right rep using fun i => edge_indexed (es i)
  apply Nat.le_antisymm (Nat.sInf_le (s := sizes) hit)
  apply edge_domination_lower (left := left) (right := right)
  intro a b
  obtain ⟨i,common⟩ := dom (edgeAt a b)
  rw [rep i] at common
  rcases (share_endpoint _ _ _ _).mp common with h | h
  · exact Or.inl ⟨i,h⟩
  · exact Or.inr ⟨i,h⟩

instance (n : ℕ) : DecidableRel (biclique n).Adj := fun x y => inferInstanceAs (Decidable (x.1 ≠ y.1))

theorem regular_biclique (n : ℕ) : (biclique n).IsRegularOfDegree n := by
  intro v
  rw [← card_neighborFinset_eq_degree]
  let e : Fin n ↪ Vertex n := ⟨fun i => (!v.1,i), fun _ _ h => congrArg Prod.snd h⟩
  have h : (biclique n).neighborFinset v = univ.map e := by
    ext u
    rw [mem_neighborFinset,mem_map]
    change (v.1 ≠ u.1) ↔ _
    constructor
    · intro ne
      have dist : ∀ a b : Bool, a ≠ b → (!a) = b := by decide
      exact ⟨u.2,mem_univ _,Prod.ext (dist _ _ ne) rfl⟩
    · rintro ⟨i,_,rfl⟩
      change v.1 ≠ !v.1
      cases v.1 <;> decide
  simp [h]

theorem four_clique_free (n : ℕ) : (biclique n).CliqueFree 4 := by
  intro s hs
  have injective : Function.Injective (fun x : s => x.val.1) := by
    intro a b h
    apply Subtype.ext
    by_contra diff
    exact (show a.val.1 ≠ b.val.1 from hs.1 a.property b.property diff) h
  have card := Fintype.card_le_of_injective _ injective
  rw [Fintype.card_coe,Fintype.card_bool,hs.2] at card
  omega

end AutoGraphForge1883

namespace BalancedForcing
open SimpleGraph Finset AutoGraphForge373 AutoGraphForge1080 AutoGraphForge378 AutoGraphForge1883
set_option maxHeartbeats 1000000
def CliquePartition {U : Type*} (G : SimpleGraph U) (k : ℕ) : Prop :=
  ∃ f : U → Fin k, ∀ a b, f a = f b → a ≠ b → G.Adj a b

noncomputable def vertexCliqueCover {U : Type*} (G : SimpleGraph U) : ℕ :=
  sInf {k | CliquePartition G k}

theorem cliquePartition_iff_complement_colorable {U : Type*} (G : SimpleGraph U) (k : ℕ) :
    CliquePartition G k ↔ Nonempty (Gᶜ →g (⊤ : SimpleGraph (Fin k))) := by
  constructor
  · rintro ⟨f,h⟩
    exact ⟨⟨f,fun {a b} e eq =>
      ((G.compl_adj a b).mp e).2 (h a b eq ((G.compl_adj a b).mp e).1)⟩⟩
  · rintro ⟨f⟩
    refine ⟨f,fun a b eq ne => ?_⟩
    by_contra missing
    exact f.map_rel ((G.compl_adj a b).mpr ⟨ne,missing⟩) eq


inductive Observed {V : Type*} (G : SimpleGraph V) (S : Finset V) : V → Prop where
  | root {v} (h : v ∈ S) : Observed G S v
  | neighbor {v w} (h : w ∈ S) (hvw : G.Adj v w) : Observed G S v
  | force {v w} (hvw : G.Adj v w) (hw : Observed G S w)
      (rest : ∀ u, G.Adj w u → u ≠ v → Observed G S u) : Observed G S v

noncomputable def power {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {n | ∃ S : Finset V, n = S.card ∧ ∀ v, Observed G S v}

def Eulerian {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ ∀ v, Even (G.degree v)


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

variable {n k : ℕ}
private def side (b : Bool) : Finset (Vertex n) := {b} ×ˢ univ

@[simp] private theorem in_side {v : Vertex n} {b : Bool} : v ∈ side b ↔ v.1=b := by
  rcases v with ⟨a,i⟩
  simp [side,eq_comm]

private theorem neighbors (v : Vertex n) : (biclique n).neighborFinset v = side (!v.1) := by
  ext w
  rw [mem_neighborFinset,in_side]
  change (v.1 ≠ w.1) ↔ _
  cases v.1 <;> cases w.1 <;> decide

private theorem part_bound {S : Finset (Vertex n)} (h : full (biclique n) k S) (b : Bool) :
    (side b \ S).card ≤ k := by
  classical
  let W := side b \ S
  by_contra! large
  have stuck (t : ℕ) : ∀ w ∈ W, w ∉ (step (biclique n) k)^[t] S := by
    induction t with
    | zero => exact fun w hw => (mem_sdiff.mp hw).2
    | succ t ih =>
      let B := (step (biclique n) k)^[t] S
      intro w hw added
      rw [Function.iterate_succ_apply'] at added
      obtain old | new := mem_union.mp added
      · exact ih w hw old
      obtain ⟨_,v,_,vw,cap⟩ := (mem_filter.mp new).2
      have wb : w.1=b := in_side.mp (mem_sdiff.mp hw).1
      have vside : v.1 ≠ b := wb ▸ vw
      have sub : W ⊆ (biclique n).neighborFinset v \ B := by
        intro u hu
        exact mem_sdiff.mpr ⟨(mem_neighborFinset _ _ _).mpr (show v.1 ≠ u.1 from
          (in_side.mp (mem_sdiff.mp hu).1).symm ▸ vside),ih u hu⟩
      exact (Nat.not_le_of_gt large) ((card_le_card sub).trans cap)
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < W.card by dsimp [W]; omega)
  have impossible := stuck (Fintype.card (Vertex n)) w hw
  exact impossible (h ▸ mem_univ w)

theorem forcing_lower {S : Finset (Vertex n)} (h : full (biclique n) k S) :
    2*(n-k) ≤ S.card := by
  have first := part_bound h false
  have second := part_bound h true
  have split : univ \ S = (side false \ S) ∪ (side true \ S) := by
    ext ⟨b,i⟩
    cases b <;> simp
  have small := card_union_le (side false \ S) (side true \ S)
  rw [← split,card_sdiff (subset_univ S)] at small
  have count : (univ : Finset (Vertex n)).card = 2*n := by simp
  have le := card_le_univ S
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at le
  omega

private theorem canonical {A : Finset (Fin n)} (non : A.Nonempty) (cap : n-A.card ≤ k) :
    let D := (univ : Finset Bool) ×ˢ A
    full (biclique n) k D ∧ isolateFree (biclique n) D ∧ seedConnected (biclique n) D := by
  let D := (univ : Finset Bool) ×ˢ A
  obtain ⟨j,hj⟩ := non
  have memD (b : Bool) : (b,j) ∈ D := by simp [D,hj]
  have across (b : Bool) : (!b) ≠ b := by cases b <;> decide
  have done : step (biclique n) k D = univ := by
    apply eq_univ_of_forall
    intro v
    by_cases inside : v ∈ D
    · exact mem_union_left _ inside
    · let u : Vertex n := (!v.1,j)
      have rest : (biclique n).neighborFinset u \ D = {v.1} ×ˢ (univ \ A) := by
        ext ⟨a,i⟩
        simp [neighbors,side,D,u,and_assoc,and_comm]
      refine mem_union_right _ (mem_filter.mpr ⟨mem_univ _,inside,u,memD _,across _,?_⟩)
      rw [rest]
      simpa [card_sdiff] using cap
  have fixed : step (biclique n) k univ = univ := by simp [step]
  have rounds (t : ℕ) : (step (biclique n) k)^[t+1] D = univ := by
    induction t with
    | zero => exact done
    | succ t ih => rw [Function.iterate_succ_apply',ih,fixed]
  have positive : 0 < Fintype.card (Vertex n) := Fintype.card_pos_iff.mpr ⟨false,j⟩
  have all : full (biclique n) k D := by
    obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
    unfold full
    rw [ht]
    exact rounds t
  have totalD : isolateFree (biclique n) D := by
    intro v _
    exact ⟨(!v.1,j),memD _,(across _).symm⟩
  let J := (biclique n).induce (D : Set (Vertex n))
  let hub : (D : Set (Vertex n)) := ⟨(false,j),memD _⟩
  let mid : (D : Set (Vertex n)) := ⟨(true,j),memD _⟩
  have reach (v : (D : Set (Vertex n))) : J.Reachable v hub := by
    by_cases h : v.val.1 = true
    · exact (show J.Adj v hub from fun eq => Bool.noConfusion (h.symm.trans eq)).reachable
    · exact (show J.Adj v mid from h).reachable.trans
        (show J.Adj mid hub from (by decide : true ≠ false)).reachable
  haveI : Nonempty (D : Set (Vertex n)) := ⟨hub⟩
  exact ⟨all,totalD,⟨fun x y => (reach x).trans (reach y).symm⟩⟩

theorem forcing_exact (hk : k < n) (Q : Finset (Vertex n) → Prop)
    (accept : ∀ S, isolateFree (biclique n) S → seedConnected (biclique n) S → Q S) :
    optimum (biclique n) k Q = 2*(n-k) := by
  classical
  obtain ⟨A,_,size⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := n-k) (by simp)
  have non : A.Nonempty := card_pos.mp (by omega)
  obtain ⟨fullA,totalA,connectedA⟩ := canonical (k := k) non (by omega)
  let D := (univ : Finset Bool) ×ˢ A
  let costs := {r | ∃ S : Finset (Vertex n), S.card=r ∧ full (biclique n) k S ∧ Q S}
  have upper : 2*(n-k) ∈ costs := ⟨D,by simp [D,size],fullA,accept D totalA connectedA⟩
  obtain ⟨S,eq,fs,_⟩ := Nat.sInf_mem (show costs.Nonempty from ⟨_,upper⟩)
  exact Nat.le_antisymm (Nat.sInf_le (s := costs) upper) ((forcing_lower fs).trans_eq eq)

/-- A clique color can occur at most once in each part. Conversely, each part
can label its own vertices independently with any sufficiently large palette. -/
theorem partition_iff_parts_fit {I : Type*} (P : I → Type*) [∀ i, Fintype (P i)] (k : ℕ) :
    CliquePartition (completeMultipartiteGraph P) k ↔ ∀ i, Fintype.card (P i) ≤ k := by
  classical
  constructor
  · rintro ⟨color,proper⟩ i
    have inj : Function.Injective (fun x : P i => color ⟨i,x⟩) := by
      intro x y eq
      by_contra ne
      have edge := proper ⟨i,x⟩ ⟨i,y⟩ eq (fun h => ne (by simpa using h))
      exact edge rfl
    simpa using Fintype.card_le_of_injective _ inj
  · intro capacity
    let label (i : I) (x : P i) : Fin k := Fin.castLE (capacity i) (Fintype.equivFin (P i) x)
    refine ⟨fun v => label v.1 v.2,?_⟩
    rintro ⟨i,x⟩ ⟨j,y⟩ same distinct (rfl : i=j)
    have eq : Fintype.equivFin (P i) x = Fintype.equivFin (P i) y := Fin.ext (congrArg (fun c : Fin k => c.val) same)
    exact distinct (by rw [(Fintype.equivFin (P i)).injective eq])

theorem clique_cover_complete_multipartite {I : Type*} [Fintype I] (P : I → Type*)
    [∀ i, Fintype (P i)] :
    vertexCliqueCover (completeMultipartiteGraph P) = univ.sup (fun i => Fintype.card (P i)) := by
  classical
  let G := completeMultipartiteGraph P
  let largest := univ.sup (fun i => Fintype.card (P i))
  have good : CliquePartition G largest := (partition_iff_parts_fit P _).mpr
    (fun i => le_sup (s := univ) (f := fun i => Fintype.card (P i)) (mem_univ i))
  apply Nat.le_antisymm (Nat.sInf_le (s := {k | CliquePartition G k}) good)
  have opt := Nat.sInf_mem (s := {k | CliquePartition G k}) ⟨_,good⟩
  exact Finset.sup_le (fun i _ => (partition_iff_parts_fit P _).mp opt i)


theorem balanced_cover (n : ℕ) : vertexCliqueCover (biclique n) = n := by
  let P (_ : Bool) := Fin n
  have convert (k : ℕ) : CliquePartition (biclique n) k ↔ CliquePartition (completeMultipartiteGraph P) k := by
    constructor
    · rintro ⟨f,ok⟩
      refine ⟨fun x => f (x.1,x.2),?_⟩
      rintro ⟨a,i⟩ ⟨b,j⟩ eq ne
      exact ok (a,i) (b,j) eq (fun h => ne (by cases h; rfl))
    · rintro ⟨f,ok⟩
      refine ⟨fun x => f ⟨x.1,x.2⟩,?_⟩
      rintro ⟨a,i⟩ ⟨b,j⟩ eq ne
      exact ok ⟨a,i⟩ ⟨b,j⟩ eq (fun h => ne (by cases h; rfl))
  have same : vertexCliqueCover (biclique n) = vertexCliqueCover (completeMultipartiteGraph P) :=
    congrArg sInf (Set.ext convert)
  rw [same,clique_cover_complete_multipartite]
  simp [P]

noncomputable def eccentricity {U : Type*} [Fintype U] (G : SimpleGraph U) (u : U) := univ.sup (G.dist u)
noncomputable def radius {U : Type*} [Fintype U] (G : SimpleGraph U) := sInf (Set.range (eccentricity G))

/-- Distances on distinct triples, with maximum zero if there are no triples. -/
noncomputable def triScore {U : Type*} [DecidableEq U] (G : SimpleGraph U) (t : U × U × U) :=
  if t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 then
    G.dist t.1 t.2.1 + G.dist t.2.2 t.2.1 + G.dist t.1 t.2.2 else 0
noncomputable def triameter {U : Type*} [Fintype U] [DecidableEq U] (G : SimpleGraph U) :=
  univ.sup (triScore G)

private def via (u v : Vertex n) (eq : u.1=v.1) : (biclique n).Walk u v :=
  .cons (show (biclique n).Adj u (!u.1,u.2) from
    (show u.1 ≠ !u.1 by cases u.1 <;> decide))
    (.cons (show (biclique n).Adj (!u.1,u.2) v from
      (show (!u.1) ≠ v.1 by rw [← eq]; cases u.1 <;> decide)) .nil)

private theorem distance (u v : Vertex n) : (biclique n).dist u v =
    if u=v then 0 else if u.1=v.1 then 2 else 1 := by
  split_ifs with same sideeq
  · subst v
    exact dist_self
  · let walk := via u v sideeq
    have bound : (biclique n).dist u v ≤ 2 := SimpleGraph.dist_le walk
    have pos := walk.reachable.pos_dist_of_ne same
    have diff : (biclique n).dist u v ≠ 1 := fun h => (dist_eq_one_iff_adj.mp h) sideeq
    omega
  · exact dist_eq_one_iff_adj.mpr sideeq

theorem connected_biclique (j : Fin n) : (biclique n).Connected := by
  haveI : Nonempty (Vertex n) := ⟨false,j⟩
  refine ⟨fun u v => ?_⟩
  by_cases eq : u.1=v.1
  · exact (via u v eq).reachable
  · exact (show (biclique n).Adj u v from eq).reachable

private theorem dist_two_le (u v : Vertex n) : (biclique n).dist u v ≤ 2 := by
  rw [distance]
  split_ifs <;> decide

theorem radius_formula (hn : 2 ≤ n) : radius (biclique n) = 2 := by
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  have ab : a ≠ b := fun h => by have := congrArg Fin.val h; simp [a,b] at this
  have ecc (u : Vertex n) : eccentricity (biclique n) u = 2 := by
    apply le_antisymm (Finset.sup_le (fun v _ => dist_two_le u v))
    let v : Vertex n := (u.1,if u.2=a then b else a)
    have diff : u ≠ v := by
      intro h
      have e := congrArg Prod.snd h
      dsimp [v] at e
      split at e <;> simp_all
    have d : (biclique n).dist u v = 2 := by simp [distance,diff,v]
    exact d ▸ (Finset.le_sup (s := univ) (f := (biclique n).dist u) (mem_univ v))
  have seteq : Set.range (eccentricity (biclique n)) = {2} := by
    ext z
    constructor
    · rintro ⟨v,rfl⟩
      exact ecc v
    · rintro (rfl : z=2)
      exact ⟨(false,a),ecc _⟩
  simp [radius,seteq]

theorem triameter_formula (hn : 3 ≤ n) : triameter (biclique n) = 6 := by
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨u,v,w⟩ _
    unfold triScore
    split
    · change (biclique n).dist u v + (biclique n).dist w v + (biclique n).dist u w ≤ 6
      have := dist_two_le u v
      have := dist_two_le w v
      have := dist_two_le u w
      omega
    · decide
  · let a : Vertex n := (false,⟨0,by omega⟩)
    let b : Vertex n := (false,⟨1,by omega⟩)
    let c : Vertex n := (false,⟨2,by omega⟩)
    have dis (i j : Fin n) (h : i.val ≠ j.val) : (false,i) ≠ (false,j) :=
      fun e => h (congrArg Fin.val (congrArg Prod.snd e))
    have ab : a ≠ b := dis _ _ (by simp [a,b,c])
    have ac : a ≠ c := dis _ _ (by simp [a,b,c])
    have bc : b ≠ c := dis _ _ (by simp [a,b,c])
    have d : triScore (biclique n) (a,b,c) = 6 := by
      simp [triScore,distance,ab,ac,bc,bc.symm,a,b,c]
    exact d ▸ (Finset.le_sup (s := univ) (f := triScore (biclique n)) (mem_univ (a,b,c)))

theorem bipartite_power (j : Fin n) : power (biclique n) ≤ 2 := by
  let S : Finset (Vertex n) := {(false,j),(true,j)}
  refine Nat.sInf_le (s := {k | ∃ S : Finset (Vertex n), k = S.card ∧
    ∀ v, Observed (biclique n) S v}) ⟨S,by simp [S],?_⟩
  rintro ⟨b,i⟩
  cases b
  · exact Observed.neighbor (show (true,j) ∈ S by simp [S]) (by decide : false ≠ true)
  · exact Observed.neighbor (show (false,j) ∈ S by simp [S]) (by decide : true ≠ false)

theorem triangle_free (n : ℕ) : (biclique n).CliqueFree 3 := by
  intro s hs
  have inj : Function.Injective (fun x : s => x.val.1) := by
    intro a b eq
    apply Subtype.ext
    by_contra ne
    exact (hs.1 a.property b.property ne) eq
  have bound := Fintype.card_le_of_injective _ inj
  rw [Fintype.card_coe,Fintype.card_bool,hs.2] at bound
  omega

abbrev Bipartite {U : Type*} (G : SimpleGraph U) := Nonempty (G →g (⊤ : SimpleGraph (Fin 2)))
def NoIsolates {U : Type*} (G : SimpleGraph U) := ∀ v, ∃ w, G.Adj v w

theorem no_isolates (n : ℕ) : NoIsolates (biclique n) := by
  rintro ⟨b,i⟩
  exact ⟨(!b,i),show b ≠ !b by cases b <;> decide⟩

theorem eulerian_of_even (j : Fin n) (h : Even n) : Eulerian (biclique n) :=
  ⟨connected_biclique j,fun v => by rw [regular_biclique n v]; exact h⟩

theorem balanced_forcing_values (hn : 3 ≤ n) :
    forcing (biclique n) 1 = 2*(n-1) ∧ forcing (biclique n) 2 = 2*(n-2) ∧
    total (biclique n) = 2*(n-1) ∧ connectedForcing (biclique n) = 2*(n-1) :=
  ⟨forcing_exact (by omega) _ (fun _ _ _ => True.intro),
   forcing_exact (by omega) _ (fun _ _ _ => True.intro),
   forcing_exact (by omega) _ (fun _ h _ => h), forcing_exact (by omega) _ (fun _ _ h => h)⟩

private abbrev V := Vertex 16
private abbrev G := biclique 16
private theorem nontriv : 2 ≤ Fintype.card V := by decide
private theorem reg : ∃ d, G.IsRegularOfDegree d := ⟨16,regular_biclique 16⟩
private theorem eu : Eulerian G := eulerian_of_even 0 (by decide)
private theorem conn : G.Connected := eu.1
private theorem cg : Cograph G := (biclique_class 16).1
private theorem bi : Bipartite G := (biclique_class 16).2
private theorem tri : G.CliqueFree 3 := triangle_free 16
private theorem k4 : G.CliqueFree 4 := four_clique_free 16
private theorem z : forcing G 1 = 30 := (balanced_forcing_values (n := 16) (by decide)).1
private theorem two : forcing G 2 = 28 := (balanced_forcing_values (n := 16) (by decide)).2.1
private theorem t : total G = 30 := (balanced_forcing_values (n := 16) (by decide)).2.2.1
private theorem cf : connectedForcing G = 30 := (balanced_forcing_values (n := 16) (by decide)).2.2.2
private theorem radius16 : radius G = 2 := radius_formula (by decide)
private theorem triam : triameter G = 6 := triameter_formula (by decide)
private theorem theta : vertexCliqueCover G = 16 := balanced_cover 16
private theorem matching : minMaximalMatching G = 16 := matching_exact 16
private theorem delta : G.minDegree = 16 := by
  apply le_antisymm ((G.minDegree_le_degree (false,0)).trans_eq (regular_biclique 16 _))
  exact G.le_minDegree_of_forall_le_degree _ (fun v => (regular_biclique 16 v).ge)
private theorem maxdeg : G.maxDegree = 16 := by
  apply le_antisymm (G.maxDegree_le_of_forall_degree_le _ (fun v => (regular_biclique 16 v).le))
  exact (regular_biclique 16 (false,0)).symm.trans_le (G.degree_le_maxDegree (false,0))
theorem row942_defined_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → (∃ d, H.IsRegularOfDegree d) → H.CliqueFree 3 → NoIsolates H →
    (1/8 : ℚ) * total H + 3/4 ≤ power H) := by
  intro h
  have bound := h V G nontriv reg tri (no_isolates 16)
  rw [t] at bound
  have p : (power G : ℚ) ≤ 2 := by exact_mod_cast bipartite_power (n := 16) (0 : Fin 16)
  norm_num at bound
  linarith

theorem row942_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → (∃ d, H.IsRegularOfDegree d) → H.CliqueFree 3 →
    (1/8 : ℚ) * total H + 3/4 ≤ power H) := by
  intro h
  apply row942_defined_false
  intro U _ _ H _ non regular triangle _
  exact h U H non regular triangle

theorem row1539_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → H.Connected →
    (forcing H 2 : ℚ) ≤ (13/14 : ℚ) * forcing H 1 + 1/14) := by
  intro h
  have bound := h V G nontriv conn
  rw [two,z] at bound
  norm_num at bound

theorem row1904_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Cograph H → Eulerian H →
    (vertexCliqueCover H : ℤ) ≤ 3*(triameter H : ℤ)-8) := by
  intro h
  have bound := h V G nontriv cg eu
  rw [theta,triam] at bound
  norm_num at bound

theorem row1956_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → H.CliqueFree 4 → (∃ d, H.IsRegularOfDegree d) →
    (minMaximalMatching H : ℤ) ≤ 4*(radius H : ℤ)-1) := by
  intro h
  have bound := h V G nontriv k4 reg
  rw [matching,radius16] at bound
  norm_num at bound

theorem row2222_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → H.Connected →
    forcing H 2 ≤ H.maxDegree + 2) := by
  intro h
  have bound := h V G nontriv conn
  rw [two,maxdeg] at bound
  norm_num at bound

theorem row2240_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Cograph H → Eulerian H →
    (minMaximalMatching H : ℚ) ≤ (1/2 : ℚ)*H.minDegree + 4) := by
  intro h
  have bound := h V G nontriv cg eu
  rw [matching,delta] at bound
  norm_num at bound

theorem row2255_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Eulerian H → H.CliqueFree 3 →
    total H ≤ triameter H + 4) := by
  intro h
  have bound := h V G nontriv eu tri
  rw [t,triam] at bound
  norm_num at bound

theorem row2319_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Eulerian H → H.CliqueFree 3 →
    (connectedForcing H : ℚ) ≤ (5/3 : ℚ)*triameter H) := by
  intro h
  have bound := h V G nontriv eu tri
  rw [cf,triam] at bound
  norm_num at bound

theorem row2320_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Bipartite H → Eulerian H →
    (total H : ℚ) ≤ (5/3 : ℚ)*triameter H) := by
  intro h
  have bound := h V G nontriv bi eu
  rw [t,triam] at bound
  norm_num at bound

theorem row2321_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Bipartite H → Eulerian H →
    (forcing H 1 : ℚ) ≤ (5/3 : ℚ)*triameter H) := by
  intro h
  have bound := h V G nontriv bi eu
  rw [z,triam] at bound
  norm_num at bound

theorem row2354_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → H.CliqueFree 4 →
    (minMaximalMatching H : ℚ) ≤ (7/6 : ℚ)*triameter H + 1) := by
  intro h
  have bound := h V G nontriv k4
  rw [matching,triam] at bound
  norm_num at bound

theorem row2376_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Eulerian H →
    vertexCliqueCover H ≤ triameter H + 4) := by
  intro h
  have bound := h V G nontriv eu
  rw [theta,triam] at bound
  norm_num at bound

#print axioms forcing_exact
#print axioms balanced_forcing_values
#print axioms triameter_formula
#print axioms radius_formula
#print axioms balanced_cover
#print axioms row942_defined_false
#print axioms row942_false
#print axioms row1539_false
#print axioms row1904_false
#print axioms row1956_false
#print axioms row2222_false
#print axioms row2240_false
#print axioms row2255_false
#print axioms row2319_false
#print axioms row2320_false
#print axioms row2321_false
#print axioms row2354_false
#print axioms row2376_false
end BalancedForcing
