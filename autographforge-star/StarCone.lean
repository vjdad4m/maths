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

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Topology.Path
import Mathlib.Topology.Algebra.Ring.Real

namespace StarCone
open Finset SimpleGraph
open scoped BigOperators unitInterval
set_option maxHeartbeats 3200000
set_option maxRecDepth 20000
set_option synthInstance.maxSize 2048

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


abbrev V := Fin 17
def graph : SimpleGraph V where
  Adj u v := (u=0 ∧ v≠0) ∨ (v=0 ∧ u≠0)
  symm := fun _ _ => Or.symm
  loopless := fun _ => by simp

instance : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable ((u=0 ∧ v≠0) ∨ (v=0 ∧ u≠0)))

private theorem hub_adj {v : V} (ne : v≠0) : graph.Adj v 0 := Or.inr ⟨rfl,ne⟩
private theorem leaf_neighbor {v w : V} (ne : w≠0) (adj : graph.Adj v w) : v=0 :=
  (adj.resolve_right (fun h => ne h.1)).1

private theorem connected : graph.Connected := by
  have reach (v : V) : graph.Reachable v 0 := by
    by_cases h : v=0
    · subst v; exact .refl _
    · exact (hub_adj h).reachable
  exact ⟨fun x y => (reach x).trans (reach y).symm⟩

private theorem tree : graph.IsTree := by
  refine isTree_iff_connected_and_card.mpr ⟨connected,?_⟩
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← edgeFinset_card]
  decide

def Cograph {U : Type*} (H : SimpleGraph U) := ∀ a b c d : U, H.Adj a b → H.Adj b c → H.Adj c d →
  ¬H.Adj a c → ¬H.Adj b d → H.Adj a d
private theorem cograph : Cograph graph := by unfold Cograph; decide

abbrev Bipartite {U : Type*} (H : SimpleGraph U) := Nonempty (H →g (⊤ : SimpleGraph (Fin 2)))
private theorem bipartite : Bipartite graph := by
  let col (v : V) : Fin 2 := if v=0 then 0 else 1
  exact ⟨⟨col,show ∀ {x y : V}, graph.Adj x y → col x ≠ col y by decide⟩⟩

private def leaves : Finset V := univ.erase 0

private theorem forcing_lower {k} {S : Finset V} (h : full graph k S) : 16-k ≤ S.card := by
  let W := leaves \ S
  by_contra! low
  have le := Finset.le_card_sdiff S leaves
  have size : leaves.card = 16 := by decide
  have large : k < W.card := by dsimp [W]; omega
  have stuck (t : ℕ) : ∀ w ∈ W, w ∉ (step graph k)^[t] S := by
    induction t with
    | zero => exact fun w hw => (mem_sdiff.mp hw).2
    | succ t ih =>
      intro w hw added
      rw [Function.iterate_succ_apply'] at added
      obtain old | fresh := mem_union.mp added
      · exact ih w hw old
      obtain ⟨_,v,_,adj,cap⟩ := (mem_filter.mp fresh).2
      have hub := leaf_neighbor (mem_erase.mp (mem_sdiff.mp hw).1).1 adj
      subst v
      have sub : W ⊆ graph.neighborFinset 0 \ (step graph k)^[t] S := by
        intro u hu
        exact mem_sdiff.mpr ⟨(mem_neighborFinset _ _ _).mpr
          (hub_adj (mem_erase.mp (mem_sdiff.mp hu).1).1).symm,ih u hu⟩
      exact (Nat.not_le_of_gt large) ((card_le_card sub).trans cap)
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < W.card by omega)
  exact stuck (Fintype.card V) w hw (h ▸ mem_univ w)

private theorem after_two {k} {S : Finset V} (two : step graph k (step graph k S) = univ) :
    full graph k S := by
  have more (t : ℕ) : (step graph k)^[t+2] S = univ := by
    induction t with
    | zero => exact two
    | succ t ih => rw [Function.iterate_succ_apply',ih]; simp [step]
  exact more 15

private def seed (k : ℕ) := (univ : Finset V).filter (fun v => v≠0 ∧ v.val ≤ 16-k)

private theorem force_value {k} (size : (seed k).card=16-k)
    (rounds : step graph k (step graph k (seed k))=univ) : forcing graph k = 16-k := by
  let costs := {r | ∃ S : Finset V, S.card=r ∧ full graph k S ∧ True}
  have hit : 16-k ∈ costs := ⟨_,size,after_two rounds,trivial⟩
  obtain ⟨S,eq,ok,_⟩ := Nat.sInf_mem (show costs.Nonempty from ⟨_,hit⟩)
  exact Nat.le_antisymm (Nat.sInf_le (s := costs) hit) ((forcing_lower ok).trans_eq eq)

theorem star_forcing : forcing graph 1 = 15 ∧ forcing graph 2 = 14 :=
  ⟨force_value (by decide) (by decide),force_value (by decide) (by decide)⟩

private theorem connected_bound : connectedForcing graph ≤ 16 := by
  let S := (univ : Finset V).erase 16
  refine Nat.sInf_le (s := {k | ∃ D : Finset V, D.card=k ∧ full graph 1 D ∧ seedConnected graph D})
    ⟨S,by decide,after_two (by decide),?_⟩
  let hub : (S : Set V) := ⟨0,by decide⟩
  let J := graph.induce (S : Set V)
  have reach (v : (S : Set V)) : J.Reachable v hub := by
    by_cases h : v.val=0
    · have eq : v=hub := Subtype.ext h
      subst v; exact .refl _
    · exact (show J.Adj v hub from hub_adj h).reachable
  haveI : Nonempty (S : Set V) := ⟨hub⟩
  exact ⟨fun x y => (reach x).trans (reach y).symm⟩

theorem cover : vertexCliqueCover graph = 16 := by
  let color (v : V) : Fin 16 := ⟨v.val-1,by omega⟩
  let costs := {k | CliquePartition graph k}
  have ok : 16 ∈ costs := ⟨color,by decide⟩
  obtain ⟨f,proper⟩ := Nat.sInf_mem (show costs.Nonempty from ⟨_,ok⟩)
  have inj : Function.Injective (fun i : Fin 16 => f i.succ) := by
    intro i j eq
    by_contra ne
    have e := proper i.succ j.succ eq (fun h => ne (Fin.succ_injective _ h))
    exact Fin.succ_ne_zero _ (leaf_neighbor (Fin.succ_ne_zero _) e)
  exact Nat.le_antisymm (Nat.sInf_le (s := costs) ok) (by simpa using Fintype.card_le_of_injective _ inj)

def Dominates {U : Type*} (H : SimpleGraph U) (S : Finset U) :=
  ∀ v, v ∈ S ∨ ∃ w ∈ S, H.Adj v w
def Restrained {U : Type*} (H : SimpleGraph U) (S : Finset U) :=
  Dominates H S ∧ ∀ v ∉ S, ∃ w ∉ S, H.Adj v w
noncomputable def restrained {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {k | ∃ D : Finset U, Restrained H D ∧ D.card=k}

private theorem restrained_bound : restrained graph ≤ 17 := by
  exact Nat.sInf_le (s := {k | ∃ D : Finset V, Restrained graph D ∧ D.card=k})
    ⟨univ,⟨fun v => Or.inl (mem_univ v),fun v h => (h (mem_univ v)).elim⟩,by decide⟩
private def hhTail (d : ℕ) (xs : List ℕ) : List ℕ :=
  (xs.take d).map Nat.pred ++ xs.drop d

private def descending (xs : List ℕ) : List ℕ := xs.mergeSort (fun a b => decide (b ≤ a))

private def residueAux : ℕ → List ℕ → ℕ
  | 0, xs => xs.length
  | fuel+1, xs => match descending xs with
    | [] => 0
    | d :: tail => if d = 0 then tail.length + 1 else residueAux fuel (hhTail d tail)

/-- Re-sort in descending order, delete the maximum, and subtract one
from the next that many degrees, until the list is all zero. -/
def residueSequence (xs : List ℕ) : ℕ := residueAux xs.length xs

noncomputable def residue {U : Type*} [Fintype U] (H : SimpleGraph U) [DecidableRel H.Adj] :=
  residueSequence ((univ.val.map (fun v => H.degree v)).sort (· ≥ ·))

noncomputable def annihilation {U : Type*} [Fintype U] (H : SimpleGraph U) [DecidableRel H.Adj] :=
  sSup {k | k ≤ Fintype.card U ∧ (((univ.val.map (fun v => H.degree v)).sort (· ≤ ·)).take k).sum ≤
    H.edgeFinset.card}

private theorem list_degrees :
    (List.finRange 17).map (fun v => graph.degree v) = 16 :: List.replicate 16 1 := by decide

private theorem star_residue : residue graph = 16 := by
  unfold residue
  rw [Finset.val_univ_fin,Multiset.map_coe,Multiset.coe_sort,list_degrees]
  rw [List.mergeSort_eq_self (· ≥ ·) (by decide)]
  have desc (L : List ℕ) (h : List.Sorted (· ≥ ·) L) : descending L = L :=
    List.mergeSort_eq_self (· ≥ ·) h
  change residueAux 17 (16 :: List.replicate 16 1) = 16
  rw [residueAux,desc _ (by decide)]
  change residueAux 16 (List.replicate 16 0) = 16
  rw [residueAux,desc _ (by decide)]
  decide

private theorem annihilation_bound : annihilation graph ≤ 16 := by
  apply csSup_le (show {k | k ≤ Fintype.card V ∧ (((univ.val.map (fun v => graph.degree v)).sort (· ≤ ·)).take k).sum ≤ graph.edgeFinset.card}.Nonempty from ⟨0,by simp⟩)
  rintro k ⟨le,cost⟩
  change k ≤ 17 at le
  by_contra! large
  have eq : k=17 := by omega
  subst k
  rw [Finset.val_univ_fin,Multiset.map_coe,Multiset.coe_sort,list_degrees] at cost
  let L := (16 :: List.replicate 16 (1 : ℕ))
  let sorted := L.mergeSort (fun a b => decide (a ≤ b))
  have perm : sorted.Perm L := List.mergeSort_perm _ _
  have len : sorted.length = 17 := perm.length_eq.trans (by decide)
  have sum : sorted.sum = 32 := perm.sum_eq.trans (by decide)
  change (sorted.take 17).sum ≤ graph.edgeFinset.card at cost
  rw [List.take_of_length_le len.le,sum,show graph.edgeFinset.card = 16 by decide] at cost
  omega

def Outer {U : Type*} (H : SimpleGraph U) (S : Finset U) :=
  Dominates H S ∧ (H.induce (↑S : Set U)ᶜ).Connected
noncomputable def outer {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {k | ∃ S : Finset U, Outer H S ∧ S.card=k}

theorem star_outer : outer graph = 16 := by
  let costs := {k | ∃ S : Finset V, Outer graph S ∧ S.card=k}
  have feasible : Outer graph leaves := by
    constructor
    · intro v
      by_cases hv : v=0
      · subst v
        exact Or.inr ⟨1,by decide,by decide⟩
      · exact Or.inl (mem_erase.mpr ⟨hv,mem_univ _⟩)
    · let X : Set V := (↑leaves : Set V)ᶜ
      have zero (v : X) : v.val = 0 := by
        have := v.property
        simpa [X,leaves] using this
      haveI : Nonempty X := ⟨⟨0,by simp [X,leaves]⟩⟩
      change (graph.induce X).Connected
      refine ⟨fun x y => ?_⟩
      have h : x=y := Subtype.ext ((zero x).trans (zero y).symm)
      subst y
      exact .refl _
  have hit : 16 ∈ costs := ⟨leaves,feasible,by decide⟩
  obtain ⟨S,⟨dom,con⟩,eq⟩ := Nat.sInf_mem (show costs.Nonempty from ⟨_,hit⟩)
  apply le_antisymm (Nat.sInf_le (s := costs) hit)
  change 16 ≤ sInf costs
  rw [← eq]
  by_cases hub : (0 : V) ∈ S
  · let U := (S : Set V)ᶜ
    have no : graph.induce U = ⊥ := by
      ext x y
      change graph.Adj x.val y.val ↔ False
      constructor
      · rintro (h|h)
        · exact x.property (h.1 ▸ hub)
        · exact y.property (h.1 ▸ hub)
      · exact False.elim
    have same (x y : U) : x=y := by
      have reach := con x y
      change (graph.induce U).Reachable x y at reach
      rw [no] at reach
      exact reachable_bot.mp reach
    have cap : (univ \ S).card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      exact congrArg Subtype.val (same ⟨x,(mem_sdiff.mp hx).2⟩ ⟨y,(mem_sdiff.mp hy).2⟩)
    rw [card_sdiff (subset_univ S),card_univ,Fintype.card_fin] at cap
    omega
  · have sub : leaves ⊆ S := by
      intro v hv
      obtain inside | ⟨w,hw,e⟩ := dom v
      · exact inside
      · exact (hub ((leaf_neighbor (mem_erase.mp hv).1 e.symm) ▸ hw)).elim
    exact (show 16 = leaves.card by decide).trans_le (card_le_card sub)

abbrev Plane := ℝ × ℝ

/-- A topological drawing using distinct vertex points and embedded edge arcs.
Opposite orientations use the same arc in reverse. Each open edge misses every
vertex, and distinct undirected edges have disjoint open arcs. -/
structure PlaneDrawing {U : Type*} (G : SimpleGraph U) where
  pos : U → Plane
  pos_injective : Function.Injective pos
  arc : ∀ a b, G.Adj a b → Path (pos a) (pos b)
  embedded : ∀ a b (e : G.Adj a b), Topology.IsEmbedding (arc a b e)
  reverse_arc : ∀ a b (e : G.Adj a b), arc b a e.symm = (arc a b e).symm
  avoids_vertex : ∀ a b (e : G.Adj a b) (v : U) (s : I),
    0 < (s : ℝ) → (s : ℝ) < 1 → arc a b e s ≠ pos v
  interiors : ∀ a b c d (e : G.Adj a b) (f : G.Adj c d) (s t : I),
    0 < (s : ℝ) → (s : ℝ) < 1 → 0 < (t : ℝ) → (t : ℝ) < 1 →
    arc a b e s = arc c d f t → (a=c ∧ b=d) ∨ (a=d ∧ b=c)

/-- Usual planar-graph predicate, allowing arbitrary embedded arcs. -/
def Planar {U : Type*} (G : SimpleGraph U) : Prop := Nonempty (PlaneDrawing G)

private def grid (v : V) : ℤ × ℤ := ((v.val : ℤ),(v.val : ℤ)^2)

private def det {K : Type*} [CommRing K] (a b c : K × K) : K :=
  (b.1-a.1)*(c.2-a.2) - (b.2-a.2)*(c.1-a.1)

/-- Two points lie on one weak side of a line, with at least one strictly off it. -/
private def side {K : Type*} [Zero K] [LE K] [LT K] (u v : K) : Prop :=
  (0 ≤ u ∧ 0 ≤ v ∧ (0 < u ∨ 0 < v)) ∨ (u ≤ 0 ∧ v ≤ 0 ∧ (u < 0 ∨ v < 0))

private instance (u v : ℤ) : Decidable (side u v) := by unfold side; infer_instance

private theorem grid_injective : Function.Injective grid := by
  have h : ∀ u v : V, grid u = grid v → u = v := by decide
  exact fun _ _ => h _ _

private theorem grid_vertex : ∀ a b : V, graph.Adj a b → ∀ v : V,
    v ≠ a → v ≠ b → det (grid a) (grid b) (grid v) ≠ 0 := by decide

private theorem grid_edges : ∀ a b : V, graph.Adj a b → ∀ c d : V, graph.Adj c d →
    ¬((a=c ∧ b=d) ∨ (a=d ∧ b=c)) →
    side (det (grid a) (grid b) (grid c)) (det (grid a) (grid b) (grid d)) ∨
    side (det (grid c) (grid d) (grid a)) (det (grid c) (grid d) (grid b)) := by decide

noncomputable def point (v : V) : Plane := ((grid v).1, (grid v).2)

private theorem point_injective : Function.Injective point := by
  intro u v eq
  apply grid_injective
  simp only [point,Prod.mk.injEq] at eq
  exact Prod.ext (by exact_mod_cast eq.1) (by exact_mod_cast eq.2)

noncomputable def mix (a b : Plane) (s : ℝ) : Plane :=
  ((1-s)*a.1+s*b.1, (1-s)*a.2+s*b.2)

noncomputable def segmentPath (a b : Plane) : Path a b where
  toFun t := mix a b t
  continuous_toFun := by unfold mix; fun_prop
  source' := by simp [mix]
  target' := by simp [mix]

private theorem segment_injective {a b : Plane} (ne : a ≠ b) :
    Function.Injective (segmentPath a b) := by
  intro s t h
  by_contra distinct
  have st : (s : ℝ) - t ≠ 0 := sub_ne_zero.mpr (fun e => distinct (Subtype.ext e))
  apply ne
  have cancel (x y : ℝ) (h : (1-(s:ℝ))*x+s*y = (1-(t:ℝ))*x+t*y) : x=y := by
    have zero : ((s:ℝ)-t)*(y-x) = 0 := by linarith only [h]
    exact (sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left st)).symm
  exact Prod.ext (cancel _ _ (congrArg Prod.fst h)) (cancel _ _ (congrArg Prod.snd h))

private theorem det_mix (a b c d : Plane) (s : ℝ) :
    det a b (mix c d s) = (1-s)*det a b c + s*det a b d := by
  unfold det mix
  ring

private theorem det_on (a b : Plane) (s : ℝ) : det a b (mix a b s) = 0 := by
  rw [det_mix]
  unfold det
  ring

private theorem det_cast (a b c : V) :
    det (point a) (point b) (point c) = (det (grid a) (grid b) (grid c) : ℤ) := by
  unfold det point
  push_cast
  rfl

private theorem side_cast {u v : ℤ} (h : side u v) : side (u : ℝ) (v : ℝ) := by
  unfold side at h ⊢
  exact_mod_cast h

private theorem weighted_nonzero {u v s : ℝ} (h : side u v) (hs : 0<s) (ht : s<1) :
    (1-s)*u+s*v ≠ 0 := by
  have h' : 0 < 1-s := sub_pos.mpr ht
  rcases h with ⟨hu,hv,hp|hp⟩ | ⟨hu,hv,hn|hn⟩
  · exact ne_of_gt (add_pos_of_pos_of_nonneg (mul_pos h' hp) (mul_nonneg hs.le hv))
  · exact ne_of_gt (add_pos_of_nonneg_of_pos (mul_nonneg h'.le hu) (mul_pos hs hp))
  · exact ne_of_lt (add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg h' hn) (mul_nonpos_of_nonneg_of_nonpos hs.le hv))
  · exact ne_of_lt (add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos h'.le hu) (mul_neg_of_pos_of_neg hs hn))

private theorem different_points {a b : V} (e : graph.Adj a b) : point a ≠ point b :=
  fun h => e.ne (point_injective h)

/-- A common interior point is impossible when both endpoints of the second
segment lie on one weak side of the first line, at least one strictly. -/
private theorem exclude {a b c d : V} {s t : I}
    (h : side (det (grid a) (grid b) (grid c)) (det (grid a) (grid b) (grid d)))
    (ht : 0 < (t:ℝ)) (ht' : (t:ℝ) < 1)
    (meet : mix (point a) (point b) s = mix (point c) (point d) t) : False := by
  have eq := congrArg (det (point a) (point b)) meet
  rw [det_on,det_mix,det_cast,det_cast] at eq
  exact weighted_nonzero (side_cast h) ht ht' eq.symm

noncomputable def witnessDrawing : PlaneDrawing graph where
  pos := point
  pos_injective := point_injective
  arc a b _ := segmentPath (point a) (point b)
  embedded _ _ e := ((segmentPath _ _).continuous.isClosedEmbedding
    (segment_injective (different_points e))).isEmbedding
  reverse_arc := by
    intro a b _
    apply Path.ext
    funext t
    change mix (point b) (point a) t = mix (point a) (point b) (1-(t:ℝ))
    apply Prod.ext <;> change _ = _ <;> dsimp [mix] <;> ring
  avoids_vertex := by
    intro a b e v s hs ht meet
    let arc := segmentPath (point a) (point b)
    have inj := segment_injective (different_points e)
    by_cases va : v=a
    · subst v
      have h : s=0 := inj (meet.trans arc.source.symm)
      subst s
      norm_num at hs
    by_cases vb : v=b
    · subst v
      have h : s=1 := inj (meet.trans arc.target.symm)
      subst s
      norm_num at ht
    have eq := congrArg (det (point a) (point b)) meet
    change det _ _ (mix _ _ _) = _ at eq
    rw [det_on,det_cast] at eq
    exact grid_vertex a b e v va vb (by exact_mod_cast eq.symm)
  interiors := by
    intro a b c d e f s t hs hs' ht ht' meet
    by_contra diff
    rcases grid_edges a b e c d f diff with h | h
    · exact exclude h ht ht' meet
    · exact exclude h hs hs' meet.symm

theorem row2175_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Cograph H →
    (vertexCliqueCover H : ℚ) ≤ (7/9 : ℚ)*connectedForcing H+26/9) := by
  intro claim
  have bad := claim V graph (by decide) cograph
  rw [cover] at bad
  have h : (connectedForcing graph : ℚ) ≤ 16 := by exact_mod_cast connected_bound
  norm_num at bad
  linarith

theorem row2206_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → H.Connected → Planar H →
    (forcing H 2 : ℚ) ≤ (9/11 : ℚ)*annihilation H+6/11) := by
  intro claim
  have bad := claim V graph (by decide) connected ⟨witnessDrawing⟩
  rw [star_forcing.2] at bad
  have h : (annihilation graph : ℚ) ≤ 16 := by exact_mod_cast annihilation_bound
  norm_num at bad
  linarith

theorem row2417_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → H.IsTree →
    (forcing H 2 : ℚ) ≤ (11/13 : ℚ)*restrained H-9/13) := by
  intro claim
  have bad := claim V graph (by decide) tree
  rw [star_forcing.2] at bad
  have h : (restrained graph : ℚ) ≤ 17 := by exact_mod_cast restrained_bound
  norm_num at bad
  linarith

theorem row2494_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Cograph H → H.Connected →
    (outer H : ℚ) ≤ (10/11 : ℚ)*residue H+14/11) := by
  intro claim
  have bad := claim V graph (by decide) cograph connected
  rw [star_outer,star_residue] at bad
  norm_num at bad

theorem row2512_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Cograph H → H.IsTree →
    (vertexCliqueCover H : ℚ) ≤ (11/12 : ℚ)*connectedForcing H+13/12) := by
  intro claim
  have bad := claim V graph (by decide) cograph tree
  rw [cover] at bad
  have h : (connectedForcing graph : ℚ) ≤ 16 := by exact_mod_cast connected_bound
  norm_num at bad
  linarith

theorem row2577_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → H.Connected → Planar H →
    (forcing H 2 : ℚ) ≤ (4/13 : ℚ)*restrained H+96/13) := by
  intro claim
  have bad := claim V graph (by decide) connected ⟨witnessDrawing⟩
  rw [star_forcing.2] at bad
  have h : (restrained graph : ℚ) ≤ 17 := by exact_mod_cast restrained_bound
  norm_num at bad
  linarith

theorem row2580_false : ¬ (∀ (U : Type) [Fintype U] [DecidableEq U] (H : SimpleGraph U) [DecidableRel H.Adj],
    2 ≤ Fintype.card U → Bipartite H → Cograph H →
    (forcing H 1 : ℚ) ≤ (2/3 : ℚ)*forcing H 2+16/3) := by
  intro claim
  have bad := claim V graph (by decide) bipartite cograph
  rw [star_forcing.1,star_forcing.2] at bad
  norm_num at bad

#print axioms star_forcing
#print axioms star_outer
#print axioms witnessDrawing
#print axioms row2175_false
#print axioms row2206_false
#print axioms row2417_false
#print axioms row2494_false
#print axioms row2512_false
#print axioms row2577_false
#print axioms row2580_false
end StarCone
