import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Tauto
import Lean.Elab.Tactic.Omega

/-! Standalone for Lean 4.19.0 and Mathlib v4.19.0. -/

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

/-! Ján Pastorek, AutoGraphForge, commit 4d1a8afc99447cacd2328cca20e47b6493e8dbc5,
normalized line 377, raw line 394, record 80c8031c. -/
namespace AutoGraphForge377
open Finset SimpleGraph Graffiti372
variable {V : Type*} (G : SimpleGraph V)

/-- Source's IsClawFreeClass predicate. -/
def ClawFree := ∀ v a b c : V, G.Adj v a → G.Adj v b → G.Adj v c →
    a ≠ b → a ≠ c → b ≠ c → G.Adj a b ∨ G.Adj a c ∨ G.Adj b c

/-- Chordal graphs exclude all induced cycles of order at least four. -/
def Chordal : Prop := ∀ m : ℕ, 4 ≤ m → ¬∃ f : Fin m ↪ V, ∀ i j,
  G.Adj (f i) (f j) ↔ ((i.val + 1) % m = j.val ∨ (j.val + 1) % m = i.val)

variable [Fintype V] [DecidableRel G.Adj]

theorem maxDegree_le_cover_add_one (cf : ClawFree G) : G.maxDegree ≤ vertexCoverNumber G + 1 := by
  classical
  obtain ⟨C,cover,size⟩ := minVertexCover G
  rw [← size]
  apply G.maxDegree_le_of_forall_degree_le
  intro v
  let N := G.neighborFinset v
  change N.card ≤ C.card + 1
  by_cases hv : v ∈ C
  · have few : (N \ C).card ≤ 2 := by
      by_contra! big
      obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := two_lt_card_iff.mp big
      obtain ⟨va,oa⟩ := mem_sdiff.mp ha
      obtain ⟨vb,ob⟩ := mem_sdiff.mp hb
      obtain ⟨vc,oc⟩ := mem_sdiff.mp hc
      rcases cf v a b c ((G.mem_neighborFinset v a).mp va) ((G.mem_neighborFinset v b).mp vb)
        ((G.mem_neighborFinset v c).mp vc) ab ac bc with e | e | e
      · exact (cover e).elim oa ob
      · exact (cover e).elim oa oc
      · exact (cover e).elim ob oc
    have sub : N ∩ C ⊆ C.erase v := by
      intro x hx
      obtain ⟨xn,xc⟩ := mem_inter.mp hx
      apply mem_erase.mpr
      refine ⟨?_,xc⟩
      rintro rfl
      exact G.not_mem_neighborFinset_self x xn
    have small := card_le_card sub
    have erased := card_erase_add_one hv
    have split := card_sdiff_add_card_inter N C
    omega
  · have sub : N ⊆ C := fun x hx => (cover ((G.mem_neighborFinset v x).mp hx)).resolve_left hv
    exact (card_le_card sub).trans (Nat.le_succ _)

theorem survivor_line377 (_n : 2 ≤ Fintype.card V) (_chordal : Chordal G) (cf : ClawFree G) :
    G.maxDegree ≤ vertexCoverNumber G + 1 := maxDegree_le_cover_add_one G cf

#print axioms maxDegree_le_cover_add_one
#print axioms survivor_line377
end AutoGraphForge377
