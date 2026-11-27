/-
# Graffiti.pc #177: proof

Let A be a maximum independent set in a finite connected graph G with n≥2, let B=V\A, and let C1,...,Cm be the components of G[B]. Let s be the second-smallest degree with multiplicity. For any independent X⊆B, A∪X induces a bipartite graph, so b≥|A|+α(G[B]). In particular b≥|A|+m, with strict inequality if any component is not complete.

If |A|=1, G is complete and a spanning star proves the inequality. Hence assume |A|≥2. At most one vertex of G has degree <s. Choose a∈A with d(a)≥s; if any such high-degree vertex sees at least two components of G[B], choose one that does. Let r be the number of components met by N(a), so r≥1.

**Marked spanning-tree construction.** Start with the star at a, and mark its d(a) noncentral vertices, all in B. Grow a tree on B and some vertices of A, always preserving d(a) distinct marked leaves in B:
* Saturate within every reached component of G[B] by adding an edge from a current B vertex to a new B vertex. If the parent is marked, transfer its mark to the new vertex.
* If not all components are reached, there are x in a reached B component, y in an unreached one and c∈A adjacent to both. This follows by looking at the first move of a path from reached to unreached B; because A is independent this move passes through exactly one A vertex. Choose c and add the path x–c–y. It is a fresh connector: a has all its neighbors in initially reached components, and earlier connectors could conceivably see an unreached component unless all their neighboring components were attached when they were added. Therefore **attach all** unreached components adjacent to c at that step, by adding one edge from c to a B neighbor in each of those components. Add one edge from x to c, and if x is marked transfer that mark to any new B neighbor of c. Now c has no neighbors in unreached components, and is not a marked leaf. Saturate again within reached B components.

At completion the tree has vertex set B∪K with K⊆A, |K|≤1+m−r (a plus at most one connector per newly reached component). Choose s−1 marked leaves R, avoiding one neighbor q∈B of the possible low-degree vertex in A\K if necessary. This is possible since there are at least s distinct marks. Then D=(B∪K)\R induces a connected subgraph; each removed leaf has a retained neighbor (its parent). Every vertex of A\K of degree ≥s retains a neighbor, and so does the possible low-degree vertex by the choice of q. Hence D is connected dominating and admits a spanning tree with every vertex outside D a leaf (attach each as a pendant to any spanning tree on D). Thus L_s≥|A|−|K|+s−1≥|A|−m+s+r−2. The construction also works when s=1; no marked leaf is removed.

If r≥2 or if any component of G[B] is not complete, this already gives L_s+b≥2|A|+s.

In the remaining case each C_i is a clique and every high-degree vertex of A has its neighbors confined to one component. If m>1 there must be exactly one low-degree vertex c∈A and it must see every component: otherwise the auxiliary graph on components joined by a common neighbor in A is disconnected and so is G. Take K={c} if m>1 and K=∅ if m=1. In the clique C_i containing the neighbors of a, there are at least s vertices. Delete s−1 of them, retaining a neighbor of c there when c is needed, or a neighbor of the possible low-degree vertex when m=1 and that vertex is in A. All cliques stay nonempty, and the retained cliques connect through c if needed. The removed clique vertices and A\K are dominated just as before. This gives L_s≥|A|+s−1−|K|≥|A|+s−m, as needed.

Source: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
Prior weaker +1 bound: DeLaViña–Waller (2008), Theorem 3, https://www.combinatorics.org/ojs/index.php/eljc/article/download/v15i1r33/pdf

The live machine-readable catalogue marks #177 open, pending review. No priority claim is made.
The exact theorem is Graffiti177.conjecture177.
-/
/- Reproduce with Lean 4.19.0 and Mathlib v4.19.0: run this source with lake env lean. -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric

/- Proof module: Mark -/

open SimpleGraph Finset
set_option linter.unusedSectionVars false

namespace Graffiti177

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

abbrev Con (S : Finset V) := (G.induce (S : Set V)).Connected

lemma con_insert {S : Finset V} {x p : V} (h : Con G S)
    (hp : p ∈ S) (e : G.Adj x p) : Con G (insert x S) := by
  let inc : G.induce (S : Set V) →g G.induce (↑(insert x S) : Set V) :=
    (G.induceHomOfLE (show (S : Set V) ≤ ↑(insert x S) from fun _ hz =>
      Finset.mem_insert_of_mem hz)).toHom
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨inc ⟨p,hp⟩,fun y => ?_⟩
  rcases Finset.mem_insert.mp y.2 with hy | hy
  · exact (show (G.induce (↑(insert x S) : Set V)).Adj (inc ⟨p,hp⟩) y from
      by change G.Adj p y.1; rw [hy]; exact e.symm).reachable
  · exact (h ⟨p,hp⟩ ⟨y.1,hy⟩).map inc

lemma con_single (a : V) : Con G ({a} : Finset V) := by
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨a,by simp⟩,fun w => ?_⟩
  have h : w = ⟨a,by simp⟩ := Subtype.ext (Finset.mem_singleton.mp w.2)
  rw [h]

def Dominates (S : Finset V) (x : V) : Prop := ∃ y ∈ S, G.Adj x y

def Marked (S M : Finset V) : Prop :=
  M ⊆ S ∧ Con G (S \ M) ∧ ∀ v ∈ M, Dominates G (S \ M) v

lemma con_of_neighbors {D E : Finset V} (hD : Con G D) (hsub : D ⊆ E)
    (hver : ∀ v ∈ E, v ∉ D → Dominates G D v) : Con G E := by
  let inc : G.induce (D : Set V) →g G.induce (E : Set V) :=
    (G.induceHomOfLE (show (D : Set V) ≤ (E : Set V) from hsub)).toHom
  obtain ⟨r,hr⟩ := (connected_iff_exists_forall_reachable _).mp hD
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨inc r, fun y => ?_⟩
  by_cases hy : y.1 ∈ D
  · exact (hr ⟨y.1,hy⟩).map inc
  · obtain ⟨z,hz,hzy⟩ := hver y.1 y.2 hy
    exact ((hr ⟨z,hz⟩).map inc).trans
      (show (G.induce (E : Set V)).Adj (inc ⟨z,hz⟩) y from hzy.symm).reachable

lemma Marked.restrict {S M R : Finset V} (h : Marked G S M) (hR : R ⊆ M) :
    Marked G S R := by
  have hs : S \ M ⊆ S \ R := by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
      fun hr => (Finset.mem_sdiff.mp hx).2 (hR hr)⟩
  refine ⟨hR.trans h.1, con_of_neighbors G h.2.1 hs ?_, ?_⟩
  · intro x hx hnot
    apply h.2.2
    by_contra hm
    exact hnot (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,hm⟩)
  · intro x hx
    obtain ⟨y,hy,e⟩ := h.2.2 x (hR hx)
    exact ⟨y,hs hy,e⟩

lemma mark_grow_unmarked {S M : Finset V} {x p : V} (h : Marked G S M)
    (hx : x ∉ S) (hp : p ∈ S \ M) (e : G.Adj x p) :
    Marked G (insert x S) M := by
  have he : insert x S \ M = insert x (S \ M) := by
    ext v
    by_cases hv : v = x
    · subst v
      have hxm : x ∉ M := fun hxm => hx (h.1 hxm)
      simp [hxm]
    · simp [Finset.mem_insert,hv]
  refine ⟨fun _ hv => Finset.mem_insert_of_mem (h.1 hv), ?_, ?_⟩
  · rw [he]; exact con_insert G h.2.1 hp e
  · intro v hv
    obtain ⟨w,hw,f⟩ := h.2.2 v hv
    rw [he]
    exact ⟨w,Finset.mem_insert_of_mem hw,f⟩

lemma mark_grow_transfer {S M : Finset V} {x p : V} (h : Marked G S M)
    (hx : x ∉ S) (hp : p ∈ M) (e : G.Adj x p) :
    Marked G (insert x S) (insert x (M.erase p)) := by
  have he : insert x S \ insert x (M.erase p) = insert p (S \ M) := by
    ext v
    by_cases h1 : v = x
    · subst v
      have hn : x ≠ p := fun hh => hx (hh ▸ h.1 hp)
      simp [hn,hx]
    · by_cases h2 : v = p
      · subst v
        have hn : p ≠ x := fun hh => hx (hh ▸ h.1 hp)
        simp [hn,h.1 hp]
      · simp [Finset.mem_insert,h1,h2]
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp
    · exact Finset.mem_insert_of_mem (h.1 (Finset.mem_of_mem_erase hv))
  · obtain ⟨q,hq,f⟩ := h.2.2 p hp
    rw [he]
    exact con_insert G h.2.1 hq f
  · intro v hv
    rw [he]
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨p,by simp,e⟩
    · obtain ⟨w,hw,f⟩ := h.2.2 v (Finset.mem_of_mem_erase hv)
      exact ⟨w,Finset.mem_insert_of_mem hw,f⟩


lemma marked_star {B : Finset V} {a : V} (ha : a ∉ B)
    (he : ∀ v ∈ B, G.Adj a v) : Marked G (insert a B) B := by
  have eq : insert a B \ B = ({a} : Finset V) := by
    ext v
    by_cases h : v = a
    · subst v; simp [ha]
    · simp [Finset.mem_insert,h]
  refine ⟨fun _ h => Finset.mem_insert_of_mem h, ?_, ?_⟩
  · rw [eq]; exact con_single G a
  · intro v hv
    exact ⟨a,by rw [eq]; simp,(he v hv).symm⟩

lemma mark_grow_B {S M B : Finset V} {x p : V} (h : Marked G S M)
    (hM : M ⊆ B) (hx : x ∉ S) (hxB : x ∈ B) (hp : p ∈ S) (e : G.Adj x p) :
    ∃ M' ⊆ B, M'.card = M.card ∧ Marked G (insert x S) M' := by
  by_cases hm : p ∈ M
  · refine ⟨insert x (M.erase p),?_,?_,mark_grow_transfer G h hx hm e⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hxB
      · exact hM (Finset.mem_of_mem_erase hv)
    · rw [Finset.card_insert_of_not_mem (fun he => hx (h.1 (Finset.mem_of_mem_erase he))),
        Finset.card_erase_of_mem hm]
      have hp' := Finset.card_pos.mpr ⟨p,hm⟩
      omega
  · exact ⟨M,hM,rfl,mark_grow_unmarked G h hx (Finset.mem_sdiff.mpr ⟨hp,hm⟩) e⟩

lemma mark_grow_connector {S M B : Finset V} {x p c : V} (h : Marked G S M)
    (hM : M ⊆ B) (hx : x ∉ S) (hc : c ∉ S) (hcB : c ∉ B) (hxB : x ∈ B)
    (hp : p ∈ S) (hpc : G.Adj c p) (hcx : G.Adj x c) :
    ∃ M' ⊆ B, M'.card = M.card ∧ Marked G (insert x (insert c S)) M' := by
  have hcne : x ≠ c := fun h => hcB (h ▸ hxB)
  by_cases hpM : p ∈ M
  · obtain ⟨q,hq,hqp⟩ := h.2.2 p hpM
    have hcM : c ∉ M := fun he => hc (h.1 he)
    have eq : insert c S \ M.erase p = insert c (insert p (S \ M)) := by
      ext v
      by_cases h1 : v = c
      · subst v; simp [hcM]
      · by_cases h2 : v = p
        · subst v; simp [hp]
        · simp [Finset.mem_insert,h1,h2]
    have hmid : Marked G (insert c S) (M.erase p) := by
      refine ⟨fun v hv => Finset.mem_insert_of_mem (h.1 (Finset.mem_of_mem_erase hv)),?_,?_⟩
      · rw [eq]
        exact con_insert G (con_insert G h.2.1 hq hqp) (Finset.mem_insert_self _ _) hpc
      · intro v hv
        obtain ⟨z,hz,e⟩ := h.2.2 v (Finset.mem_of_mem_erase hv)
        rw [eq]
        exact ⟨z,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz),e⟩
    let M' := insert x (M.erase p)
    refine ⟨M',?_,?_,?_⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hxB
      · exact hM (Finset.mem_of_mem_erase hv)
    · dsimp [M']
      rw [Finset.card_insert_of_not_mem (fun he => hx (h.1 (Finset.mem_of_mem_erase he))),
        Finset.card_erase_of_mem hpM]
      have hp' := Finset.card_pos.mpr ⟨p,hpM⟩
      omega
    · have eq' : insert x (insert c S) \ M' = insert c S \ M.erase p := by
        ext v
        by_cases ev : v = x
        · subst v; simp [M',hcne,hx,Finset.mem_insert]
        · simp [M',Finset.mem_insert,ev]
      refine ⟨?_,?_,?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · simp
        · exact Finset.mem_insert_of_mem (hmid.1 hv)
      · rw [eq']; exact hmid.2.1
      · intro v hv
        rw [eq']
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact ⟨c,Finset.mem_sdiff.mpr ⟨by simp, fun he => hcM (Finset.mem_of_mem_erase he)⟩,hcx⟩
        · exact hmid.2.2 v hv
  · have hmid := mark_grow_unmarked G h hc (Finset.mem_sdiff.mpr ⟨hp,hpM⟩) hpc
    exact mark_grow_B G hmid hM (by simp [Finset.mem_insert,hcne,hx]) hxB (by simp) hcx

end Graffiti177

/- Proof module: Reps -/
set_option warningAsError true
set_option linter.unusedSectionVars false
open Finset

namespace Graffiti177
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

noncomputable def compCount (B : Finset V) : Nat :=
  Nat.card ((G.induce (B : Set V)).ConnectedComponent)

def Indep (X : Finset V) : Prop :=
  ∀ u ∈ X, ∀ v ∈ X, u ≠ v → ¬ G.Adj u v

private theorem image_of_reps (B : Finset V)
    (r : (G.induce (B : Set V)).ConnectedComponent → (B : Set V))
    (hr : ∀ c, (G.induce (B : Set V)).connectedComponentMk (r c) = c) :
    ∃ X ⊆ B, Indep G X ∧ X.card = compCount G B ∧
      (∀ c, (r c).val ∈ X) ∧
      ∀ x ∈ X, ∃ c, (r c).val = x := by
  classical
  let H := G.induce (B : Set V)
  letI : Finite H.ConnectedComponent := Finite.of_surjective H.connectedComponentMk
    (fun c => ⟨r c, hr c⟩)
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  let f : H.ConnectedComponent → V := fun c => (r c).1
  have hInj : Function.Injective f := by
    intro a b h
    have hes : r a = r b := Subtype.ext h
    exact (hr a).symm.trans ((congrArg H.connectedComponentMk hes).trans (hr b))
  let X := Finset.univ.image f
  refine ⟨X,?_,?_,?_,?_,?_⟩
  · intro u hu
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hu
    exact (r c).property
  · intro u hu v hv ne edge
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hv
    have e : H.Adj (r c) (r d) := edge
    have h := SimpleGraph.ConnectedComponent.sound e.reachable
    rw [hr c,hr d] at h
    exact ne (congrArg f h)
  · unfold X
    rw [Finset.card_image_of_injOn hInj.injOn]
    simp [compCount,H,Nat.card_eq_fintype_card]
  · intro c
    exact Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩
  · intro x hx
    obtain ⟨c,_,h⟩ := Finset.mem_image.mp hx
    exact ⟨c,h⟩

/-- Representatives of the induced components form one independent set. -/
theorem independentReps (B : Finset V) :
    ∃ X ⊆ B, Indep G X ∧ X.card = compCount G B := by
  classical
  let H := G.induce (B : Set V)
  have h (c : H.ConnectedComponent) : ∃ e, H.connectedComponentMk e = c := Quot.exists_rep c
  let rep (c : H.ConnectedComponent) := Classical.choose (h c)
  have hr (c : H.ConnectedComponent) : H.connectedComponentMk (rep c) = c :=
    Classical.choose_spec (h c)
  obtain ⟨X,hX,hi,hcard,_,_⟩ := image_of_reps G B rep hr
  exact ⟨X,hX,hi,hcard⟩

/-- In a noncomplete component, two nonadjacent vertices can be selected
instead of one representative. -/
theorem independentRepsPlus (B : Finset V) (u v : (B : Set V))
    (hR : (G.induce (B : Set V)).Reachable u v) (hne : u ≠ v)
    (hNA : ¬ G.Adj u.val v.val) :
    ∃ X ⊆ B, Indep G X ∧ compCount G B + 1 ≤ X.card := by
  classical
  let H := G.induce (B : Set V)
  let A := H.connectedComponentMk u
  have h (c : H.ConnectedComponent) : ∃ e, H.connectedComponentMk e = c := Quot.exists_rep c
  let rep (c : H.ConnectedComponent) := if c = A then u else Classical.choose (h c)
  have hr (c : H.ConnectedComponent) : H.connectedComponentMk (rep c) = c := by
    by_cases e : c = A
    · simp [rep,e,A]
    · simpa [rep,e] using Classical.choose_spec (h c)
  obtain ⟨X,hX,hi,hcard,_,hall⟩ := image_of_reps G B rep hr
  have hvA : H.connectedComponentMk v = A :=
    SimpleGraph.ConnectedComponent.sound hR.symm
  have hnot : v.val ∉ X := by
    intro hV
    obtain ⟨c,he⟩ := hall v.val hV
    have hes : rep c = v := Subtype.ext he
    have hc : c = A := (hr c).symm.trans ((congrArg H.connectedComponentMk hes).trans hvA)
    have hU : rep c = u := by simp [rep,hc]
    exact hne (hU.symm.trans hes)
  have hno (x : V) (hx : x ∈ X) : ¬ G.Adj x v.val := by
    intro e
    obtain ⟨c,he⟩ := hall x hx
    have e' : H.Adj (rep c) v := by
      change G.Adj (rep c).val v.val
      rwa [he]
    have hcv := SimpleGraph.ConnectedComponent.sound e'.reachable
    rw [hr c,hvA] at hcv
    have hu : rep c = u := by simp [rep,hcv]
    have hv' : G.Adj (rep c).val v.val := e'
    rw [hu] at hv'
    exact hNA hv'
  refine ⟨insert v.val X,Finset.insert_subset_iff.mpr ⟨v.property,hX⟩,?_,?_⟩
  · intro x hx y hy hxy e
    rcases Finset.mem_insert.mp hx with eq | hx
    · subst x
      rcases Finset.mem_insert.mp hy with eq | hy
      · exact hxy eq.symm
      · exact hno y hy e.symm
    · rcases Finset.mem_insert.mp hy with eq | hy
      · subst y
        exact hno x hx e
      · exact hi x hx y hy hxy e
  · rw [Finset.card_insert_of_not_mem hnot,hcard]

end Graffiti177

/- Proof module: Grow -/
open SimpleGraph Finset
set_option linter.unusedSectionVars false

namespace Graffiti177
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

lemma walk_closed {P : V → Prop} (h : ∀ {a b}, G.Adj a b → P a → P b)
    {a b : V} (p : G.Walk a b) (ha : P a) : P b := by
  induction p with
  | nil => exact ha
  | cons e p ih => exact ih (h e ha)

lemma cross_B (B S : Finset V) (hc : G.Connected)
    (hA : Indep G (univ \ B)) (hS : S.Nonempty) (hB : ¬ B ⊆ S)
    (hd : ¬ ∃ x ∈ B, x ∉ S ∧ ∃ p ∈ S, G.Adj x p) :
    ∃ x ∈ B, x ∉ S ∧ ∃ c ∉ B, c ∉ S ∧ ∃ p ∈ S, G.Adj c p ∧ G.Adj x c := by
  classical
  by_contra H
  let P (v : V) := v ∈ S ∨ v ∉ B ∧ ∃ p ∈ S, G.Adj v p
  have cl {u v : V} (e : G.Adj u v) (hu : P u) : P v := by
    by_cases hv : v ∈ S
    · exact Or.inl hv
    rcases hu with hu | ⟨huB,p,hp,f⟩
    · by_cases hvB : v ∈ B
      · exact False.elim (hd ⟨v,hvB,hv,u,hu,e.symm⟩)
      · exact Or.inr ⟨hvB,u,hu,e.symm⟩
    · by_cases hvB : v ∈ B
      · by_cases huc : u ∈ S
        · exact False.elim (hd ⟨v,hvB,hv,u,huc,e.symm⟩)
        · exact False.elim (H ⟨v,hvB,hv,u,huB,huc,p,hp,f,e.symm⟩)
      · exact False.elim (hA u (by simp [huB]) v (by simp [hvB]) e.ne e)
  obtain ⟨r,hr⟩ := hS
  obtain ⟨b,hb,hn⟩ := Finset.not_subset.mp hB
  obtain ⟨p⟩ := hc r b
  rcases walk_closed G cl p (Or.inl hr) with hm | ⟨he,_⟩
  · exact hn hm
  · exact he hb

noncomputable def seen (B S : Finset V) :
    Finset ((G.induce (B : Set V)).ConnectedComponent) := by
  classical
  exact (B.attach.filter (fun x => x.val ∈ S)).image (G.induce (B : Set V)).connectedComponentMk

lemma mem_seen {B S : Finset V} {c : (G.induce (B : Set V)).ConnectedComponent} :
    c ∈ seen G B S ↔ ∃ x : (B : Set V), x.val ∈ S ∧
      (G.induce (B : Set V)).connectedComponentMk x = c := by
  classical
  simp [seen]

lemma seen_mono {B S T : Finset V} (h : S ⊆ T) : seen G B S ⊆ seen G B T := by
  intro c hc
  obtain ⟨v,hv,hc⟩ := (mem_seen G).mp hc
  exact (mem_seen G).mpr ⟨v,h hv,hc⟩

lemma seen_card (B S : Finset V) : (seen G B S).card ≤ compCount G B := by
  classical
  let H := G.induce (B : Set V)
  letI : Finite H.ConnectedComponent :=
    Finite.of_surjective H.connectedComponentMk (fun c => c.exists_rep)
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  have h := Finset.card_le_card (Finset.subset_univ (seen G B S))
  simpa [compCount,H,Nat.card_eq_fintype_card] using h

lemma new_class {B S : Finset V} {x : V} (hx : x ∈ B) (hn : x ∉ S)
    (hd : ¬ ∃ x ∈ B, x ∉ S ∧ ∃ p ∈ S, G.Adj x p) :
    (G.induce (B : Set V)).connectedComponentMk ⟨x,hx⟩ ∉ seen G B S := by
  intro h
  obtain ⟨v,hv,he⟩ := (mem_seen G).mp h
  obtain ⟨p⟩ := ConnectedComponent.exact he
  refine hn (walk_closed (G.induce (B : Set V)) (P := fun v => v.val ∈ S) ?_ p hv)
  intro u w e hu
  by_contra hw
  exact hd ⟨w.val,w.property,hw,u.val,hu,(show G.Adj u.val w.val from e).symm⟩

lemma grow_cover (B : Finset V) (hc : G.Connected) (hA : Indep G (univ \ B))
    (S M : Finset V) (hS : S.Nonempty) (hM : M ⊆ B) (h : Marked G S M) :
    ∃ E N : Finset V, B ⊆ E ∧ N ⊆ B ∧ N.card = M.card ∧ Marked G E N ∧
      (E \ B).card + (seen G B S).card ≤ (S \ B).card + compCount G B := by
  classical
  generalize hr : Fintype.card V - S.card = r
  induction r using Nat.strong_induction_on generalizing S M with
  | h r ih =>
    by_cases hB : B ⊆ S
    · exact ⟨S,M,hB,hM,rfl,h,Nat.add_le_add_left (seen_card G B S) _⟩
    by_cases hd : ∃ x ∈ B, x ∉ S ∧ ∃ p ∈ S, G.Adj x p
    · obtain ⟨x,hx,hn,p,hp,e⟩ := hd
      obtain ⟨N,hN,hcn,hm⟩ := mark_grow_B G h hM hn hx hp e
      let T := insert x S
      have hST : S ⊆ T := Finset.subset_insert _ _
      have ht : T.card = S.card + 1 := Finset.card_insert_of_not_mem hn
      have htle : T.card ≤ Fintype.card V := Finset.card_le_univ _
      have htr : Fintype.card V - T.card < r := by omega
      obtain ⟨E,J,hBE,hJB,hJ,he,hcount⟩ :=
        ih _ htr T N (hS.mono hST) hN hm rfl
      have heq : T \ B = S \ B := by
        ext v
        by_cases hv : v = x
        · subst v; simp [hx]
        · simp [T,Finset.mem_insert,hv]
      rw [heq] at hcount
      have hic := Finset.card_le_card (seen_mono G (B := B) hST)
      exact ⟨E,J,hBE,hJB,hJ.trans hcn,he,by omega⟩
    · obtain ⟨x,hx,hn,c,hcB,hcS,p,hp,e,f⟩ := cross_B G B S hc hA hS hB hd
      obtain ⟨N,hN,hcn,hm⟩ := mark_grow_connector G h hM hn hcS hcB hx hp e f
      let T := insert x (insert c S)
      have hST : S ⊆ T := (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
      have hxc : x ≠ c := fun he => hcB (he ▸ hx)
      have ht : T.card = S.card + 2 := by
        dsimp [T]
        rw [Finset.card_insert_of_not_mem (by simp [hxc,hn]),Finset.card_insert_of_not_mem hcS]
      have htle : T.card ≤ Fintype.card V := Finset.card_le_univ _
      have htr : Fintype.card V - T.card < r := by omega
      obtain ⟨E,J,hBE,hJB,hJ,he,hcount⟩ :=
        ih _ htr T N (hS.mono hST) hN hm rfl
      have heq : T \ B = insert c (S \ B) := by
        ext v
        by_cases hv : v = x
        · subst v; simp [hx,hxc]
        · by_cases hv' : v = c
          · subst v; simp [T,hcB]
          · simp [T,Finset.mem_insert,hv,hv']
      rw [heq,Finset.card_insert_of_not_mem (by simp [hcS])] at hcount
      let C := (G.induce (B : Set V)).connectedComponentMk ⟨x,hx⟩
      have hcc : C ∉ seen G B S := new_class G hx hn hd
      have hmem : C ∈ seen G B T := (mem_seen G).mpr ⟨⟨x,hx⟩,by simp [T],rfl⟩
      have hsub : insert C (seen G B S) ⊆ seen G B T :=
        Finset.insert_subset_iff.mpr ⟨hmem,seen_mono G hST⟩
      have hic := Finset.card_le_card hsub
      rw [Finset.card_insert_of_not_mem hcc] at hic
      exact ⟨E,J,hBE,hJB,hJ.trans hcn,he,by omega⟩
end Graffiti177

/- Proof module: Bound -/
open SimpleGraph Finset
set_option linter.unusedSectionVars false

namespace Graffiti177
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def leaves (T : SimpleGraph V) : Finset V := by
  classical exact univ.filter (fun v => T.degree v = 1)

noncomputable def maxLeaves : ℕ := by
  classical
  exact ((Finset.univ : Finset (SimpleGraph V)).filter
    (fun T => T ≤ G ∧ T.IsTree)).sup (fun T => (leaves T).card)

noncomputable def independence : ℕ := by
  classical exact ((Finset.univ : Finset (Finset V)).filter (Indep G)).sup Finset.card

def TwoColor (W : Finset V) : Prop :=
  ∃ X Y : Finset V, Disjoint X Y ∧ X ∪ Y = W ∧ Indep G X ∧ Indep G Y

noncomputable def bipartiteNum : ℕ := by
  classical exact ((Finset.univ : Finset (Finset V)).filter (TwoColor G)).sup Finset.card

lemma bip_bound {A X : Finset V} (hA : Indep G A) (hX : Indep G X)
    (h : Disjoint A X) : A.card + X.card ≤ bipartiteNum G := by
  classical
  rw [← Finset.card_union_of_disjoint h]
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,A,X,h,rfl,hA,hX⟩)

lemma exists_max_indep : ∃ A : Finset V, Indep G A ∧ A.card = independence G := by
  classical
  have h0 : Indep G (∅ : Finset V) := by simp [Indep]
  obtain ⟨A,hA,he⟩ := Finset.exists_mem_eq_sup
    (s := (Finset.univ : Finset (Finset V)).filter (Indep G))
    (f := Finset.card) ⟨∅,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h0⟩⟩
  exact ⟨A,(Finset.mem_filter.mp hA).2,he.symm⟩

lemma indep_card_le {A : Finset V} (h : Indep G A) : A.card ≤ independence G := by
  classical
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)

lemma exists_adj (hc : G.Connected) (hn : 1 < Fintype.card V) (v : V) :
    ∃ w, G.Adj v w := by
  obtain ⟨u,w,hh⟩ := Fintype.one_lt_card_iff.mp hn
  have hl : ∃ x, x ≠ v := by
    by_cases he : u = v
    · exact ⟨w,by intro hf; exact hh (he.trans hf.symm)⟩
    · exact ⟨u,he⟩
  obtain ⟨x,hx⟩ := hl
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist v x
  have hp' : 0 < p.length := by rw [hp]; exact hc.pos_dist_of_ne hx.symm
  exact ⟨p.getVert 1, by simpa using p.adj_getVert_succ (i := 0) hp'⟩

lemma conDom_leaves (D : Finset V) (hc : Con G D)
    (hD : ∀ v ∉ D, Dominates G D v) : (univ \ D).card ≤ maxLeaves G := by
  classical
  let par (v : V) : V := if h : v ∉ D then (hD v h).choose else v
  have hpar (v : V) (hv : v ∉ D) : par v ∈ D ∧ G.Adj v (par v) := by
    simpa [par,hv] using (hD v hv).choose_spec
  let H : SimpleGraph V :=
    { Adj := fun u v => G.Adj u v ∧
        ((u ∈ D ∧ v ∈ D) ∨ (u ∉ D ∧ par u = v) ∨ (v ∉ D ∧ par v = u))
      symm := by
        intro u v h
        obtain ⟨huv, h | h | h⟩ := h
        · exact ⟨huv.symm, Or.inl h.symm⟩
        · exact ⟨huv.symm, Or.inr (Or.inr h)⟩
        · exact ⟨huv.symm, Or.inr (Or.inl h)⟩
      loopless := fun u h => G.loopless u h.1 }
  let inc : G.induce (D : Set V) →g H :=
    ⟨fun v => v.1, fun {a b} h => ⟨h,Or.inl ⟨a.2,b.2⟩⟩⟩
  let lift (v : V) : ↥(D : Set V) :=
    if h : v ∈ D then ⟨v,h⟩ else ⟨par v,(hpar v h).1⟩
  have reach (v : V) : H.Reachable v (lift v).1 := by
    by_cases h : v ∈ D
    · have he : (lift v).1 = v := by simp [lift,h]
      rw [he]
    · have he : (lift v).1 = par v := by simp [lift,h]
      rw [he]
      exact (show H.Adj v (par v) from ⟨(hpar v h).2, Or.inr (Or.inl ⟨h,rfl⟩)⟩).reachable
  have hH : H.Connected := by
    have : Nonempty V := ⟨(Classical.choice hc.nonempty).1⟩
    refine ⟨fun u v => ?_⟩
    exact (reach u).trans (((hc (lift u) (lift v)).map inc).trans (reach v).symm)
  obtain ⟨T, hT, ht⟩ := hH.exists_isTree_le
  have hTG : T ≤ G := fun _ _ h => (hT h).1
  have hleaf : (Finset.univ : Finset V) \ D ⊆ leaves T := by
    intro v hv
    have hn : v ∉ D := (Finset.mem_sdiff.mp hv).2
    have hpne : v ≠ par v := fun h => hn (h ▸ (hpar v hn).1)
    obtain ⟨p,hp⟩ := ht.isConnected.exists_walk_length_eq_dist v (par v)
    have hpos : 0 < p.length := by rw [hp]; exact ht.isConnected.pos_dist_of_ne hpne
    have hz : T.Adj v (p.getVert 1) := by simpa using p.adj_getVert_succ (i := 0) hpos
    have single {w : V} (h : T.Adj v w) : w = par v := by
      rcases (hT h).2 with h' | h' | h'
      · exact (hn h'.1).elim
      · exact h'.2.symm
      · exact (hn (h'.2 ▸ (hpar w h'.1).1)).elim
    have hs : T.neighborFinset v = {par v} := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
      exact ⟨single, fun h => by rwa [h, ← single hz]⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← T.card_neighborFinset_eq_degree,hs,Finset.card_singleton]
  exact (Finset.card_le_card hleaf).trans (Finset.le_sup
    (f := fun T => (leaves T).card) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hTG,ht⟩))

lemma generalCore (A : Finset V) (hA : Indep G A) (hc : G.Connected)
    (hn : 1 < Fintype.card V) (s : ℕ) (hs : 1 ≤ s) (a z : V) (ha : a ∈ A)
    (hsa : s ≤ G.degree a) (hz : ∀ v ≠ z, s ≤ G.degree v) :
    ∃ D : Finset V, Con G D ∧ (∀ v ∉ D, Dominates G D v) ∧
      A.card + s + (seen G (univ \ A) (insert a (G.neighborFinset a))).card
        ≤ (univ \ D).card + compCount G (univ \ A) + 2 := by
  classical
  let B := (Finset.univ : Finset V) \ A
  let M := G.neighborFinset a
  let S := insert a M
  have hB : Finset.univ \ B = A := by ext v; simp [B]
  have haB : a ∉ B := by simp [B,ha]
  have hM : M ⊆ B := by
    intro x hx
    have e : G.Adj a x := (G.mem_neighborFinset a x).mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hm => hA a ha x hm e.ne e⟩
  have hm : Marked G S M := marked_star G (by simp [M])
    (fun x hv => (G.mem_neighborFinset a x).mp hv)
  obtain ⟨E,N,hBE,hNB,hN,he,hcount⟩ :=
    grow_cover G B hc (by rwa [hB]) S M (by exact ⟨a,by simp [S]⟩) hM hm
  have hsb : S \ B = {a} := by
    ext v
    by_cases hv : v = a
    · subst v; simp [S,haB]
    · by_cases hvM : v ∈ M
      · simp [hv,hM hvM]
      · simp [S,Finset.mem_insert,hv,hvM]
  rw [hsb,Finset.card_singleton] at hcount
  have hnc : s ≤ N.card := by rw [hN]; simpa [M] using hsa
  let avoid : V := if h : z ∉ E then (exists_adj G hc hn z).choose else a
  have haz : z ∉ E → G.Adj z avoid := by
    intro hzE
    simp only [avoid,dif_pos hzE]
    exact (exists_adj G hc hn z).choose_spec
  have herr := Finset.card_erase_le (s := N) (a := avoid)
  have hdiff : s-1 ≤ (N.erase avoid).card := by
    by_cases haN : avoid ∈ N
    · rw [Finset.card_erase_of_mem haN]; omega
    · rw [Finset.erase_eq_of_not_mem haN]; omega 
  obtain ⟨R,hRa,hRc⟩ := Finset.exists_subset_card_eq hdiff
  have hRN : R ⊆ N := hRa.trans (Finset.erase_subset _ _)
  let D := E \ R
  have hmark := Marked.restrict G he hRN
  have hRE : R ⊆ E := hRN.trans he.1
  have hRB : R ⊆ B := hRN.trans hNB
  have hd : ∀ v ∉ D, Dominates G D v := by
    intro v hv
    by_cases hvR : v ∈ R
    · exact hmark.2.2 v hvR
    have hve : v ∉ E := fun hvE => hv (Finset.mem_sdiff.mpr ⟨hvE,hvR⟩)
    have hva : v ∈ A := by
      by_cases ha' : v ∈ A
      · exact ha'
      · exact False.elim (hve (hBE (by simp [B,ha'])))
    have adjB (w : V) (e : G.Adj v w) : w ∈ B := by
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hw => hA v hva w hw e.ne e⟩
    by_cases hvz : v = z
    · subst v
      exact ⟨avoid,Finset.mem_sdiff.mpr ⟨hBE (adjB _ (haz hve)),
        fun h => Finset.not_mem_erase _ _ (hRa h)⟩, haz hve⟩
    · have hdeg := hz v hvz
      have hex : ∃ w ∈ G.neighborFinset v, w ∉ R := by
        by_contra h
        have hsub : G.neighborFinset v ⊆ R := by
          intro w hw
          exact Classical.byContradiction (fun hn => h ⟨w,hw,hn⟩)
        have hcard := Finset.card_le_card hsub
        rw [G.card_neighborFinset_eq_degree, hRc] at hcard
        omega
      obtain ⟨w,hw,hwr⟩ := hex
      have e := (G.mem_neighborFinset v w).mp hw
      exact ⟨w,Finset.mem_sdiff.mpr ⟨hBE (adjB _ e),hwr⟩,e⟩
  have hE : B.card + (E \ B).card = E.card :=
    by simpa [Nat.add_comm] using (Finset.card_sdiff_add_card_eq_card hBE)
  have hV : A.card + B.card = Fintype.card V := by
    simpa [B,Nat.add_comm] using (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A))
  have hDC : D.card = E.card - R.card := Finset.card_sdiff hRE
  have hV2 : D.card + (univ \ D).card = Fintype.card V := by
    simpa [Nat.add_comm] using (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D))
  have hrc := Finset.card_le_card hRE
  exact ⟨D,hmark.2.1,hd,by change A.card + s + (seen G B S).card ≤ (univ \ D).card + compCount G B + 2; omega⟩

end Graffiti177

/- Proof module: Clq -/
open SimpleGraph Finset
namespace Graffiti177

private lemma weakConnected {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hc : G.Connected) (f : V → W) (hSurj : Function.Surjective f)
    (he : ∀ {u v}, G.Adj u v → f u = f v ∨ H.Adj (f u) (f v)) : H.Connected := by
  have path {u v} (w : G.Walk u v) : H.Reachable (f u) (f v) := by
    induction w with
    | nil => exact ⟨Walk.nil⟩
    | cons e _ ih =>
      rcases he e with h | h
      · simpa only [h] using ih
      · exact h.reachable.trans ih
  obtain ⟨x⟩ := hc.nonempty
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨f x, fun v => ?_⟩
  obtain ⟨y,rfl⟩ := hSurj v
  obtain ⟨w⟩ := hc x y
  exact path w

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cliqueCore (A B : Finset V) (s : ℕ) (z : V)
    (hB : B = univ \ A) (hInd : Indep G A) (hc : G.Connected)
    (hn : 1 < Fintype.card V) (hs : 1 ≤ s) (hAnchor : ∃ a ∈ A, s ≤ G.degree a)
    (hAll : ∀ v, v ≠ z → s ≤ G.degree v)
    (hClq : ∀ u v : ↥(B : Set V), (G.induce (B : Set V)).Reachable u v →
      u ≠ v → G.Adj u.val v.val)
    (hHigh : ∀ a ∈ A, s ≤ G.degree a → ∀ u v : ↥(B : Set V), G.Adj a u.val →
      G.Adj a v.val → (G.induce (B : Set V)).Reachable u v) :
    ∃ D : Finset V, Con G D ∧ (∀ v, v ∉ D → Dominates G D v) ∧
      A.card + s ≤ (univ \ D).card + compCount G B := by
  classical
  let H := G.induce (B : Set V)
  have biff (v : V) : v ∈ B ↔ v ∉ A := by simp [hB]
  have nbA {x y} (hx : x ∈ A) (e : G.Adj x y) : y ∈ B :=
    (biff y).mpr (fun hy => hInd x hx y hy e.ne e)
  have nbExists (x : V) (hx : x ∈ A) : ∃ y : ↥(B : Set V), G.Adj x y.val := by
    obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hn x
    obtain ⟨p⟩ := hc x w
    cases p with
    | nil => exact (hw rfl).elim
    | @cons _ y _ e _ => exact ⟨⟨y,nbA hx e⟩,e⟩
  obtain ⟨a, ha, has⟩ := hAnchor
  obtain ⟨u, eu⟩ := nbExists a ha
  letI : Finite H.ConnectedComponent :=
    Finite.of_surjective H.connectedComponentMk (fun c => Quot.exists_rep c)
  letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  have hm : compCount G B = Fintype.card H.ConnectedComponent := Nat.card_eq_fintype_card
  have hmp : 1 ≤ compCount G B := by
    rw [hm]
    haveI : Nonempty H.ConnectedComponent := ⟨H.connectedComponentMk u⟩
    exact Fintype.card_pos
  let D0 := if 1 < compCount G B then insert z B else B
  have b0 : B ⊆ D0 := by
    intro x hx
    by_cases h : 1 < compCount G B <;> simp [D0,h,hx]
  have outA {x} (hx : x ∉ D0) : x ∈ A := by
    by_contra hnA
    exact hx (b0 ((biff x).mpr hnA))
  have onlyz {x} (hx : x ∈ D0) (hnB : x ∉ B) : x = z := by
    by_cases h : 1 < compCount G B
    · simpa [D0,h,hnB] using hx
    · exact (hnB (by simpa [D0,h] using hx)).elim
  have hD0 : Con G D0 := by
    by_cases hmBig : 1 < compCount G B
    · have z0 : z ∈ D0 := by simp [D0,hmBig]
      let f : V → ↥(D0 : Set V) := fun x =>
        if hx : x ∈ D0 then ⟨x,hx⟩ else
          ⟨(Classical.choose (nbExists x (outA hx))).val,
            b0 (Classical.choose (nbExists x (outA hx))).property⟩
      have one {x y} (hx : x ∉ D0) (hy : y ∈ D0) (e : G.Adj x y) :
          f x = f y ∨ (G.induce (D0 : Set V)).Adj (f x) (f y) := by
        have hb := nbA (outA hx) e
        let k := Classical.choose (nbExists x (outA hx))
        have ek : G.Adj x k.val := Classical.choose_spec (nbExists x (outA hx))
        by_cases eq : k = (⟨y,hb⟩ : ↥(B : Set V))
        · left
          apply Subtype.ext
          simpa [f,hx,hy,k] using congrArg Subtype.val eq
        · right
          have hr := hHigh x (outA hx) (hAll x (fun h => hx (h ▸ z0))) k ⟨y,hb⟩ ek e
          have hed := hClq k ⟨y,hb⟩ hr eq
          change G.Adj (f x).val (f y).val
          simpa [f,hx,hy,k] using hed
      apply weakConnected hc f
      · intro x
        exact ⟨x.val, by simp [f, show x.val ∈ D0 from x.property]⟩
      · intro x y e
        by_cases hx : x ∈ D0 <;> by_cases hy : y ∈ D0
        · right
          change G.Adj (f x).val (f y).val
          simpa [f,hx,hy] using e
        · exact (one hy hx e.symm).elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
        · exact one hx hy e
        · exact (hy (b0 (nbA (outA hx) e))).elim
    · have hle : Fintype.card H.ConnectedComponent ≤ 1 := by omega
      haveI := Fintype.card_le_one_iff_subsingleton.mp hle
      have hcon : H.Connected := (connected_iff_exists_forall_reachable _).mpr
        ⟨u, fun v => SimpleGraph.ConnectedComponent.eq.mp (Subsingleton.elim _ _)⟩
      simpa [D0,hmBig,H] using hcon
  let C := B.filter (fun v => ∃ hv : v ∈ B, H.Reachable u ⟨v,hv⟩)
  have bC {v} (hv : v ∈ C) : v ∈ B := (mem_filter.mp hv).1
  have rc {v} (hv : v ∈ C) : H.Reachable u ⟨v,bC hv⟩ :=
    (mem_filter.mp hv).2.elim (fun _ h => h)
  have uc : u.val ∈ C := mem_filter.mpr ⟨u.property, u.property, ⟨Walk.nil⟩⟩
  have CC {x y} (hx : x ∈ C) (hy : y ∈ C) (ne : x ≠ y) : G.Adj x y :=
    hClq ⟨x,bC hx⟩ ⟨y,bC hy⟩ ((rc hx).symm.trans (rc hy))
      (fun h => ne (congrArg Subtype.val h))
  have Cnext {x y} (hx : x ∈ C) (hy : y ∈ B) (e : G.Adj x y) : y ∈ C :=
    mem_filter.mpr ⟨hy,hy,(rc hx).trans
      (show H.Adj ⟨x,bC hx⟩ ⟨y,hy⟩ from e).reachable⟩
  have hSize : s ≤ C.card := by
    refine has.trans ?_
    rw [← G.card_neighborFinset_eq_degree]
    apply card_le_card
    intro x hx
    have ex := (G.mem_neighborFinset a x).mp hx
    have xb := nbA ha ex
    exact mem_filter.mpr ⟨xb,xb,hHigh a ha has u ⟨x,xb⟩ eu ex⟩
  have qEx : ∃ q ∈ C, (∀ x ∈ C, G.Adj z x → G.Adj z q) := by
    by_cases hh : ∃ q ∈ C, G.Adj z q
    · obtain ⟨q,hq,eq⟩ := hh
      exact ⟨q,hq,fun _ _ _ => eq⟩
    · exact ⟨u.val,uc,fun x hx ex => (hh ⟨x,hx,ex⟩).elim⟩
  obtain ⟨q,hq,hze⟩ := qEx
  have hErase : s - 1 ≤ (C.erase q).card := by
    rw [card_erase_of_mem hq]
    omega
  obtain ⟨R,hR,hrCard⟩ := exists_subset_card_eq hErase
  have Rq : q ∉ R := fun hr => (mem_erase.mp (hR hr)).1 rfl
  have RC {v} (hv : v ∈ R) : v ∈ C := (mem_erase.mp (hR hv)).2
  have R0 {v} (hv : v ∈ R) : v ∈ D0 := b0 (bC (RC hv))
  let D := D0 \ R
  have qd : q ∈ D := mem_sdiff.mpr ⟨b0 (bC hq), Rq⟩
  have hD : Con G D := by
    let f : ↥(D0 : Set V) → ↥(D : Set V) := fun x =>
      if h : x.val ∈ R then ⟨q,qd⟩ else ⟨x.val,mem_sdiff.mpr ⟨x.property,h⟩⟩
    have one {x y : ↥(D0 : Set V)} (hx : x.val ∈ R) (hy : y.val ∉ R)
        (e : G.Adj x.val y.val) : f x = f y ∨ (G.induce (D : Set V)).Adj (f x) (f y) := by
      by_cases eq : q = y.val
      · exact Or.inl (Subtype.ext (by simp [f,hx,hy,eq]))
      · right
        change G.Adj (f x).val (f y).val
        simp only [f, dif_pos hx, dif_neg hy]
        by_cases yb : y.val ∈ B
        · exact CC hq (Cnext (RC hx) yb e) eq
        · rw [onlyz y.property yb]
          exact (hze x.val (RC hx) (onlyz y.property yb ▸ e.symm)).symm
    apply weakConnected hD0 f
    · intro x
      exact ⟨⟨x.val,(mem_sdiff.mp x.property).1⟩,
        Subtype.ext (by simp [f,(mem_sdiff.mp x.property).2])⟩
    · intro x y e
      change G.Adj x.val y.val at e
      by_cases hx : x.val ∈ R <;> by_cases hy : y.val ∈ R
      · exact Or.inl (Subtype.ext (by simp [f,hx,hy]))
      · exact one hx hy e
      · exact (one hy hx e.symm).elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
      · right
        change G.Adj (f x).val (f y).val
        simpa [f,hx,hy] using e
  refine ⟨D,hD,?_,?_⟩
  · intro v hv
    by_cases hvR : v ∈ R
    · exact ⟨q,qd,CC (RC hvR) hq (fun he => Rq (he ▸ hvR))⟩
    have vn0 : v ∉ D0 := fun h => hv (mem_sdiff.mpr ⟨h,hvR⟩)
    by_cases vz : v = z
    · subst z
      obtain ⟨y,ey⟩ := nbExists v (outA vn0)
      by_cases yr : y.val ∈ R
      · exact ⟨q,qd,hze y.val (RC yr) ey⟩
      · exact ⟨y.val,mem_sdiff.mpr ⟨b0 y.property,yr⟩,ey⟩
    · by_contra hh
      have incl : G.neighborFinset v ⊆ R := by
        intro x hx
        have ex := (G.mem_neighborFinset v x).mp hx
        by_contra xn
        exact hh ⟨x,mem_sdiff.mpr ⟨b0 (nbA (outA vn0) ex),xn⟩,ex⟩
      have h := card_le_card incl
      rw [G.card_neighborFinset_eq_degree,hrCard] at h
      have := hAll v vz
      omega
  · let A0 := if 1 < compCount G B then A.erase z else A
    have A0out {v} (hv : v ∈ A0) : v ∉ D0 := by
      intro h0
      by_cases hbig : 1 < compCount G B
      · have va : v ∈ A.erase z := by simpa [A0,hbig] using hv
        exact (mem_erase.mp va).1 (onlyz h0 (fun vb => (biff v).mp vb (mem_erase.mp va).2))
      · have vb : v ∈ B := by simpa [D0,hbig] using h0
        exact (biff v).mp vb (by simpa [A0,hbig] using hv)
    have hdis : Disjoint A0 R := disjoint_left.mpr (fun _ ha hr => A0out ha (R0 hr))
    have hinc : A0 ∪ R ⊆ univ \ D := by
      intro v hv
      refine mem_sdiff.mpr ⟨mem_univ _, fun hd => ?_⟩
      obtain ⟨h0,hnR⟩ := mem_sdiff.mp hd
      exact (mem_union.mp hv).elim (fun ha => A0out ha h0) hnR
    have hh := card_le_card hinc
    rw [card_union_of_disjoint hdis,hrCard] at hh
    by_cases hbig : 1 < compCount G B
    · have he : A.card ≤ (A.erase z).card + 1 := by
        by_cases hz : z ∈ A
        · rw [card_erase_of_mem hz]
          omega
        · rw [erase_eq_of_not_mem hz]
          omega
      simp [A0,hbig] at hh
      omega
    · simp [A0,hbig] at hh
      omega

#print axioms cliqueCore
end Graffiti177

/- Proof module: Exact177 -/
open SimpleGraph Finset
set_option linter.unusedSectionVars false

namespace Graffiti177
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Minimum of the larger degree in a pair of distinct vertices:
the second entry of the sorted degree sequence, counting multiplicity. -/
noncomputable def secondDegree : ℕ :=
  sInf {k | ∃ u v : V, u ≠ v ∧ max (G.degree u) (G.degree v) = k}

lemma secondDegree_properties (hc : G.Connected) (hn : 1 < Fintype.card V) :
    1 ≤ secondDegree G ∧ ∃ z : V, ∀ v ≠ z, secondDegree G ≤ G.degree v := by
  classical
  obtain ⟨x,y,hxy⟩ := Fintype.one_lt_card_iff.mp hn
  have hne : {k | ∃ u v : V, u ≠ v ∧ max (G.degree u) (G.degree v) = k}.Nonempty :=
    ⟨_,x,y,hxy,rfl⟩
  have degPos (v : V) : 0 < G.degree v := by
    obtain ⟨w,e⟩ := exists_adj G hc hn v
    rw [← G.card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨w,(G.mem_neighborFinset v w).mpr e⟩
  have hz : (Finset.univ : Finset V).Nonempty := ⟨x,Finset.mem_univ _⟩
  obtain ⟨z,_,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset V) (fun v : V => G.degree v) hz
  refine ⟨?_,z,fun v hv => ?_⟩
  · obtain ⟨u,v,_,he⟩ := Nat.sInf_mem hne
    unfold secondDegree
    rw [← he]
    exact (degPos u).trans_le (le_max_left _ _)
  · have he : G.degree z ≤ G.degree v := hmin v (Finset.mem_univ _)
    unfold secondDegree
    exact Nat.sInf_le ⟨z,v,hv.symm,max_eq_right he⟩

lemma basic_bipartite (hn : 1 < Fintype.card V) : 2 ≤ bipartiteNum G := by
  classical
  obtain ⟨a,b,hab⟩ := Fintype.one_lt_card_iff.mp hn
  have sing (v : V) : Indep G ({v} : Finset V) := by simp [Indep]
  have disj : Disjoint ({a} : Finset V) {b} := by simpa using hab.symm
  simpa using bip_bound G (sing a) (sing b) disj

lemma complete_of_alpha_le_one (hh : independence G ≤ 1)
    {u v : V} (hn : u ≠ v) : G.Adj u v := by
  classical
  by_cases e : G.Adj u v
  · exact e
  · exfalso
    have hi : Indep G ({u,v} : Finset V) := by
      intro a ha b hb hab he
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact hab rfl
      · exact e he
      · exact e he.symm
      · exact hab rfl
    have h := indep_card_le G hi
    simp [Finset.card_insert_of_not_mem,hn] at h
    omega

lemma graff177_degree_parameter (hc : G.Connected) (hn : 1 < Fintype.card V)
    (s : ℕ) (hs : 1 ≤ s) (z : V) (hAll : ∀ v ≠ z, s ≤ G.degree v) :
    2 * independence G + s ≤ maxLeaves G + bipartiteNum G := by
  classical
  by_cases hα : independence G ≤ 1
  · obtain ⟨u,v,huv⟩ := Fintype.one_lt_card_iff.mp hn
    have hz : ∃ w, w ≠ z := by
      by_cases hu : u = z
      · exact ⟨v,fun hv => huv (hu.trans hv.symm)⟩
      · exact ⟨u,hu⟩
    obtain ⟨w,hw⟩ := hz
    have hd := hAll w hw
    have hdz : G.degree w ≤ Fintype.card V - 1 := by have he := G.degree_lt_card_verts w; omega
    have hleaf := conDom_leaves G {w} (con_single G w) (by
      intro x hx
      refine ⟨w,by simp,complete_of_alpha_le_one G hα ?_⟩
      simpa using hx)
    rw [Finset.card_sdiff (Finset.subset_univ _),Finset.card_univ,Finset.card_singleton] at hleaf
    have hbi := basic_bipartite G hn
    omega
  obtain ⟨A,hA,hAc⟩ := exists_max_indep G
  have hcard : 1 < A.card := by omega
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp hcard
  have anchor : ∃ a ∈ A, s ≤ G.degree a := by
    by_cases hz : u = z
    · exact ⟨v,hv,hAll v (fun he => huv (hz.trans he.symm))⟩
    · exact ⟨u,hu,hAll u hz⟩
  let B := (univ : Finset V) \ A
  let H := G.induce (B : Set V)
  have bne (a : V) (ha : a ∈ A) (x : V) (e : G.Adj a x) : x ∈ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hx => hA a ha x hx e.ne e⟩
  have baseB : A.card + compCount G B ≤ bipartiteNum G := by
    obtain ⟨X,hXB,hX,hcX⟩ := independentReps G B
    rw [← hcX]
    exact bip_bound G hA hX (Finset.disjoint_left.mpr
      (fun _ ha hx => (Finset.mem_sdiff.mp (hXB hx)).2 ha))
  by_cases hhi : ∀ a ∈ A, s ≤ G.degree a → ∀ u v : ↥(B : Set V),
      G.Adj a u.val → G.Adj a v.val → H.Reachable u v
  · by_cases hcl : ∀ u v : ↥(B : Set V), H.Reachable u v → u ≠ v → G.Adj u.val v.val
    · obtain ⟨D,hD,hd,hct⟩ := cliqueCore G A B s z rfl hA hc hn hs anchor hAll hcl hhi
      have hle := conDom_leaves G D hD hd
      omega
    · push_neg at hcl
      obtain ⟨u,v,hR,hnuv,e⟩ := hcl
      obtain ⟨X,hXB,hX,hcX⟩ := independentRepsPlus G B u v hR hnuv e
      have hbi := bip_bound G hA hX (Finset.disjoint_left.mpr
        (fun _ ha hx => (Finset.mem_sdiff.mp (hXB hx)).2 ha))
      obtain ⟨a,ha,hsa⟩ := anchor
      obtain ⟨D,hD,hd,hct⟩ := generalCore G A hA hc hn s hs a z ha hsa hAll
      change A.card + s + (seen G B (insert a (G.neighborFinset a))).card
        ≤ (univ \ D).card + compCount G B + 2 at hct
      obtain ⟨w,ew⟩ := exists_adj G hc hn a
      have hmem : H.connectedComponentMk ⟨w,bne a ha w ew⟩ ∈
          seen G B (insert a (G.neighborFinset a)) :=
        (mem_seen G).mpr ⟨⟨w,bne a ha w ew⟩,
          Finset.mem_insert_of_mem ((G.mem_neighborFinset a w).mpr ew),rfl⟩
      have hpos := Finset.card_pos.mpr ⟨_,hmem⟩
      have hle := conDom_leaves G D hD hd
      omega
  · push_neg at hhi
    obtain ⟨a,ha,hsa,u,v,eu,ev,hur⟩ := hhi
    obtain ⟨D,hD,hd,hct⟩ := generalCore G A hA hc hn s hs a z ha hsa hAll
    change A.card + s + (seen G B (insert a (G.neighborFinset a))).card
      ≤ (univ \ D).card + compCount G B + 2 at hct
    have hmem1 : H.connectedComponentMk u ∈ seen G B (insert a (G.neighborFinset a)) :=
      (mem_seen G).mpr ⟨u,Finset.mem_insert_of_mem ((G.mem_neighborFinset a u.val).mpr eu),rfl⟩
    have hmem2 : H.connectedComponentMk v ∈ seen G B (insert a (G.neighborFinset a)) :=
      (mem_seen G).mpr ⟨v,Finset.mem_insert_of_mem ((G.mem_neighborFinset a v.val).mpr ev),rfl⟩
    have hnuv : H.connectedComponentMk u ≠ H.connectedComponentMk v :=
      fun e => hur (ConnectedComponent.exact e)
    have hpos := Finset.one_lt_card.mpr ⟨_,hmem1,_,hmem2,hnuv⟩
    have hle := conDom_leaves G D hD hd
    omega

/-- Exact Written on the Wall II Conjecture 177 for all finite connected simple
graphs with at least two vertices. The degree parameter counts multiplicity. -/
theorem conjecture177 (hc : G.Connected) (hn : 1 < Fintype.card V) :
    2 * independence G + secondDegree G ≤ maxLeaves G + bipartiteNum G := by
  obtain ⟨hs,z,hz⟩ := secondDegree_properties G hc hn
  exact graff177_degree_parameter G hc hn (secondDegree G) hs z hz

#print axioms conjecture177
end Graffiti177
