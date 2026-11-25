/-
# Graffiti.pc #208: sparse complement and Hamilton paths

**Theorem.** Let G be a finite connected simple graph on n>1 vertices. Write m for the edge count of its complement and μ for its matching number. If 2m+3≤6μ, then G has a Hamiltonian path.

[Exact official source, page 123](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf): Written on the Wall II #208, announced January 12, 2006 and labeled open in the November 6, 2026 PDF. The displayed source condition is (1/2)(1+(2/3)m)≤μ, exactly the theorem's condition after multiplying by 6. The catalogue records that Richard Stong observed that it does not imply the Chvátal condition. Searches by number, formulation, and Stong attribution located no prior resolution; this is a bounded source audit, not a claim of absolute priority.

## Saturate a putative counterexample

Add edges to G until it is maximal without a Hamiltonian path. Connectivity and the hypothesis are preserved: μ cannot fall, m cannot rise. Let H be the complement of that maximal graph, and write d for its degrees. Every edge xy of H satisfies d(x)+d(y)≥n: otherwise the original degrees sum to at least n−1, and adding xy cannot create the first Hamiltonian path. Also d≤n−2 everywhere, since the original graph is connected.

For completeness, the one-edge closure fact follows by adjoining a universal vertex. A Hamiltonian path in the augmented graph becomes a Hamiltonian cycle on n+1 vertices. If this cycle uses the newly added edge xy, deleting xy gives a spanning list v₀=x,...,vₙ=y. The subsets of cut indices i with y adjacent to vᵢ and x adjacent to vᵢ₊₁ have cardinalities deg(y) and deg(x), respectively, in the graph with universal vertex but no xy. Their sum is at least n+1, so they overlap among the n cut indices. The chords at an overlap allow the same spanning list to be closed as a cycle without xy, following the first segment forward and the second backward. Removing the universal vertex yields a Hamiltonian path of the original graph.

## Rule out the saturated complement

Assume H has an edge, and let D be its maximum degree. We have n≤2D, D≤n−2, every positive degree is at least two, and
`2m+3≤6μ≤6 floor(n/2)≤3n`.
For a degree-D vertex and its neighbors the degree sum yields
`2m≥D+D(n−D)`.

* If H has a degree-two vertex, its two distinct neighbors have degree n−2. Their incident edge sets overlap in at most one edge, so m≥2n−5. The budget rules this out unless n=4 or n=6.
* If H has no degree-two vertex and D=n−2, then the D neighbors of a maximum-degree vertex all have degree at least three, so 2m≥4(n−2), impossible for n≥9.
* Otherwise, for n≥9, n/2≤D≤n−3. In this range D(n+1−D)≥4(n−3); equivalently the difference factors as (n−3−D)(D−4)≥0. This contradicts the budget for n≥10, and at n=9 the bound 2m≥24 contradicts μ≤4.

The remaining small cases can be classified by the same bounds. If a degree-two vertex exists then n=4,D=2 or n=6,D=4 as above. Otherwise 2m≥4D, and together with 2m≥D+D(n−D) and the budget this leaves (n,D)=(6,3),(8,4),(8,5). Here is the full treatment:

1. **n=2D, D in {2,3,4}.** Each nonisolated vertex of H has degree D, by the edge degree-sum property. A degree-D vertex and its neighbors give D+1 nonisolated vertices. Their degree sum already forces μ=D under the hypothesis. There are no more nonisolated vertices: for D=3 or 4, one more exceeds the degree-sum budget; for D=2 another would make G a disconnected 1-regular graph on four vertices. Thus H contains a clique on D+1 vertices, so G has an independent set of that size, contradicting the perfect matching.
2. **n=6, D=4 with a degree-two vertex.** Its two neighbors x,y have degree four, so m≥7. The budget forces m=7 and μ=3. Equality means xy is an edge of H and every H edge meets x or y. In G, x and y have degree one. The G-neighbor z of x cannot be y; since z is not an H-neighbor of x and every H edge meets x or y, z has at most one H-neighbor, so it is isolated in H. Hence z is also the unique G-neighbor of y. This rules out a perfect matching.
3. **n=8, D=5 without a degree-two vertex.** A degree-five vertex and its five neighbors have total degree at least 20. The budget allows at most 20, so those neighbors all have degree three, and the other vertices have degree zero. Every degree-three vertex can be adjacent only to a vertex of degree at least five, and there is just one such vertex, a contradiction.

Therefore H has no edges. But its complement is complete, and has a Hamiltonian path, contradicting saturation.

## Formalization

The main Lean statement is Graffiti208.conjecture208. It uses Mathlib's finite simple graphs and exact connectivity/complement/cardinal degrees. A matching of size k is an injection from Fin k × Bool into the vertices, with each Boolean pair adjacent. The file proves both that the defined matching maximum is attained and is an upper bound for every matching. The Hamiltonian path is a chain listing all n vertices without repetitions.

Verified with Lean/Mathlib v4.19.0. Exact entry point: Graffiti208.conjecture208.
-/
/- Reproduce with Lean 4.19.0 and Mathlib v4.19.0: run this source with lake env lean. -/
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Tactic.Linarith

/- Proof module: TraceClosure -/

namespace TraceClosure

universe u

def Traceable {V : Type u} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ p : List V, p.Nodup ∧ p.length = Fintype.card V ∧ p.Chain' G.Adj

private theorem chain_reverse {α : Type*} {R : α → α → Prop}
    (hs : ∀ x y, R x y → R y x) {l : List α} (h : l.Chain' R) :
    l.reverse.Chain' R :=
  List.chain'_reverse.mpr (h.imp hs)

private theorem no_pair_count {α : Type*} (a b : α → Bool) (l : List α)
    (h : l.Chain' fun u v => ¬ (a u = true ∧ b v = true)) :
    l.dropLast.countP a + l.tail.countP b ≤ l.length - 1 := by
  induction l with
  | nil => simp
  | cons u t ih =>
    cases t with
    | nil => simp
    | cons v r =>
      have ht := ih h.tail
      have hrel := h.rel_head
      rw [List.dropLast_cons₂]
      simp only [List.countP_cons (a := u), List.tail_cons, List.length_cons] at *
      rw [List.countP_cons (a := v)]
      cases ha : a u <;> cases hb : b v
      · simp [ha,hb] at *; omega
      · simp [ha,hb] at *; omega
      · simp [ha,hb] at *; omega
      · exact (hrel ⟨ha,hb⟩).elim

private theorem find_pair {α : Type*} {a b : α → Bool} {l : List α} {x y : α}
    (hx : l.head? = some x) (hy : l.getLast? = some y)
    (hax : a y = false) (hby : b x = false)
    (ht : l.length ≤ l.countP a + l.countP b) :
    ∃ (L : List α) (u v : α) (M : List α), l = L ++ u :: v :: M ∧ a u = true ∧ b v = true := by
  classical
  by_contra hn
  have hchain : l.Chain' (fun u v => ¬ (a u = true ∧ b v = true)) := by
    apply List.chain'_iff_forall_rel_of_append_cons_cons.mpr
    intro u v L M hl hab
    exact hn ⟨L,u,v,M,hl,hab⟩
  have hc := no_pair_count a b l hchain
  have hA : l.countP a = l.dropLast.countP a := by
    have he : l.dropLast ++ [y] = l := List.dropLast_append_getLast? y (by rw [hy]; rfl)
    have hh := congrArg (List.countP a) he
    simpa [List.countP_append,hax] using hh.symm
  have hB : l.countP b = l.tail.countP b := by
    obtain ⟨t,ht⟩ := List.head?_eq_some_iff.mp hx
    rw [ht]
    simp [List.countP_cons,hby]
  have hpos : 0 < l.length := by
    obtain ⟨t,ht⟩ := List.head?_eq_some_iff.mp hx
    simp [ht]
  omega

private def Cyclic {α : Type*} (R : α → α → Prop) (l : List α) : Prop :=
  l.Chain' R ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, R x y

private theorem cycled {α : Type*} {R : α → α → Prop}
    (hs : ∀ x y, R x y → R y x)
    {l : List α} {x y : α}
    (hx : l.head? = some x) (hy : l.getLast? = some y)
    (hc : l.Chain' R)
    {L : List α} {v w : α} {M : List α} (he : l = L ++ v :: w :: M)
    (hyv : R y v) (hxw : R x w) :
    ∃ c : List α, Cyclic R c ∧ c.Perm l := by
  let A := L ++ [v]
  let B := w :: M
  have he' : l = A ++ B := by simp [A,B,he]
  have hA : A ≠ [] := by simp [A]
  have hB : B ≠ [] := by simp [B]
  rw [he'] at hc
  have hAh : A.head? = some x := by
    rw [he', List.head?_append_of_ne_nil A hA] at hx
    exact hx
  have hBt : B.getLast? = some y := by
    rw [he', List.getLast?_append_of_ne_nil A hB] at hy
    exact hy
  have hAt : A.getLast? = some v := by simp [A,List.getLast?_append_cons]
  have hBh : B.head? = some w := rfl
  refine ⟨A ++ B.reverse, ⟨?_,?_⟩,?_⟩
  · apply hc.left_of_append.append (chain_reverse hs hc.right_of_append)
    simp [hAt,List.head?_reverse,hBt,hs y v hyv]
  · have hrev : B.reverse ≠ [] := by simp [hB]
    rw [List.getLast?_append_of_ne_nil A hrev, List.getLast?_reverse, hBh,
        List.head?_append_of_ne_nil A hA, hAh]
    simpa using hs x w hxw
  · rw [he']
    exact (List.reverse_perm B).append_left A

private theorem rotate_cycle {α : Type*} {R : α → α → Prop} {A B : List α}
    (h : Cyclic R (A ++ B)) : Cyclic R (B ++ A) := by
  by_cases hA : A = []
  · simpa [hA] using h
  by_cases hB : B = []
  · simpa [hB] using h
  obtain ⟨h1, h2⟩ := h
  have h3 := (List.chain'_append.mp h1).2.2
  rw [List.getLast?_append_of_ne_nil A hB, List.head?_append_of_ne_nil A hA] at h2
  refine ⟨h1.right_of_append.append h1.left_of_append h2,?_⟩
  rwa [List.getLast?_append_of_ne_nil B hA, List.head?_append_of_ne_nil B hB]

private theorem split_at_mem {α : Type*} (x : α) (l : List α) (h : x ∈ l) :
    ∃ A B : List α, l = A ++ x :: B := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    rcases List.mem_cons.mp h with e | e
    · exact ⟨[],t,by simp [e]⟩
    · obtain ⟨A,B,he⟩ := ih e
      exact ⟨a :: A,B,by simp [he]⟩

private theorem option_map_some {α : Type*} (l : List (Option α)) (h : none ∉ l) :
    ∃ p : List α, p.map some = l := by
  induction l with
  | nil => exact ⟨[],rfl⟩
  | cons a t ih =>
    rcases a with _ | v
    · exact (h (by simp)).elim
    · obtain ⟨p,hp⟩ := ih (fun hh => h (List.mem_cons_of_mem _ hh))
      exact ⟨v :: p,by simp [hp]⟩


private def univRel {V : Type*} (G : SimpleGraph V) : Option V → Option V → Prop
  | some x, some y => G.Adj x y
  | none, none => False
  | _, _ => True

private theorem univRel_symm {V : Type*} (G : SimpleGraph V) :
    ∀ x y, univRel G x y → univRel G y x := by
  intro x y h
  rcases x with _ | x <;> rcases y with _ | y
  · exact h
  · trivial
  · trivial
  · exact G.symm h

private noncomputable def mark {α : Type*} (R : α → α → Prop) (x : α) (v : α) : Bool :=
  @decide (R x v) (Classical.propDecidable _)

@[simp] private theorem mark_true {α : Type*} {R : α → α → Prop} {x y : α} :
    mark R x y = true ↔ R x y := by
  classical
  exact Iff.of_eq (@decide_eq_true_eq (R x y) (Classical.propDecidable _))

private theorem mark_false {α : Type*} {R : α → α → Prop} {x y : α} (h : ¬R x y) :
    mark R x y = false := by
  cases he : mark R x y
  · rfl
  · exact (h (mark_true.mp he)).elim

private theorem full_toFinset {V : Type*} [Fintype V] [DecidableEq V]
    {p : List V} (hn : p.Nodup) (hl : p.length = Fintype.card V) :
    p.toFinset = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, List.toFinset_card_of_nodup hn, hl]

private theorem count_deg {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : List V} (hn : p.Nodup) (hl : p.length = Fintype.card V) (x : V) :
    (none :: p.map some).countP (mark (univRel G) (some x)) = G.degree x + 1 := by
  classical
  have ht : mark (univRel G) (some x) none = true := mark_true.mpr trivial
  let f := mark (univRel G) (some x) ∘ some
  have hfil : (p.filter f).toFinset = G.neighborFinset x := by
    rw [List.toFinset_filter, full_toFinset hn hl]
    ext y
    simp [f,univRel, G.mem_neighborFinset]
  have hc : (p.filter f).length = G.degree x := by
    rw [← List.toFinset_card_of_nodup (hn.filter f), hfil, G.card_neighborFinset_eq_degree]
  have hd : p.countP f = G.degree x := by
    rw [List.countP_eq_length_filter, hc]
  simpa [List.countP_cons,List.countP_map,ht,f] using hd

private theorem split_left {V : Type*} (G : SimpleGraph V) {x y : V} {L M : List V}
    (hn : (L ++ x :: y :: M).Nodup)
    (hc : (L ++ x :: y :: M).Chain' (G ⊔ SimpleGraph.edge x y).Adj) :
    (L ++ [x]).Chain' G.Adj := by
  have hn' : ((L ++ [x]) ++ y :: M).Nodup := by simpa using hn
  have hd := (List.nodup_append.mp hn').2.2
  have hy : y ∉ L ++ [x] := fun hy => hd hy (by simp)
  have head := (List.chain'_append_cons_cons.mp hc).1
  apply (List.Chain'.iff_mem.mp head).imp
  intro a b ⟨ha,hb,hab⟩
  rcases (SimpleGraph.sup_adj _ _ _ _).mp hab with hag | hae
  · exact hag
  · rcases ((SimpleGraph.edge_adj _ _ _ _).mp hae).1 with ⟨_,rfl⟩ | ⟨rfl,_⟩
    · exact (hy hb).elim
    · exact (hy ha).elim

private theorem split_right {V : Type*} (G : SimpleGraph V) {x y : V} {L M : List V}
    (hn : (L ++ x :: y :: M).Nodup)
    (hc : (L ++ x :: y :: M).Chain' (G ⊔ SimpleGraph.edge x y).Adj) :
    (y :: M).Chain' G.Adj := by
  have hn' : ((L ++ [x]) ++ y :: M).Nodup := by simpa using hn
  have hd := (List.nodup_append.mp hn').2.2
  have hx : x ∉ y :: M := fun hx => hd (by simp) hx
  have tail := (List.chain'_append_cons_cons.mp hc).2.2
  apply (List.Chain'.iff_mem.mp tail).imp
  intro a b ⟨ha,hb,hab⟩
  rcases (SimpleGraph.sup_adj _ _ _ _).mp hab with hag | hae
  · exact hag
  · rcases ((SimpleGraph.edge_adj _ _ _ _).mp hae).1 with ⟨rfl,_⟩ | ⟨_,rfl⟩
    · exact (hx ha).elim
    · exact (hx hb).elim

private theorem chain_option {V : Type*} (G : SimpleGraph V) {p : List V}
    (h : p.Chain' G.Adj) : (p.map some).Chain' (univRel G) := by
  exact (List.chain'_map (some : V → Option V)).mpr h

private theorem augmentation {V : Type*} (G : SimpleGraph V) {x y : V} {L M : List V}
    (h1 : (L ++ [x]).Chain' G.Adj) (h2 : (y :: M).Chain' G.Adj) :
    ∃ t : List (Option V), t.head? = some (some x) ∧ t.getLast? = some (some y) ∧
      t.Chain' (univRel G) ∧ t.Perm (none :: (L ++ x :: y :: M).map some) := by
  let A : List (Option V) := (L ++ [x]).reverse.map some
  let B : List (Option V) := (y :: M).reverse.map some
  have hnA : A ≠ [] := by simp [A]
  have hnB : B ≠ [] := by simp [B]
  have hCA : A.Chain' (univRel G) := chain_option G (chain_reverse (fun _ _ h => G.symm h) h1)
  have hCB : B.Chain' (univRel G) := chain_option G (chain_reverse (fun _ _ h => G.symm h) h2)
  have ha : A.head? = some (some x) := by
    simp [A,List.head?_map,List.head?_reverse,List.getLast?_append_cons]
  have hb : B.getLast? = some (some y) := by simp [B,List.getLast?_map,List.getLast?_reverse]
  refine ⟨A ++ none :: B, ?_, ?_, ?_, ?_⟩
  · rwa [List.head?_append_of_ne_nil A hnA]
  · rw [show A ++ none :: B = (A ++ [none]) ++ B by simp]
    rwa [List.getLast?_append_of_ne_nil _ hnB]
  · have haNone : none ∉ A := by simp [A]
    have hbNone : none ∉ B := by simp [B]
    have hFront : (none :: B).Chain' (univRel G) := by
      apply hCB.cons'
      intro v hv
      cases v
      · exact (hbNone (List.mem_of_mem_head? hv)).elim
      · trivial
    apply hCA.append hFront
    intro u hu v hv
    have he : none = v := by simpa using hv
    subst v
    cases u
    · exact (haNone (List.mem_of_mem_getLast? hu)).elim
    · trivial
  · have hpA := (List.reverse_perm (L ++ [x])).map (some : V → Option V)
    have hpB := (List.reverse_perm (y :: M)).map (some : V → Option V)
    have him : (A ++ B).Perm ((L ++ x :: y :: M).map some) := by
      rw [show L ++ x :: y :: M = (L ++ [x]) ++ y :: M by simp,List.map_append]
      exact hpA.append hpB
    have hm : (A ++ none :: B).Perm (none :: (A ++ B)) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := A) (l₂ := [none])).append_right B
    exact hm.trans (him.cons _)

private theorem omit_hub {V : Type*} [Fintype V] (G : SimpleGraph V)
    {p : List V} (hn : p.Nodup) (hl : p.length = Fintype.card V)
    {c : List (Option V)} (hc : Cyclic (univRel G) c) (hp : c.Perm (none :: p.map some)) :
    Traceable G := by
  have hn' : (none :: p.map some).Nodup :=
    List.nodup_cons.mpr ⟨by simp, hn.map (Option.some_injective V)⟩
  have hmem : none ∈ c := hp.mem_iff.mpr (by simp)
  obtain ⟨A,B,he⟩ := split_at_mem none c hmem
  rw [he] at hc hp
  have hrot := rotate_cycle (A := A) (B := none :: B) hc
  have hpc : (none :: (B ++ A)).Perm (none :: p.map some) :=
    (List.perm_append_comm (l₁ := none :: B) (l₂ := A)).trans hp
  have hnod : (none :: (B ++ A)).Nodup := hpc.nodup_iff.mpr hn'
  obtain ⟨q,hq⟩ := option_map_some (B ++ A) (List.nodup_cons.mp hnod).1
  refine ⟨q, ?_, ?_, ?_⟩
  · exact List.Nodup.of_map some (hq ▸ (List.nodup_cons.mp hnod).2)
  · have ht := hpc.length_eq
    simpa [← hq, hl] using ht
  · have hChain : (q.map some).Chain' (univRel G) := hq ▸ hrot.1.tail
    exact (List.chain'_map (some : V → Option V)).mp hChain

private theorem close_split {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (L M : List V)
    (hn : (L ++ x :: y :: M).Nodup) (hl : (L ++ x :: y :: M).length = Fintype.card V)
    (hc : (L ++ x :: y :: M).Chain' (G ⊔ SimpleGraph.edge x y).Adj)
    (hd : Fintype.card V - 1 ≤ G.degree x + G.degree y) : Traceable G := by
  obtain ⟨t,hx,hy,ht,hperm⟩ :=
    augmentation G (split_left G hn hc) (split_right G hn hc)
  have hlen : t.length = Fintype.card V + 1 := by
    simpa only [List.length_cons, List.length_map, hl] using hperm.length_eq
  have hdx := (hperm.countP_eq (mark (univRel G) (some x))).trans (count_deg G hn hl x)
  have hdy := (hperm.countP_eq (mark (univRel G) (some y))).trans (count_deg G hn hl y)
  have hcx : mark (univRel G) (some x) (some x) = false := mark_false (G.loopless x)
  have hcy : mark (univRel G) (some y) (some y) = false := mark_false (G.loopless y)
  have ht' : t.length ≤ t.countP (mark (univRel G) (some y)) +
      t.countP (mark (univRel G) (some x)) := by
    omega
  obtain ⟨A,a,b,B,hsep,ha,hb⟩ := find_pair hx hy hcy hcx ht'
  obtain ⟨c,hc,hpc⟩ := cycled (univRel_symm G) hx hy ht hsep (mark_true.mp ha) (mark_true.mp hb)
  exact omit_hub G hn hl hc (hpc.trans hperm)

private theorem edge_comm {V : Type*} (x y : V) :
    SimpleGraph.edge x y = SimpleGraph.edge y x := by
  ext a b
  simp only [SimpleGraph.edge_adj]
  tauto

/-- The traceability form of the Bondy–Chvátal edge-closure step. -/
theorem traceable_sup_edge {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (hd : Fintype.card V - 1 ≤ G.degree x + G.degree y) :
    Traceable (G ⊔ SimpleGraph.edge x y) → Traceable G := by
  classical
  rintro ⟨p,hn,hl,hc⟩
  by_cases hgood : p.Chain' G.Adj
  · exact ⟨p,hn,hl,hgood⟩
  have hex : ∃ (a b : V) (L M : List V), p = L ++ a :: b :: M ∧ ¬ G.Adj a b := by
    by_contra hh
    apply hgood
    apply List.chain'_iff_forall_rel_of_append_cons_cons.mpr
    intro a b L M hp
    by_contra hd
    exact hh ⟨a,b,L,M,hp,hd⟩
  rcases hex with ⟨a,b,L,M,rfl,hab⟩
  have he := (List.chain'_append_cons_cons.mp hc).2.1
  have he := ((SimpleGraph.sup_adj _ _ _ _).mp he).resolve_left hab
  rcases ((SimpleGraph.edge_adj _ _ _ _).mp he).1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact close_split G _ _ L M hn hl hc hd
  · rw [edge_comm] at hc
    exact close_split G _ _ L M hn hl hc (by omega)

#print axioms traceable_sup_edge


theorem traceable_mono {V : Type*} [Fintype V] {G H : SimpleGraph V} (h : G ≤ H) :
    Traceable G → Traceable H := by
  rintro ⟨p,hn,hl,hc⟩
  exact ⟨p,hn,hl,hc.imp (fun _ _ h' => h h')⟩

theorem traceable_top (V : Type*) [Fintype V] : Traceable (⊤ : SimpleGraph V) := by
  let e := (Fintype.equivFin V).symm
  let p := List.ofFn e
  have hn : p.Nodup := List.nodup_ofFn.mpr e.injective
  refine ⟨p,hn,List.length_ofFn,?_⟩
  apply List.chain'_iff_forall_rel_of_append_cons_cons.mpr
  intro a b L M he
  apply (SimpleGraph.top_adj _ _).mpr
  intro hh
  have hN : (a :: b :: M).Nodup := (he ▸ hn).of_append_right
  exact (List.nodup_cons.mp hN).1 (by simp [hh])



/-- A nontraceable finite graph has an edge-maximal nontraceable supergraph. -/
theorem exists_maximal_nontraceable_supergraph {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hnt : ¬Traceable G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ ¬Traceable H ∧
      ∀ x y, Hᶜ.Adj x y → Traceable (H ⊔ SimpleGraph.edge x y) := by
  classical
  let S : Set (SimpleGraph V) := {H | G ≤ H ∧ ¬Traceable H}
  obtain ⟨H,hH,hm⟩ := (Set.toFinite S).exists_maximal_wrt id S ⟨G,le_rfl,hnt⟩
  refine ⟨H,hH.1,hH.2,?_⟩
  intro x y hxy
  obtain ⟨hne,hna⟩ := (SimpleGraph.compl_adj H x y).mp hxy
  by_contra ht
  let J := H ⊔ SimpleGraph.edge x y
  have hsub : H ≤ J := le_sup_left
  have hj : J.Adj x y := (SimpleGraph.sup_adj _ _ _ _).mpr
    (Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩))
  have hJ : J ∈ S := ⟨hH.1.trans hsub,ht⟩
  have heq : H = J := hm J hJ hsub
  exact hna (heq.symm ▸ hj)

/-- Ore's degree-sum condition for spanning paths. -/
theorem ore_traceable {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hd : ∀ x y, x ≠ y → ¬G.Adj x y → Fintype.card V - 1 ≤ G.degree x + G.degree y) :
    Traceable G := by
  classical
  by_contra hn
  obtain ⟨H,hgh,hnt,hmax⟩ := exists_maximal_nontraceable_supergraph G hn
  letI : DecidableRel H.Adj := Classical.decRel _
  have hxyn : ∃ x y, x ≠ y ∧ ¬H.Adj x y := by
    by_contra h
    apply hnt
    have heq : H = ⊤ := by
      ext x y
      rw [SimpleGraph.top_adj]
      exact ⟨fun hh => hh.ne, fun hne => by_contra fun hh => h ⟨x,y,hne,hh⟩⟩
    rw [heq]
    exact traceable_top V
  obtain ⟨x,y,hne,hnxy⟩ := hxyn
  have ht := hmax x y ((SimpleGraph.compl_adj H x y).mpr ⟨hne,hnxy⟩)
  have hdg := hd x y hne (fun h => hnxy (hgh h))
  have hx := SimpleGraph.degree_le_of_le (v := x) hgh
  have hy := SimpleGraph.degree_le_of_le (v := y) hgh
  exact hnt (traceable_sup_edge H x y (by omega) ht)

#print axioms exists_maximal_nontraceable_supergraph
#print axioms ore_traceable

end TraceClosure

/- Proof module: Sparse -/

namespace Graffiti208
open Finset
open scoped BigOperators
noncomputable section
variable {V : Type*} [Fintype V]
local notation "n" => Fintype.card V
attribute [-instance] SimpleGraph.Compl.adjDecidable
local instance : DecidableEq V := Classical.decEq V
local instance (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel H.Adj

def HasMatching (G : SimpleGraph V) (k : ℕ) :=
  ∃ f : Fin k × Bool ↪ V, ∀ i, G.Adj (f (i,false)) (f (i,true))

private theorem matching_bound {G : SimpleGraph V} {k : ℕ} (h : HasMatching G k) :
    2*k ≤ n := by
  obtain ⟨f, -⟩ := h
  simpa [Nat.mul_comm] using Fintype.card_le_of_injective f f.injective

private theorem perfectPartner {G : SimpleGraph V} {k : ℕ} (h : HasMatching G k)
    (hk : 2*k = n) : ∃ f : V → V, Function.Injective f ∧ ∀ v, G.Adj v (f v) := by
  obtain ⟨e, he⟩ := h
  have hc : Fintype.card (Fin k × Bool) = n := by simpa [Nat.mul_comm] using hk
  have hs : Function.Surjective e := (Fintype.bijective_iff_injective_and_card _).2
    ⟨e.injective, hc⟩ |>.2
  let E : (Fin k × Bool) ≃ V := Equiv.ofBijective e ⟨e.injective, hs⟩
  let flip : Fin k × Bool → Fin k × Bool := fun p => (p.1, ! p.2)
  have hf : Function.Injective flip := by
    intro ⟨i,b⟩ ⟨j,c⟩ h
    cases b <;> cases c <;> simp_all [flip, Prod.mk.injEq]
  refine ⟨fun v => E (flip (E.symm v)), E.injective.comp (hf.comp E.symm.injective), ?_⟩
  intro v
  obtain ⟨⟨i,b⟩, rfl⟩ := E.surjective v
  change G.Adj (E (i,b)) (E (flip (E.symm (E (i,b)))))
  rw [E.symm_apply_apply]
  cases b
  · exact he i
  · exact G.symm (he i)

private theorem countNeighbor (H : SimpleGraph V) (u : V) (q : ℕ)
    (hq : ∀ v, H.Adj u v → q ≤ H.degree v) :
    H.degree u + H.degree u*q ≤ 2*H.edgeFinset.card := by
  have h₁ := sum_le_sum (s := H.neighborFinset u)
    (f := fun _ => q) (g := fun v : V => H.degree v)
    (fun v hv => hq v ((H.mem_neighborFinset u v).1 hv))
  have hu : u ∉ H.neighborFinset u := by simp
  have h₂ := sum_le_sum_of_subset (f := fun v : V => H.degree v)
    (Finset.subset_univ (insert u (H.neighborFinset u)))
  rw [Finset.sum_insert hu, H.sum_degrees_eq_twice_card_edges] at h₂
  simp only [Finset.sum_const, nsmul_eq_mul, H.card_neighborFinset_eq_degree] at h₁
  simp only [Nat.cast_id] at h₁
  omega

private theorem union_bound (H : SimpleGraph V) (a b : V) (hab : a ≠ b) :
    H.degree a + H.degree b ≤ H.edgeFinset.card + 1 := by
  let A := H.incidenceFinset a
  let B := H.incidenceFinset b
  have h₁ : (A ∪ B).card ≤ H.edgeFinset.card := by
    apply Finset.card_le_card
    intro e he
    rcases Finset.mem_union.1 he with h|h
    · exact SimpleGraph.mem_edgeFinset.2 (((H.mem_incidenceFinset a e).1 h).1)
    · exact SimpleGraph.mem_edgeFinset.2 (((H.mem_incidenceFinset b e).1 h).1)
  have h₂ : (A ∩ B).card ≤ 1 := by
    apply Finset.card_le_one.2
    suffices ∀ e ∈ A ∩ B, e = s(a,b) by
      intro x hx y hy
      rw [this x hx, this y hy]
    intro e he
    obtain ⟨ha,hb⟩ := Finset.mem_inter.1 he
    have ha' := ((H.mem_incidenceFinset a e).1 ha).2
    have hb' := ((H.mem_incidenceFinset b e).1 hb).2
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.1 ha'
    simp only [Sym2.mem_iff] at hb'
    rcases hb' with h|rfl
    · exact (hab h.symm).elim
    · rfl
  have h₃ := Finset.card_union_add_card_inter A B
  change (A ∪ B).card + (A ∩ B).card = _ at h₃
  change _ = (H.incidenceFinset a).card + (H.incidenceFinset b).card at h₃
  rw [H.card_incidenceFinset_eq_degree, H.card_incidenceFinset_eq_degree] at h₃
  omega

private theorem two_neighbors (H : SimpleGraph V) {u : V} (hu : H.degree u = 2) :
    ∃ a b, a ≠ b ∧ H.neighborFinset u = {a,b} :=
  Finset.card_eq_two.1 hu

private theorem large_nonempty_compl (H : SimpleGraph V) {k : ℕ} (hn : 9 ≤ n)
    (hm : 2*H.edgeFinset.card + 3 ≤ 6*k) (hk : 2*k ≤ n)
    (hD : ∀ u, H.degree u ≤ n-2)
    (hsum : ∀ ⦃u v⦄, H.Adj u v → n ≤ H.degree u + H.degree v) :
    H = ⊥ := by
  by_contra h
  have hadj : ∃ u v, H.Adj u v := by
    by_contra! hn
    apply h
    ext u v
    simp [hn]
  obtain ⟨a,b,hab⟩ := hadj
  obtain ⟨u, -, hu⟩ := Finset.exists_max_image (Finset.univ : Finset V)
    (fun z : V => H.degree z) ⟨a, Finset.mem_univ _⟩
  simp only [Finset.mem_univ, true_implies] at hu
  let D := H.degree u
  have hhalf : n ≤ 2*D := by have := hsum hab; have := hu a; have := hu b; dsimp [D]; omega
  have hDb : D ≤ n-2 := hD u
  by_cases htwo : ∃ v, H.degree v = 2
  · obtain ⟨v,hv⟩ := htwo
    obtain ⟨x,y,hxy,hset⟩ := two_neighbors H hv
    have hx : H.Adj v x := (H.mem_neighborFinset v x).1 (by rw [hset]; simp)
    have hy : H.Adj v y := (H.mem_neighborFinset v y).1 (by rw [hset]; simp)
    have hx' := hsum hx
    have hy' := hsum hy
    have hbig := union_bound H x y hxy
    have := hD x
    have := hD y
    omega
  · push_neg at htwo
    by_cases hmax : D = n-2
    · have hq : ∀ v, H.Adj u v → 3 ≤ H.degree v := by
        intro v had
        have := hsum had
        have := htwo v
        change D = n-2 at hmax
        have hEq : H.degree u = D := rfl
        omega
      have hh : D + D*3 ≤ 2*H.edgeFinset.card := countNeighbor H u 3 hq
      omega
    · have hD3 : D ≤ n-3 := by omega
      have hq : ∀ v, H.Adj u v → n-D ≤ H.degree v := by
        intro v had
        have := hsum had
        have hEq : H.degree u = D := rfl
        omega
      have hlower : D + D*(n-D) ≤ 2*H.edgeFinset.card := countNeighbor H u (n-D) hq
      have hnSub : (↑(n-D) : ℤ) = (n : ℤ) - (D : ℤ) := by omega
      have hprod : 0 ≤ (((n : ℤ) - 3) - (D : ℤ)) * (2*(D : ℤ) - (n : ℤ)) := by
        apply mul_nonneg <;> omega
      have hprod₂ : 0 ≤ ((n : ℤ)-8) * ((n : ℤ)-3-(D : ℤ)) := by
        apply mul_nonneg <;> omega
      have Hbig : 4*(n : ℤ)-12 ≤ 2*(H.edgeFinset.card : ℤ) := by
        zify at hlower
        rw [hnSub] at hlower
        nlinarith only [hprod, hprod₂, hlower]
      omega

private theorem sum_lower (H : SimpleGraph V) (S : Finset V) (q : ℕ)
    (hq : ∀ v ∈ S, q ≤ H.degree v) :
    S.card*q ≤ 2*H.edgeFinset.card := by
  have h₁ := sum_le_sum (s := S) (f := fun _ => q) (g := fun v : V => H.degree v) hq
  have h₂ := sum_le_sum_of_subset (f := fun v : V => H.degree v) (subset_univ S)
  rw [H.sum_degrees_eq_twice_card_edges] at h₂
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at h₁
  change ∑ x ∈ S, H.degree x ≤ _ at h₂
  omega

private theorem degree_le_of_connected (G : SimpleGraph V) (hc : G.Connected) (hn : 1 < n) :
    ∀ u, Gᶜ.degree u ≤ n-2 := by
  intro u
  obtain ⟨v,huv⟩ := Fintype.exists_ne_of_one_lt_card hn u
  have hp : 0 < G.degree u := by
    obtain ⟨w⟩ := hc.preconnected u v
    cases w with
    | nil => exact (huv rfl).elim
    | cons h _ => exact (G.degree_pos_iff_exists_adj u).2 ⟨_, h⟩
  rw [G.degree_compl]
  omega

private theorem disconnected_of_all_degree_one (G : SimpleGraph V) (hc : G.Connected)
    (hn : 2 < n) (hh : ∀ v, G.degree v = 1) : False := by
  obtain ⟨a⟩ := hc.nonempty
  obtain ⟨b,hb⟩ := Finset.card_eq_one.1 (hh a)
  have hab : G.Adj a b := (G.mem_neighborFinset _ _).1 (by rw [hb]; simp)
  have hb' : G.neighborFinset b = {a} := by
    have he : {a} ⊆ G.neighborFinset b := by
      intro x hx
      have hxa : x = a := Finset.mem_singleton.1 hx
      subst x
      exact (G.mem_neighborFinset _ _).2 (G.symm hab)
    exact (eq_of_subset_of_card_le he (by simpa using (hh b).le)).symm
  have hclosed : ∀ ⦃u v⦄, G.Adj u v → (u = a ∨ u = b) → (v = a ∨ v = b) := by
    intro u v huv h
    rcases h with rfl|rfl
    · right
      have hh' := (G.mem_neighborFinset _ _).2 huv
      rwa [hb, Finset.mem_singleton] at hh'
    · left
      have hh' := (G.mem_neighborFinset _ _).2 huv
      rwa [hb', Finset.mem_singleton] at hh'
  have hw : ∀ {u v}, (w : G.Walk u v) → (u = a ∨ u = b) → (v = a ∨ v = b) := by
    intro u v w
    induction w with
    | nil => exact id
    | cons he _ ih => exact fun h => ih (hclosed he h)
  have hAll : (univ : Finset V) ⊆ {a,b} := by
    intro v _
    obtain ⟨w⟩ := hc.preconnected a v
    simpa using hw w (Or.inl rfl)
  have hcard := card_le_card hAll
  have hne : a ≠ b := hab.ne
  simp [hne] at hcard
  omega

private theorem max_regular_small (G : SimpleGraph V) (hc : G.Connected)
    (u : V) (D k : ℕ) (hord : n = 2*D) (hD : Gᶜ.degree u = D)
    (hmax : ∀ z, Gᶜ.degree z ≤ D) (hDsmall : 2 ≤ D ∧ D ≤ 4)
    (hM : HasMatching G k) (hK : 2*k ≤ n)
    (hm : 2*Gᶜ.edgeFinset.card + 3 ≤ 6*k)
    (hsum : ∀ ⦃v w⦄, Gᶜ.Adj v w → n ≤ Gᶜ.degree v + Gᶜ.degree w) : False := by
  let H := Gᶜ
  change 2*H.edgeFinset.card + 3 ≤ 6*k at hm
  have hreg : ∀ v, 0 < H.degree v → H.degree v = D := by
    intro v hv
    obtain ⟨w,hw⟩ := (H.degree_pos_iff_exists_adj v).1 hv
    have h := hsum hw
    have h₁ := hmax v
    have h₂ := hmax w
    change H.degree v ≤ D at h₁
    change H.degree w ≤ D at h₂
    change n ≤ H.degree v + H.degree w at h
    omega
  have hcl := countNeighbor H u D (fun v hv =>
    (hreg v ((H.degree_pos_iff_exists_adj v).2 ⟨u,H.symm hv⟩)).ge)
  change H.degree u + H.degree u * D ≤ _ at hcl
  have hdu : H.degree u = D := hD
  rw [hdu] at hcl
  have hK' : 2*k = n := by
    have hd := hDsmall
    rcases (by omega : D = 2 ∨ D = 3 ∨ D = 4) with rfl|rfl|rfl <;> omega
  obtain ⟨f,hf,hfadj⟩ := perfectPartner hM hK'
  let S := insert u (H.neighborFinset u)
  have hSu : S.card = D+1 := by
    dsimp [S]
    rw [Finset.card_insert_of_not_mem (by simp), H.card_neighborFinset_eq_degree, hdu]
  have hSdeg : ∀ z ∈ S, H.degree z = D := by
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl|hz
    · exact hdu
    · exact hreg z ((H.degree_pos_iff_exists_adj z).2 ⟨u,H.symm ((H.mem_neighborFinset _ _).1 hz)⟩)
  have hOut : ∀ z, z ∉ S → H.degree z = 0 := by
    intro z hz
    by_cases hz' : H.degree z = 0
    · exact hz'
    exfalso
    have hbig := sum_lower H (insert z S) D (by
      intro v hv
      rcases Finset.mem_insert.1 hv with rfl|hv
      · exact (hreg v (by omega)).ge
      · exact (hSdeg v hv).ge)
    rw [Finset.card_insert_of_not_mem hz, hSu] at hbig
    have hds := hDsmall
    rcases (by omega : D = 2 ∨ D = 3 ∨ D = 4) with h|h|h
    · have huniv : insert z S = univ := eq_of_subset_of_card_le (subset_univ _) (by
        rw [card_univ, Finset.card_insert_of_not_mem hz, hSu]; omega)
      have hall : ∀ a, G.degree a = 1 := by
        intro a
        have ha : a ∈ insert z S := by rw [huniv]; simp
        have he : H.degree a = D := by
          rcases Finset.mem_insert.1 ha with rfl|ha
          · exact hreg _ (by omega)
          · exact hSdeg _ ha
        change Gᶜ.degree a = D at he
        rw [G.degree_compl] at he
        omega
      exact disconnected_of_all_degree_one G hc (by omega) hall
    · rw [h] at hbig
      omega
    · rw [h] at hbig
      omega
  have hSclique : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → H.Adj a b := by
    intro a ha b hb hab
    have hSub : H.neighborFinset a ⊆ S.erase a := by
      intro z hz
      have had := (H.mem_neighborFinset _ _).1 hz
      refine Finset.mem_erase.2 ⟨had.ne.symm, ?_⟩
      by_cases hn : z ∈ S
      · exact hn
      exfalso
      have hPos := (H.degree_pos_iff_exists_adj z).2 ⟨a,H.symm had⟩
      have := hOut z hn
      omega
    have hEq := eq_of_subset_of_card_le hSub (by
      rw [Finset.card_erase_of_mem ha, H.card_neighborFinset_eq_degree, hSu, hSdeg a ha]
      omega)
    exact (H.mem_neighborFinset _ _).1 (by rw [hEq]; exact Finset.mem_erase.2 ⟨hab.symm,hb⟩)
  have hinj := Finset.card_le_card_of_injOn f
    (s := S) (t := (univ : Finset V) \ S)
    (by
      intro a ha
      refine Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ?_⟩
      intro hfa
      have he := hfadj a
      exact ((G.compl_adj _ _).1 (hSclique a ha _ hfa he.ne)).2 he)
    hf.injOn
  rw [Finset.card_sdiff (subset_univ _), Finset.card_univ, hSu] at hinj
  omega

private theorem countNeighborTight (H : SimpleGraph V) (u : V) (q : ℕ)
    (hq : ∀ v, H.Adj u v → q ≤ H.degree v)
    (hm : 2*H.edgeFinset.card ≤ H.degree u + H.degree u*q) :
    ∀ v, H.degree v = if v = u then H.degree u else if H.Adj u v then q else 0 := by
  let f : V → ℕ := fun v => if v = u then H.degree u else if H.Adj u v then q else 0
  have hp : ∀ v, f v ≤ H.degree v := by
    intro v
    by_cases hv : v=u
    · subst v; simp [f]
    · by_cases had : H.Adj u v
      · simpa [f,hv,had] using hq v had
      · simp [f,hv,had]
  let S := insert u (H.neighborFinset u)
  have htotal : ∑ v, f v = H.degree u + H.degree u*q := by
    have hS : ∑ v ∈ S, f v = ∑ v, f v := by
      apply Finset.sum_subset (subset_univ _)
      intro v _ hv
      have hne : v ≠ u := by intro he; apply hv; simp [S,he]
      have hnot : ¬H.Adj u v := by
        intro he
        exact hv (Finset.mem_insert_of_mem ((H.mem_neighborFinset _ _).2 he))
      simp [f,hne,hnot]
    rw [← hS]
    dsimp [S]
    rw [Finset.sum_insert (by simp)]
    have hk : ∑ v ∈ H.neighborFinset u, f v = H.degree u*q := by
      trans ∑ _v ∈ H.neighborFinset u, q
      · apply Finset.sum_congr rfl
        intro v hv
        have had := (H.mem_neighborFinset _ _).1 hv
        simp [f,had,had.ne.symm]
      · simp [H.card_neighborFinset_eq_degree]
    rw [hk]
    simp [f]
  intro v
  change H.degree v = f v
  by_cases h : H.degree v = f v
  · exact h
  · have hs := Finset.sum_lt_sum (s := univ) (f := f) (g := fun a : V => H.degree a)
      (fun a _ => hp a) ⟨v,mem_univ _,lt_of_le_of_ne (hp v) (Ne.symm h)⟩
    rw [htotal, H.sum_degrees_eq_twice_card_edges] at hs
    omega

private theorem incidenceCover (H : SimpleGraph V) (a b : V) (hab : a ≠ b)
    (heq : H.edgeFinset.card+1 = H.degree a + H.degree b) :
    H.Adj a b ∧ ∀ ⦃v w⦄, H.Adj v w → (v=a ∨ w=a) ∨ (v=b ∨ w=b) := by
  let A := H.incidenceFinset a
  let B := H.incidenceFinset b
  have hsub : A ∪ B ⊆ H.edgeFinset := by
    intro e he
    rcases Finset.mem_union.1 he with h|h
    · exact SimpleGraph.mem_edgeFinset.2 (((H.mem_incidenceFinset a e).1 h).1)
    · exact SimpleGraph.mem_edgeFinset.2 (((H.mem_incidenceFinset b e).1 h).1)
  have hinter : ∀ e ∈ A ∩ B, e = s(a,b) := by
    intro e he
    obtain ⟨ha,hb⟩ := Finset.mem_inter.1 he
    have ha' := ((H.mem_incidenceFinset a e).1 ha).2
    have hb' := ((H.mem_incidenceFinset b e).1 hb).2
    obtain ⟨z,rfl⟩ := Sym2.mem_iff_exists.1 ha'
    simp only [Sym2.mem_iff] at hb'
    rcases hb' with h|rfl
    · exact (hab h.symm).elim
    · rfl
  have hi : (A ∩ B).card ≤ 1 := Finset.card_le_one.2 (by
    intro x hx y hy; rw [hinter x hx,hinter y hy])
  have h₃ := Finset.card_union_add_card_inter A B
  change _ = (H.incidenceFinset a).card + (H.incidenceFinset b).card at h₃
  rw [H.card_incidenceFinset_eq_degree,H.card_incidenceFinset_eq_degree] at h₃
  have hcu := card_le_card hsub
  have hcu' : A ∪ B = H.edgeFinset := eq_of_subset_of_card_le hsub (by omega)
  have hp : 0 < (A ∩ B).card := by omega
  obtain ⟨e,he⟩ := Finset.card_pos.1 hp
  have he' := hinter e he
  subst e
  have had := (H.mem_incidenceSet a b).1 ((H.mem_incidenceFinset a _).1 (Finset.mem_inter.1 he).1)
  refine ⟨had, ?_⟩
  intro v w hvw
  have hmem : s(v,w) ∈ H.edgeFinset := SimpleGraph.mem_edgeFinset.2 (H.mem_edgeSet.2 hvw)
  rw [← hcu'] at hmem
  rcases Finset.mem_union.1 hmem with hh|hh
  · exact Or.inl (by simpa only [Sym2.mem_iff,eq_comm] using ((H.mem_incidenceFinset a _).1 hh).2)
  · exact Or.inr (by simpa only [Sym2.mem_iff,eq_comm] using ((H.mem_incidenceFinset b _).1 hh).2)

theorem sparse_closed_complement (G : SimpleGraph V) (hc : G.Connected) (hn : 1 < n)
    {k : ℕ} (hM : HasMatching G k) (hm : 2*Gᶜ.edgeFinset.card+3 ≤ 6*k)
    (hsum : ∀ ⦃u v⦄, Gᶜ.Adj u v → n ≤ Gᶜ.degree u + Gᶜ.degree v) :
    Gᶜ = ⊥ := by
  let H := Gᶜ
  change 2*H.edgeFinset.card+3 ≤ 6*k at hm
  have hk := matching_bound hM
  have hDb := degree_le_of_connected G hc hn
  change ∀ v, H.degree v ≤ n-2 at hDb
  change ∀ ⦃u v⦄, H.Adj u v → n ≤ H.degree u + H.degree v at hsum
  by_cases hn9 : 9 ≤ n
  · exact large_nonempty_compl H hn9 hm hk hDb @hsum
  by_contra hN
  change H ≠ ⊥ at hN
  have hadj : ∃ u v, H.Adj u v := by
    by_contra! hw
    apply hN
    ext a b
    simp [hw]
  obtain ⟨a,b,hab⟩ := hadj
  obtain ⟨u, -, hu⟩ := Finset.exists_max_image (Finset.univ : Finset V)
    (fun z : V => H.degree z) ⟨a, Finset.mem_univ _⟩
  simp only [Finset.mem_univ, true_implies] at hu
  let D := H.degree u
  change ∀ v, H.degree v ≤ D at hu
  have hd : H.degree u = D := rfl
  have hhalf : n ≤ 2*D := by have := hsum hab; have := hu a; have := hu b; omega
  have hDub : D ≤ n-2 := hDb u
  have hPos : ∀ v, 0 < H.degree v → 2 ≤ H.degree v := by
    intro v hv
    obtain ⟨w,hw⟩ := (H.degree_pos_iff_exists_adj v).1 hv
    have := hsum hw
    have := hDb w
    omega
  have hQ : ∀ v, H.Adj u v → n-D ≤ H.degree v := by
    intro v hv
    have := hsum hv
    omega
  have hcount : D+D*(n-D) ≤ 2*H.edgeFinset.card := countNeighbor H u (n-D) hQ
  by_cases hTwo : ∃ v, H.degree v = 2
  · obtain ⟨v,hv⟩ := hTwo
    obtain ⟨x,y,hxy,hset⟩ := two_neighbors H hv
    have hx : H.Adj v x := (H.mem_neighborFinset v x).1 (by rw [hset]; simp)
    have hy : H.Adj v y := (H.mem_neighborFinset v y).1 (by rw [hset]; simp)
    have hx' := hsum hx
    have hy' := hsum hy
    have hx'' := hDb x
    have hy'' := hDb y
    have hbig := union_bound H x y hxy
    have hDx : D = n-2 := by have := hu x; omega
    have hor : n=4 ∨ n=6 := by omega
    rcases hor with hn4|hn6
    · exact max_regular_small G hc u D k (by omega) hd hu (by omega) hM hk hm @hsum
    · have hCx : H.degree x = 4 := by omega
      have hCy : H.degree y = 4 := by omega
      have hCe : H.edgeFinset.card = 7 := by omega
      have hk' : 2*k = n := by omega
      obtain ⟨f,hf,hfadj⟩ := perfectPartner hM hk'
      obtain ⟨hAdj,hCover⟩ := incidenceCover H x y hxy (by omega)
      have hz : f x ≠ y := by
        intro he
        exact ((G.compl_adj _ _).1 hAdj).2 (he ▸ hfadj x)
      have hz' : f x ≠ x := (hfadj x).ne.symm
      have hzero : H.degree (f x) = 0 := by
        by_cases he : H.degree (f x) = 0
        · exact he
        exfalso
        have hsz := hPos (f x) (by omega)
        have hSub : H.neighborFinset (f x) ⊆ {y} := by
          intro z h_z
          have hF := (H.mem_neighborFinset _ _).1 h_z
          have hi := hCover hF
          have hnot : z ≠ x := by
            intro hz
            subst z
            exact ((G.compl_adj _ _).1 (H.symm hF)).2 (hfadj x)
          rcases hi with (h|h)|(h|h)
          · exact (hz' h).elim
          · exact (hnot h).elim
          · exact (hz h).elim
          · exact Finset.mem_singleton.2 h
        have hSz := card_le_card hSub
        rw [H.card_neighborFinset_eq_degree, card_singleton] at hSz
        omega
      have hYdeg : G.degree y = 1 := by
        change Gᶜ.degree y = 4 at hCy
        rw [G.degree_compl] at hCy
        have hyPos := (G.degree_pos_iff_exists_adj y).2 ⟨_,hfadj y⟩
        omega
      have hYF : G.Adj y (f x) := by
        by_contra hnG
        have hH : H.Adj y (f x) := (G.compl_adj _ _).2 ⟨hz.symm,hnG⟩
        have hp := (H.degree_pos_iff_exists_adj (f x)).2 ⟨y,H.symm hH⟩
        omega
      have hy' : f y = f x := by
        obtain ⟨z,hz⟩ := Finset.card_eq_one.1 hYdeg
        have ha := (G.mem_neighborFinset _ _).2 hYF
        have hb := (G.mem_neighborFinset _ _).2 (hfadj y)
        rw [hz,mem_singleton] at ha hb
        exact hb.trans ha.symm
      exact hxy (hf hy'.symm)
  · have hcount' : D+D*3 ≤ 2*H.edgeFinset.card := countNeighbor H u 3 (by
      intro z hz
      have h := hPos z ((H.degree_pos_iff_exists_adj z).2 ⟨u,H.symm hz⟩)
      have hnot : H.degree z ≠ 2 := fun he => hTwo ⟨z,he⟩
      omega)
    have hCases : (n=6 ∧ D=3) ∨ (n=8 ∧ D=4) ∨ (n=8 ∧ D=5) := by
      have hDle : D ≤ 6 := by omega
      have hNot : D ≠ 2 := fun he => hTwo ⟨u,he⟩
      rcases (by omega : D=2 ∨ D=3 ∨ D=4 ∨ D=5 ∨ D=6) with he|he|he|he|he <;>
        rw [he] at hcount hcount' <;> omega
    rcases hCases with ⟨hn',hd'⟩|⟨hn',hd'⟩|⟨hn',hd'⟩
    · exact max_regular_small G hc u D k (by omega) hd hu (by omega) hM hk hm @hsum
    · exact max_regular_small G hc u D k (by omega) hd hu (by omega) hM hk hm @hsum
    · have hm' : 2*H.edgeFinset.card ≤ H.degree u + H.degree u*3 := by omega
      have hT := countNeighborTight H u 3 (by intro z hz; have := hQ z hz; omega) hm'
      have huP : 0 < H.degree u := by omega
      obtain ⟨z,huz⟩ := (H.degree_pos_iff_exists_adj u).1 huP
      have hz : H.degree z = 3 := by simpa [huz.ne.symm,huz] using hT z
      have hSub : H.neighborFinset z ⊆ {u} := by
        intro w h_w
        have hzw := (H.mem_neighborFinset _ _).1 h_w
        have hb := hsum hzw
        by_cases hw : w=u
        · exact Finset.mem_singleton.2 hw
        · have hnot : H.degree w ≤ 3 := by
            by_cases hwu : H.Adj u w
            · simpa [hw,hwu] using (hT w).le
            · have hh : H.degree w = 0 := by simpa [hw,hwu] using hT w
              omega
          omega
      have hr := card_le_card hSub
      rw [H.card_neighborFinset_eq_degree,card_singleton] at hr
      omega

end
end Graffiti208

/- Proof module: Conjecture208 -/

namespace Graffiti208
open Finset
open TraceClosure
noncomputable section
variable {V : Type*} [Fintype V]
local notation "n" => Fintype.card V
attribute [-instance] SimpleGraph.Compl.adjDecidable
local instance : DecidableEq V := Classical.decEq V
local instance (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel H.Adj
local instance (G : SimpleGraph V) : DecidablePred (HasMatching G) := Classical.decPred _

private def feasibleMatchingSizes (G : SimpleGraph V) : Finset ℕ :=
  (range (n/2+1)).filter (HasMatching G)

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
  have hk' : 2*k ≤ n := by simpa [Nat.mul_comm] using Fintype.card_le_of_injective f f.injective
  apply Finset.le_max'
  exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ⟨f,hf⟩⟩

private theorem sup_degree_complement_bridge (G : SimpleGraph V) {x y : V}
    (hx : Gᶜ.Adj x y) (h : ¬Traceable G)
    (ha : Traceable (G ⊔ SimpleGraph.edge x y)) :
    n ≤ Gᶜ.degree x + Gᶜ.degree y := by
  have hD : ¬(n-1 ≤ G.degree x + G.degree y) :=
    fun hh => h (traceable_sup_edge G x y hh ha)
  have hab := (G.compl_adj x y).1 hx
  have hDx := G.degree_lt_card_verts x
  have hDy := G.degree_lt_card_verts y
  rw [G.degree_compl,G.degree_compl]
  omega

theorem conjecture208_matching_witness (G : SimpleGraph V) (hc : G.Connected)
    (hn : 1 < n) (k : ℕ) (hM : HasMatching G k)
    (hm : 2*Gᶜ.edgeFinset.card+3 ≤ 6*k) : Traceable G := by
  by_contra hnG
  obtain ⟨H,hGH,hHN,hSat⟩ := exists_maximal_nontraceable_supergraph G hnG
  have hcH := hc.mono hGH
  have hMH : HasMatching H k := by
    obtain ⟨f,hf⟩ := hM
    exact ⟨f,fun i => hGH (hf i)⟩
  have hHGc : Hᶜ ≤ Gᶜ := by
    intro a b hab
    have hp := (H.compl_adj a b).1 hab
    exact (G.compl_adj a b).2 ⟨hp.1,fun ht => hp.2 (hGH ht)⟩
  have hC := Finset.card_le_card (SimpleGraph.edgeFinset_mono hHGc)
  have hIneq : 2*Hᶜ.edgeFinset.card+3 ≤ 6*k := by omega
  have hSum : ∀ ⦃a b⦄, Hᶜ.Adj a b → n ≤ Hᶜ.degree a + Hᶜ.degree b := by
    intro a b hab
    exact sup_degree_complement_bridge H hab hHN (hSat a b hab)
  have hComp := sparse_closed_complement H hcH hn hMH hIneq @hSum
  have hTop : H = ⊤ := by
    have h' := congrArg (fun L : SimpleGraph V => Lᶜ) hComp
    simpa using h'
  exact hHN (by rw [hTop]; exact traceable_top V)

theorem conjecture208 (G : SimpleGraph V) (hc : G.Connected) (hn : 1 < n)
    (hm : 2*Gᶜ.edgeFinset.card+3 ≤ 6*matchingNumber G) : Traceable G :=
  conjecture208_matching_witness G hc hn _ (matchingNumber_attained G) hm

#print axioms Graffiti208.conjecture208
