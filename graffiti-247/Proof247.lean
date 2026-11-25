/-
# Graffiti.pc #247 is false

The [Written on the Wall II catalogue, p. 144](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf) lists as open the February 23, 2007 conjecture that every finite connected regular graph has total domination number at least twice its path-cover number. A total dominating set contains a neighbor of each vertex, including each of its own vertices. A path cover is a partition into nonempty vertex-disjoint ordinary paths (singletons allowed).

Take four copies of the complete graph on nine vertices. In copy i, remove the edge x_i y_i. Add one new vertex c, with edges to x_i and y_i in every copy, and no other new edges. The result has 37 vertices, is connected, and is 8-regular: c has eight neighbors; the endpoints of each removed edge swap the lost neighbor for c; all other degrees stay eight.

The total domination number is exactly 5. The set containing c and one x_i per copy works: c has a selected neighbor, c dominates every x_i and y_i, and x_i dominates all other vertices of its copy. Conversely, each copy must contain a selected vertex, because its seven vertices outside {x_i,y_i} have no neighbors outside the copy. With just four selected vertices there would be exactly one per copy and no c, so none of the selected vertices would have a selected neighbor.

The path-cover number is exactly 3. Removing c splits any path containing c into at most two paths, and the other paths stay unchanged. Four components of G−c require at least four paths, so a cover of G needs at least three. Each K9−xy admits a spanning path starting at x (for labels x=0,y=1, use [0,2,1,3,4,5,6,7,8]). Use c to join two such spanning paths along their x endpoints and cover the other two copies separately.

Thus gamma_t=5<6=2p, contradicting the conjecture. The same construction with k copies of K_{2k+1} minus one edge gives a connected 2k-regular graph with gamma_t=k+1 and p=k−1 for k≥2, and disproves the inequality for all k≥4. The Lean certificate is for the concrete k=4 witness. No claim is made about the smallest counterexample or the smallest regular degree for which the conjecture fails.

## Source audit

The official entry and [Douglas B. West's open-problem notes](https://dwest.web.illinois.edu/regs/graffiti.html) mention proof for regular degree at most 3. See also the [primary DeLaViña–Liu–Pepper–Waller–West paper](https://www.uhd.edu/documents/academics/sciences/total-dom-2007.pdf). Searches by catalogue number, author, formula, construction, and partial-result bibliography found no prior full resolution. A similarly numbered entry in original Written on the Wall concerns a different problem. These checks do not certify priority.

Replay with Lean and Mathlib v4.19.0.
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

namespace Graffiti247
open Finset
abbrev Vertex := Option (Fin 4 × Fin 9)

def adj : Vertex → Vertex → Prop
  | none, none => False
  | none, some (_,j) | some (_,j), none => j = 0 ∨ j = 1
  | some (i,j), some (k,l) => i = k ∧ j ≠ l ∧ ¬((j=0 ∧ l=1) ∨ (j=1 ∧ l=0))

instance : DecidableRel adj := by
  intro a b
  cases a <;> cases b <;> unfold adj <;> infer_instance

def G : SimpleGraph Vertex where
  Adj := adj
  symm := by
    intro a b
    cases a <;> cases b
    · simp [adj]
    · simp [adj]
    · simp [adj]
    · rcases ‹Fin 4 × Fin 9› with ⟨_,_⟩
      rename_i p
      rcases p with ⟨_,_⟩
      simp only [adj]; tauto
  loopless := by intro a; cases a <;> simp [adj]

instance : DecidableRel G.Adj := inferInstanceAs (DecidableRel adj)

def D : Finset Vertex := insert none ((Finset.univ : Finset (Fin 4)).image fun i => some (i,0))

def TotallyDominates (S : Finset Vertex) := ∀ v : Vertex, ∃ w ∈ S, G.Adj v w

theorem dom : TotallyDominates D := by
  intro v
  cases v with
  | none => exact ⟨some (0,0), by simp [D], by decide⟩
  | some p =>
    rcases p with ⟨i,j⟩
    by_cases h : j=0 ∨ j=1
    · exact ⟨none,by simp [D],h⟩
    · refine ⟨some (i,0), by simp [D], ?_⟩
      change i=i ∧ j≠0 ∧ ¬((j=0 ∧ (0:Fin 9)=1) ∨ (j=1 ∧ (0:Fin 9)=0))
      aesop

theorem dom_card : D.card = 5 := by decide

theorem regular : ∀ v : Vertex, G.degree v = 8 := by decide

def toHub (v : Vertex) : G.Reachable v none := by
  cases v with
  | none => exact ⟨.nil⟩
  | some p =>
    rcases p with ⟨i,j⟩
    by_cases h : j=0 ∨ j=1
    · exact ⟨.cons (show G.Adj (some (i,j)) none from h) .nil⟩
    · have h₁ : G.Adj (some (i,j)) (some (i,0)) := by
        change i=i ∧ j≠0 ∧ ¬((j=0 ∧ (0:Fin 9)=1) ∨ (j=1 ∧ (0:Fin 9)=0))
        aesop
      exact ⟨.cons h₁ (.cons (show G.Adj (some (i,0)) none from Or.inl rfl) .nil)⟩

theorem connected : G.Connected := by
  apply (SimpleGraph.connected_iff G).2
  exact ⟨fun u v => (toHub u).trans (toHub v).symm, ⟨none⟩⟩

def blocks (l : List Vertex) : Finset (Fin 4) :=
  (l.filterMap (Option.map Prod.fst)).toFinset

private lemma blockMem {i : Fin 4} {l : List Vertex} :
    i ∈ blocks l ↔ ∃ j : Fin 9, some (i,j) ∈ l := by
  simp only [blocks, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨p,hp,he⟩
    cases p with
    | none => simp at he
    | some p =>
      rcases p with ⟨a,b⟩
      change some a = some i at he
      have he := Option.some.inj he
      subst a; exact ⟨b,hp⟩
  · rintro ⟨j,hj⟩
    exact ⟨some (i,j),hj,rfl⟩

private lemma blocks_append (a b : List Vertex) :
    blocks (a++b) = blocks a ∪ blocks b := by
  ext i
  simp only [blockMem, List.mem_append, Finset.mem_union]
  constructor
  · rintro ⟨j,h|h⟩
    · exact Or.inl ⟨j,h⟩
    · exact Or.inr ⟨j,h⟩
  · rintro (⟨j,h⟩|⟨j,h⟩)
    · exact ⟨j,Or.inl h⟩
    · exact ⟨j,Or.inr h⟩

private lemma blocks_cons_none (l : List Vertex) : blocks (none::l) = blocks l := rfl

private lemma branch (i : Fin 4) (j : Fin 9) :
    ∀ l : List Vertex, (some (i,j)::l).Chain' G.Adj → none ∉ l →
      blocks (some (i,j)::l) ⊆ {i} := by
  intro l
  induction l generalizing i j with
  | nil => simp [blocks]
  | cons a r ih =>
    intro hChain hHub
    have hn : a ≠ none := by
      intro e; exact hHub (List.mem_cons.2 (Or.inl e.symm))
    cases a with
    | none => exact (hn rfl).elim
    | some p =>
      rcases p with ⟨i',j'⟩
      obtain ⟨hE,hC⟩ := List.chain'_cons.1 hChain
      have hEq : i=i' := hE.1
      subst i'
      have hT : blocks (some (i,j')::r) ⊆ {i} :=
        ih i j' hC (fun h => hHub (List.mem_cons.2 (Or.inr h)))
      intro b hb
      rw [blockMem] at hb
      obtain ⟨k,hk⟩ := hb
      rcases List.mem_cons.1 hk with h|h
      · have he := congrArg Prod.fst (Option.some.inj h)
        exact Finset.mem_singleton.2 he
      · exact hT (blockMem.2 ⟨k,h⟩)

private lemma block_bound_nohub {l : List Vertex} (hChain : l.Chain' G.Adj)
    (hHub : none ∉ l) : (blocks l).card ≤ 1 := by
  cases l with
  | nil => decide
  | cons a r =>
    cases a with
    | none => exact (hHub (by simp)).elim
    | some p =>
      rcases p with ⟨i,j⟩
      have hh := card_le_card (branch i j r hChain (fun h => hHub (by simp [h])))
      simpa using hh

def Cover (ps : List (List Vertex)) :=
  ps.flatten.Nodup ∧ (∀ v : Vertex, v ∈ ps.flatten) ∧ ∀ p ∈ ps, p.Chain' G.Adj ∧ p ≠ []


private lemma block_bound {l : List Vertex} (hChain : l.Chain' G.Adj)
    (hn : l.Nodup) :
    (blocks l).card ≤ 1 + (if none ∈ l then 1 else 0) := by
  by_cases h : none ∈ l
  · rw [if_pos h]
    obtain ⟨a,b,rfl⟩ := List.append_of_mem h
    obtain ⟨ha,hb,-⟩ := List.chain'_append.1 hChain
    obtain ⟨hna,hnb,hd⟩ := List.nodup_append.1 hn
    have hA : none ∉ a := by
      intro hh
      exact (List.disjoint_left.1 hd hh) (by simp)
    have hB : none ∉ b := (List.nodup_cons.1 hnb).1
    rw [blocks_append, blocks_cons_none]
    have hsum := Finset.card_union_le (blocks a) (blocks b)
    have ha' := block_bound_nohub ha hA
    have hb' : (blocks b).card ≤ 1 := block_bound_nohub hb.tail hB
    omega
  · rw [if_neg h]
    exact block_bound_nohub hChain h

private lemma cover_blocks_bound :
    ∀ ps : List (List Vertex), ps.flatten.Nodup →
      (∀ p ∈ ps, p.Chain' G.Adj) →
      (blocks ps.flatten).card ≤ ps.length + (if none ∈ ps.flatten then 1 else 0) := by
  intro ps
  induction ps with
  | nil => decide
  | cons p qs ih =>
    intro hn hChain
    rw [List.flatten_cons]
    obtain ⟨hp,hqs,hd⟩ := List.nodup_append.1 (by simpa using hn)
    have hP := block_bound (hChain p (by simp)) hp
    have hQ := ih hqs (fun l hl => hChain l (List.mem_cons.2 (Or.inr hl)))
    have hsum := Finset.card_union_le (blocks p) (blocks qs.flatten)
    rw [blocks_append]
    simp only [List.length_cons,List.mem_append]
    by_cases hA : none ∈ p
    · have hB := List.disjoint_left.1 hd hA
      simp [hA,hB] at hP hQ ⊢
      omega
    · by_cases hB : none ∈ qs.flatten
      · simp [hA,hB] at hP hQ ⊢
        omega
      · simp [hA,hB] at hP hQ ⊢
        omega

theorem cover_min (ps : List (List Vertex)) (h : Cover ps) : 3 ≤ ps.length := by
  have hall : blocks ps.flatten = univ := by
    ext i
    simp only [blockMem, mem_univ, iff_true]
    exact ⟨0,h.2.1 (some (i,0))⟩
  have hh := cover_blocks_bound ps h.1 (fun p hp => (h.2.2 p hp).1)
  rw [hall, Finset.card_univ] at hh
  simp [h.2.1 none] at hh
  omega

theorem counterexample247 :
    ∃ (G' : SimpleGraph Vertex) (S : Finset Vertex),
      G' = G ∧ G'.Connected ∧ (∀ v, G.degree v = 8) ∧
      TotallyDominates S ∧ (∀ ps, Cover ps → S.card < 2*ps.length) := by
  refine ⟨G,D,rfl,connected,regular,dom,?_⟩
  intro ps h
  have := cover_min ps h
  rw [dom_card]
  omega


theorem dom_min (S : Finset Vertex) (h : TotallyDominates S) : 5 ≤ S.card := by
  classical
  have he : ∀ i : Fin 4, ∃ j : Fin 9, some (i,j) ∈ S := by
    intro i
    obtain ⟨v,hv,ha⟩ := h (some (i,2))
    cases v with
    | none =>
      have hh : (2 : Fin 9) = 0 ∨ (2 : Fin 9) = 1 := ha
      exact ((by decide : ¬((2 : Fin 9) = 0 ∨ (2 : Fin 9) = 1)) hh).elim
    | some v =>
      rcases v with ⟨k,j⟩
      have hik : i=k := ha.1
      subst k
      exact ⟨j,hv⟩
  choose j hj using he
  let f : Fin 4 → Vertex := fun i => some (i,j i)
  have hf : Function.Injective f := by
    intro a b hab
    exact congrArg Prod.fst (Option.some.inj hab)
  let T : Finset Vertex := univ.image f
  have hs : T ⊆ S := by
    intro v hv
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.1 hv
    exact hj i
  have ht : T.card = 4 := by
    dsimp [T]
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ]
    decide
  by_contra! hlt
  have hEq : T = S := Finset.eq_of_subset_of_card_le hs (by omega)
  obtain ⟨v,hv,ha⟩ := h (f 0)
  rw [← hEq] at hv
  obtain ⟨i,-,rfl⟩ := Finset.mem_image.1 hv
  have hi : (0 : Fin 4) = i := ha.1
  subst i
  exact G.loopless _ ha

def oneBranch (i : Fin 4) : List Vertex :=
  ([0,2,1,3,4,5,6,7,8] : List (Fin 9)).map (fun j => some (i,j))

def threePaths : List (List Vertex) :=
  [(oneBranch 0).reverse ++ [none] ++ oneBranch 1, oneBranch 2, oneBranch 3]

theorem cover_attained : Cover threePaths := by
  unfold Cover
  refine ⟨by decide, by decide, ?_⟩
  intro p hp
  simp only [threePaths,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl <;> decide

theorem exact_counterexample :
    G.Connected ∧ Fintype.card Vertex = 37 ∧ (∀ v, G.degree v = 8) ∧
    TotallyDominates D ∧ D.card = 5 ∧
    (∀ S, TotallyDominates S → 5 ≤ S.card) ∧
    Cover threePaths ∧ threePaths.length = 3 ∧
    (∀ ps, Cover ps → 3 ≤ ps.length) ∧ 5 < 2*3 := by
  exact ⟨connected,by decide,regular,dom,dom_card,dom_min,cover_attained,rfl,cover_min,by decide⟩

#print axioms Graffiti247.counterexample247
#print axioms Graffiti247.exact_counterexample
