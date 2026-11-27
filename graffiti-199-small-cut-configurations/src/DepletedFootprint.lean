import CutAndOrder

namespace Graffiti199Depleted

open Graffiti199K2.NearPacking.Depleted
open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {loss : Bool}

def fixedInnerEdges : List (K × K) :=
  [(0,1),(0,2),(0,3),(1,2),(4,5),(4,6),(4,7),(5,6),(8,9)]

/-- The four reassigned highs can be provided in either order in each half.
The degree-three hypotheses ensure the low vertices have no additional edges. -/
structure DepletedFootprint (G : SimpleGraph V) [DecidableRel G.Adj] (loss : Bool) where
  inner : K ↪ V
  terminal : O ↪ V
  reassigned : Fin 4 ↪ I
  reassignedHigh : ∀ j, high (reassigned j) = true
  fixed : ∀ a b, (a,b) ∈ fixedInnerEdges → G.Adj (inner a) (inner b)
  firstHalf :
    G.Adj (inner 8) (inner (inside (reassigned 0))) ∧
    G.Adj (inner 8) (inner (inside (reassigned 1))) ∧
    G.Adj (inner (inside (reassigned 0))) (inner (inside (reassigned 1)))
  secondHalf :
    G.Adj (inner 9) (inner (inside (reassigned 2))) ∧
    G.Adj (inner 9) (inner (inside (reassigned 3))) ∧
    G.Adj (inner (inside (reassigned 2))) (inner (inside (reassigned 3)))
  nonedges : ∀ a b, (a,b) ∈ forbidden → ¬ G.Adj (inner a) (inner b)
  terminalEdges : ∀ a b, (a,b) ∈ Graffiti199Depleted.terminalEdges →
    G.Adj (terminal a) (terminal b)
  innerDegree : ∀ i ∈ ([0,4,8,9] : List K), G.degree (inner i) = 3
  terminalDegree : ∀ i ∈ ([0,1] : List O), G.degree (terminal i) = 3
  separate : Disjoint (innerRegion inner) (terminalRegion terminal loss)
  cover : ∀ v, v ∈ innerRegion inner ∨ v ∈ terminalRegion terminal loss

private theorem three_names_exhaust_neighbors
    {ι : Type*} (f : ι ↪ V) {x a b c : ι}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (degree : G.degree (f x) = 3)
    (xa : G.Adj (f x) (f a)) (xb : G.Adj (f x) (f b)) (xc : G.Adj (f x) (f c))
    (v : V) (adj : G.Adj (f x) v) : ∃ i ∈ [a,b,c], f i = v := by
  classical
  let N : Finset V := {f a, f b, f c}
  have sub : N ⊆ G.neighborFinset (f x) := by
    intro y ty
    rcases (show y = f a ∨ y = f b ∨ y = f c by simpa only
      [N,Finset.mem_insert,Finset.mem_singleton] using ty) with rfl|rfl|rfl
    · exact (G.mem_neighborFinset _ _).mpr xa
    · exact (G.mem_neighborFinset _ _).mpr xb
    · exact (G.mem_neighborFinset _ _).mpr xc
  have firstOff : f a ∉ ({f b, f c} : Finset V) := by
    simp [f.injective.ne ab,f.injective.ne ac]
  have n3 : N.card = 3 := by
    change (insert (f a) ({f b, f c} : Finset V)).card = 3
    rw [Finset.card_insert_of_not_mem firstOff,Finset.card_pair (f.injective.ne bc)]
  have exactN : N = G.neighborFinset (f x) := Finset.eq_of_subset_of_card_le sub (by
    rw [G.card_neighborFinset_eq_degree,degree,n3])
  have hv : v ∈ N := exactN.symm ▸ (G.mem_neighborFinset _ _).mpr adj
  rcases (show v = f a ∨ v = f b ∨ v = f c by simpa only
    [N,Finset.mem_insert,Finset.mem_singleton] using hv) with rfl|rfl|rfl
  · exact ⟨a,by simp,rfl⟩
  · exact ⟨b,by simp,rfl⟩
  · exact ⟨c,by simp,rfl⟩

private theorem inside_ne_of_ne {a b : I} (ne : a ≠ b) : inside a ≠ inside b :=
  fun e => ne (Fin.ext (congrArg (fun k : K => k.val) e))

private theorem end_ne_inside {k : K} (large : 8 ≤ k.val) (a : I) : k ≠ inside a := by
  intro e
  have eq : k.val = a.val := congrArg (fun x : K => x.val) e
  have bound := a.isLt
  omega

/-- The finite table can be used without supplying its row number. -/
theorem DepletedFootprint.normalize (F : DepletedFootprint G loss) :
    ∃ L : NormalizedDepleted G loss, L.inner = F.inner ∧ L.terminal = F.terminal := by
  let f := F.reassigned
  obtain ⟨r,hA,hB⟩ := covered (f 0) (f 1) (f 2) (f 3)
    (F.reassignedHigh 0) (F.reassignedHigh 1) (F.reassignedHigh 2) (F.reassignedHigh 3)
    (f.injective.ne (by decide)) (f.injective.ne (by decide)) (f.injective.ne (by decide))
    (f.injective.ne (by decide)) (f.injective.ne (by decide)) (f.injective.ne (by decide))
  let a := (halves r).1
  let b := (halves r).2.1
  let c := (halves r).2.2.1
  let d := (halves r).2.2.2
  have reorder {u v u' v' : I} {k : K} (uv : u ≠ v) (eq : same u v u' v')
      (h : G.Adj (F.inner k) (F.inner (inside u)) ∧
        G.Adj (F.inner k) (F.inner (inside v)) ∧
        G.Adj (F.inner (inside u)) (F.inner (inside v))) :
      u' ≠ v' ∧ G.Adj (F.inner k) (F.inner (inside u')) ∧
        G.Adj (F.inner k) (F.inner (inside v')) ∧
        G.Adj (F.inner (inside u')) (F.inner (inside v')) := by
    rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨uv,h⟩
    · exact ⟨uv.symm,h.2.1,h.1,h.2.2.symm⟩
  have ⟨ab,ax,bx,abe⟩ := reorder (f.injective.ne (by decide : (0 : Fin 4) ≠ 1)) hA F.firstHalf
  have ⟨cd,cx,dx,cde⟩ := reorder (f.injective.ne (by decide : (2 : Fin 4) ≠ 3)) hB F.secondHalf
  have required (x y : K) (h : (x,y) ∈ edges r false) : G.Adj (F.inner x) (F.inner y) := by
    change (x,y) ∈ fixedInnerEdges ++
      [(inside a,inside b),(inside c,inside d),(8,inside a),(8,inside b),(9,inside c),(9,inside d)] at h
    rcases List.mem_append.mp h with hf|hv
    · exact F.fixed x y hf
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with e|e|e|e|e|e <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
      · exact abe
      · exact cde
      · exact ax
      · exact bx
      · exact cx
      · exact dx
  have innerLow (i : K) (ns : List K) (e : innerLowNeighbors r i = some ns)
      (v : V) (adj : G.Adj (F.inner i) v) : ∃ j ∈ ns, F.inner j = v := by
    fin_cases i
    · have eq : [1,2,3] = ns := Option.some.inj e
      rw [← eq]
      exact three_names_exhaust_neighbors F.inner (by decide) (by decide) (by decide)
        (F.innerDegree 0 (by decide)) (F.fixed 0 1 (by decide)) (F.fixed 0 2 (by decide))
        (F.fixed 0 3 (by decide)) v adj
    · cases e
    · cases e
    · cases e
    · have eq : [5,6,7] = ns := Option.some.inj e
      rw [← eq]
      exact three_names_exhaust_neighbors F.inner (by decide) (by decide) (by decide)
        (F.innerDegree 4 (by decide)) (F.fixed 4 5 (by decide)) (F.fixed 4 6 (by decide))
        (F.fixed 4 7 (by decide)) v adj
    · cases e
    · cases e
    · cases e
    · have eq : [9,inside a,inside b] = ns := Option.some.inj e
      rw [← eq]
      exact three_names_exhaust_neighbors F.inner (end_ne_inside (by decide) a)
        (end_ne_inside (by decide) b) (inside_ne_of_ne ab)
        (F.innerDegree 8 (by decide)) (F.fixed 8 9 (by decide)) ax bx v adj
    · have eq : [8,inside c,inside d] = ns := Option.some.inj e
      rw [← eq]
      exact three_names_exhaust_neighbors F.inner (end_ne_inside (by decide) c)
        (end_ne_inside (by decide) d) (inside_ne_of_ne cd)
        (F.innerDegree 9 (by decide)) (F.fixed 8 9 (by decide)).symm cx dx v adj
  have termLow (i : O) (ns : List O) (e : terminalLowNeighbors i = some ns)
      (v : V) (adj : G.Adj (F.terminal i) v) : ∃ j ∈ ns, F.terminal j = v := by
    fin_cases i
    · have eq : [1,2,3] = ns := Option.some.inj e
      rw [← eq]
      exact three_names_exhaust_neighbors F.terminal (by decide) (by decide) (by decide)
        (F.terminalDegree 0 (by decide)) (F.terminalEdges 0 1 (by decide))
        (F.terminalEdges 0 2 (by decide)) (F.terminalEdges 0 3 (by decide)) v adj
    · have eq : [0,4,5] = ns := Option.some.inj e
      rw [← eq]
      exact three_names_exhaust_neighbors F.terminal (by decide) (by decide) (by decide)
        (F.terminalDegree 1 (by decide)) (F.terminalEdges 0 1 (by decide)).symm
        (F.terminalEdges 1 4 (by decide)) (F.terminalEdges 1 5 (by decide)) v adj
    · cases e
    · cases e
    · cases e
    · cases e
  exact ⟨⟨F.inner,F.terminal,r,required,F.nonedges,innerLow,F.terminalEdges,termLow,
    F.separate,F.cover⟩,rfl,rfl⟩

/-- The block footprint with four reassigned inner highs and zero or one
terminal loss has a Hamiltonian path, under the explicit small-cut property. -/
theorem depleted_footprint_order_and_path (F : DepletedFootprint G loss)
    (reach : EdgeReachAfterSmallDeletion G)
    (looseDegree : 3 ≤ G.degree (F.inner 3)) (looseOff : G.degree (F.inner 3) ≠ 3) :
    (Fintype.card V = if loss then 15 else 16) ∧ Nonempty (PathOn G Set.univ) := by
  obtain ⟨L,h,_⟩ := F.normalize
  exact normalized_depleted_order_and_path L reach (h.symm ▸ looseDegree) (h.symm ▸ looseOff)

/-- This version states the small-cut hypotheses directly in graph terms. -/
theorem depleted_footprint_of_singleton_cuts (F : DepletedFootprint G loss)
    (below : ∀ D : Finset V, D.card < 3 → (G.induce {v | v ∉ D}).Preconnected)
    (three : ∀ D : Finset V, D.card = 3 →
      (G.induce {v | v ∉ D}).Preconnected ∨
        ∃ s : Survives D, (∀ t : Survives D, ¬ G.Adj s.val t.val) ∧
          ∀ x y : Survives D, x ≠ s → y ≠ s → (G.induce {v | v ∉ D}).Reachable x y)
    (looseDegree : 3 ≤ G.degree (F.inner 3)) (looseOff : G.degree (F.inner 3) ≠ 3) :
    (Fintype.card V = if loss then 15 else 16) ∧ Nonempty (PathOn G Set.univ) :=
  depleted_footprint_order_and_path F (edgeReach_of_singleton_cuts below three) looseDegree looseOff

#print axioms DepletedFootprint.normalize
#print axioms depleted_footprint_order_and_path
#print axioms depleted_footprint_of_singleton_cuts

end Graffiti199Depleted
