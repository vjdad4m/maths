import Horizontal180
import Mathlib.Combinatorics.SimpleGraph.Operations

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Move v's attachment from p to u. The eligible degree-two p becomes
a leaf. All old eligible leaves survive when u was not one of them. -/
theorem rotation_gain (hn : 1<Fintype.card V) (J T : SimpleGraph V) (jsub : J≤G)
    (sub : T≤J) (tree : T.IsTree) (U : Finset V) (opt : (U ∩ leaves T).card=weightedLeaves J U)
    (u v p s : V) (edge : G.Adj u v) (up : u≠p) (pv : T.Adj p v) (ps : T.Adj p s) (vs : v≠s)
    (two : ∀ x, T.Adj p x → x=v ∨ x=s) (elig : p∈U) (free : u∉U ∩ leaves T)
    (side : (T.deleteEdges {s(p,v)}).Reachable p u) : weightedLeaves J U<weightedLeaves G U := by
  classical
  let D := T.deleteEdges {s(p,v)}
  let H := D ⊔ SimpleGraph.edge u v
  have add : H.Adj u v := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,edge.ne⟩)
  have route : H.Reachable p v := (side.mono (show D≤H from le_sup_left)).trans add.reachable
  have step {a b} (e : T.Adj a b) : H.Reachable a b := by
    by_cases eq : s(a,b)=s(p,v)
    · rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact route
      · exact route.symm
    · exact (show H.Adj a b from Or.inl (deleteEdges_adj.mpr ⟨e,eq⟩)).reachable
  have connected : H.Connected := by
    letI : Nonempty V := ⟨u⟩
    constructor
    intro a b
    obtain ⟨walk⟩ := tree.isConnected a b
    induction walk with
    | nil => exact Reachable.refl _
    | cons e _ ih => exact (step e).trans ih
  obtain ⟨K,ks,kt⟩ := connected.exists_isTree_le
  have toG : H≤G := by
    apply sup_le ((T.deleteEdges_le _).trans (sub.trans jsub))
    rw [← sup_eq_left]
    exact sup_edge_of_adj G edge
  have classify {a b} (e : K.Adj a b) :
      (T.Adj a b ∧ s(a,b)≠s(p,v)) ∨ (a=u ∧ b=v) ∨ (a=v ∧ b=u) := by
    rcases ks e with h|h
    · exact Or.inl (deleteEdges_adj.mp h)
    · exact Or.inr ((edge_adj ..).mp h).1
  have pne : p≠v := pv.ne
  have adjP {b} (e : K.Adj p b) : b=s := by
    rcases classify e with h|h|h
    · rcases two b h.1 with eq|eq
      · exact (h.2 (eq ▸ rfl)).elim
      · exact eq
    · exact (up h.1.symm).elim
    · exact (pne h.1).elim
  have oldLeaves : U ∩ leaves T ⊆ U ∩ leaves K := by
    intro w hw
    obtain ⟨wu,wl⟩ := mem_inter.mp hw
    have wnu : w≠u := fun eq => free (eq ▸ hw)
    refine mem_inter.mpr ⟨wu,leaf_of_unique K kt.isConnected hn w ?_⟩
    by_cases wv : w=v
    · subst w
      have adjV {b} (e : K.Adj v b) : b=u := by
        rcases classify e with h|h|h
        · have bp := leaf_unique T wl h.1 pv.symm
          exact (h.2 (by rw [bp,Sym2.eq_swap])).elim
        · exact (wnu h.1).elim
        · exact h.2
      exact fun h k => (adjV h).trans (adjV k).symm
    · have original {b} (e : K.Adj w b) : T.Adj w b := by
        rcases classify e with h|h|h
        · exact h.1
        · exact (wnu h.1).elim
        · exact (wv h.1).elim
      exact fun h k => leaf_unique T wl (original h) (original k)
  have extra : p∈U ∩ leaves K := mem_inter.mpr ⟨elig,leaf_of_unique K kt.isConnected hn p
    (fun h k => (adjP h).trans (adjP k).symm)⟩
  have absent : p∉U ∩ leaves T := fun h => vs (leaf_unique T (mem_inter.mp h).2 pv ps)
  have grow := card_le_card (insert_subset extra oldLeaves)
  rw [card_insert_of_not_mem absent,opt] at grow
  exact grow.trans (le_sup (f:=fun X => (U ∩ leaves X).card)
    (mem_filter.mpr ⟨mem_univ _,ks.trans toG,kt⟩))

#print axioms rotation_gain
end Minimal180
