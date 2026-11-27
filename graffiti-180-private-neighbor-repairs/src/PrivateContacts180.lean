import DetachedPair180

set_option warningAsError true
namespace Minimal180.PrivateCore
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Controlled
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If the two private leaves have more contacts in total than the common
eligible pool can hold disjointly, a detached two-vertex repair exists.
The hypotheses need not identify the returning vertex. -/
theorem first_of_private_contacts (J : SimpleGraph V) (jc : J.Connected) (hn : 2<Fintype.card V)
    (U C W A B : Finset V) (x y w p t u v : V) (xy : x≠y) (old : ¬J.Adj x y)
    (xw : J.Adj x w) (wy : J.Adj w y) (pt : p≠t) (cu : C⊆U) (ct : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (free : ({p,t}:Finset V)⊆(U\C).erase y)
    (safe : ∀ z∈({p,t}:Finset V),Con J ((univ\C).erase z))
    (failed : ∀ z∈({p,t}:Finset V),¬SingleWorks J C x y z)
    (pu : privateLeaves J C x p={u}) (tv : privateLeaves J C x t={v})
    (conn : Con J ((univ\C)\{p,t}))
    (feed : ∀ z∈({p,t}:Finset V),Dominates J ((univ\C)\{p,t}) z)
    (mixed : ∀ a∈C.erase x,J.Adj a p → J.Adj a t → ¬Dominates J ((univ\C)\{p,t}) a → J.Adj a x)
    (wc : W⊆C.erase x) (alive : ∀ b∈W,Dominates J ((univ\C)\{p,t}) b)
    (aw : A⊆W) (bw : B⊆W) (au : ∀ b∈A,J.Adj b u) (bv : ∀ b∈B,J.Adj b v)
    (overlap : W.card<A.card+B.card) :
    FirstForm J U x y w ∧ ∃ b∈W,¬J.Adj x b ∧ PairWorks J C {p,t} x y b := by
  classical
  have cnt := card_union_add_card_inter A B
  have cap := card_le_card (union_subset aw bw)
  have common : 0<(A∩B).card := by omega
  obtain ⟨b,hb⟩ := card_pos.mp common
  obtain ⟨a,b'⟩ := mem_inter.mp hb
  have hp : p∈({p,t}:Finset V) := mem_insert_self .. 
  have far := singleton_far J jc hn U C x y p u xy cu ct tip (free hp) (safe p hp) (failed p hp) pu
  have no : ¬J.Adj x b := fun xb => far (Or.inr (Or.inr ⟨b,xb,au b a⟩))
  have win := (detached_pair_iff J jc hn U C x y p t u v b xy cu ct tip free safe failed pu tv conn feed mixed
    (wc (aw a))).mpr ⟨no,au b a,bv b b',alive b (aw a)⟩
  refine ⟨(second_split_iff J jc hn x y w xy old xw wy U C cu ct tip).mpr ?_,b,aw a,no,win⟩
  refine ⟨{b},singleton_subset_iff.mpr (wc (aw a)),{p,t},free,?_,?_⟩
  · rw [card_singleton,card_pair pt]; decide
  · simpa only [sdiff_singleton_eq_erase,PairWorks] using win

#print axioms first_of_private_contacts
end Minimal180.PrivateCore
