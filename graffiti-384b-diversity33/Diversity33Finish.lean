import ThreeFinish33

namespace Graffiti384b.Diversity33
open Finset SimpleGraph
open private Repair.full_nbr from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At order and diversity 33, deleting the zero vertex forces a core
whose required 2-domination number exceeds its sampling bound. -/
theorem order33 {z : V} (n : Fintype.card V=33) (t : (types G).card=33)
    (conn : G.Connected) (zz : trianglesAt G z=0) : gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt; intro bad
  have inj := ForcedCubics.exact_counts_injective G n t
  obtain ⟨_,v,_,_,_,vs,dv,zv,_,_,cover⟩ := ForcedCubics.full_obstruction G n t conn bad zz
  have vz : v≠z := by intro h; subst v; omega
  have edge : ∃ b,G.Adj z b := by
    obtain ⟨walk⟩ := conn z v
    cases walk with
    | nil => exact (vz rfl).elim
    | cons ed _ => exact ⟨_,ed⟩
  obtain ⟨b,zb⟩ := edge
  let P := ({z}:Finset V)ᶜ
  let H := G.induce (P:Set V)
  let s : P := ⟨v,by simp [P,vz]⟩
  obtain ⟨sz,_,sc,pos,ij,g⟩ := PositiveCore33.extremal_core G n t conn bad inj zz zb
  have ord : Fintype.card P=32 := (Fintype.card_coe P).trans sz
  have hs : trianglesAt H s=3 := (sc s).trans vs
  have ds : H.degree s=3 := by
    have no : ({z}:Finset V).filter (G.Adj v)=∅ := filter_eq_empty_iff.mpr (by
      intro y ym; obtain rfl := mem_singleton.mp ym; exact fun h => zv h.symm)
    have total := Repair.full_nbr G v {z}
    change (({z}:Finset V).filter (G.Adj v)).card+_= _ at total
    rw [no,card_empty,Nat.zero_add] at total
    rw [EarAnchor.induced_degree]; exact total.trans dv
  have meet (K : Finset P) (kc : H.IsNClique 5 K) : ∃ x∈K,H.Adj s x := by
    let emb : P ↪ V := Function.Embedding.subtype _
    have lifted : G.IsNClique 5 (K.map emb) := kc.map.mono (G.spanningCoe_induce_le (s:=(P:Set V)))
    obtain ⟨y,ym,vy⟩ := (cover _ lifted).2
    obtain ⟨x,xm,rfl⟩ := mem_map.mp ym
    exact ⟨x,xm,vy⟩
  have sol := ThreeChoice.core_bound H ord ds hs pos ij meet
  change gamma H=16 at g; omega

/-- Graffiti.pc 384b holds for exactly 33 triangle-incidence types,
at every graph order. -/
theorem exact33 (conn : G.Connected) (hn : 2<Fintype.card V) (t : (types G).card=33) :
    gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro bad
  obtain ⟨s,sz,hc,same,_,_,⟨z,zz,_⟩,fail⟩ := OneEar.diversity33_failure G conn hn bad t
  exact (not_lt_of_ge (order33 _ ((Fintype.card_coe s).trans sz) ((congrArg card same).trans t) hc zz)) fail

/-- Combine exact diversity 33 with the previous exact 32 and ≥34 results. -/
theorem at_least_32 (conn : G.Connected) (hn : 2<Fintype.card V) (t : 32≤(types G).card) :
    gamma G≤bound G := by
  by_cases h : (types G).card=32
  · exact Below33.exact32 G conn hn h
  by_cases k : (types G).card=33
  · exact exact33 G conn hn k
  exact Diversity35.exact_of_at_least_34_types G conn hn (by omega)

/-- Every failure has a connected induced failure with the same at most
31 triangle counts and at most 33 vertices. -/
theorem remaining (conn : G.Connected) (hn : 2<Fintype.card V) (bad : bound G<gamma G) :
    (types G).card≤31 ∧ ∃ s : Finset V, 2<s.card ∧ s.card≤33 ∧
      (G.induce (s:Set V)).Connected ∧ types (G.induce (s:Set V))=types G ∧
      bound (G.induce (s:Set V))<gamma (G.induce (s:Set V)) := by
  have cap : (types G).card≤31 := by
    by_contra! big
    exact (not_lt_of_ge (at_least_32 G conn hn big)) bad
  exact ⟨cap,Below33.induced_bound G (by omega) conn hn bad⟩

end Graffiti384b.Diversity33
#print axioms Graffiti384b.Diversity33.order33
#print axioms Graffiti384b.Diversity33.exact33
#print axioms Graffiti384b.Diversity33.at_least_32
#print axioms Graffiti384b.Diversity33.remaining
