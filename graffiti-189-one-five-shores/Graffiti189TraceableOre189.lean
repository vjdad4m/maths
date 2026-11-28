import OreClosure189

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

open private degree_increasing graphSize_lt graphSize_le from OreClosure189
omit [DecidableRel H.Adj] in
/-- Iterated unrooted Ore closure at the traceability threshold. -/
theorem traceable_closure (sub : G ≤ H)
    (hdeg : ∀ x y, H.Adj x y → ¬ G.Adj x y → Fintype.card V ≤ G.degree x + G.degree y + 1)
    (hp : Traceable H) : Traceable G := by
  classical
  induction hn : graphSize H-graphSize G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases eq : G=H
    · simpa [eq] using hp
    have not_sub : ¬ H ≤ G := fun e=>eq (le_antisymm sub e)
    have missing : ∃ u v, H.Adj u v ∧ ¬G.Adj u v := by
      by_contra neg
      push_neg at neg
      exact not_sub (fun {u v} e=>neg u v e)
    obtain ⟨u,v,uv,nu⟩ := missing
    let K := G ⊔ fromEdgeSet ({s(u,v)} : Set (Sym2 V))
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    have gk : G≤K := le_sup_left
    have kh : K≤H := by
      intro x y e
      rcases (sup_adj _ _ x y).mp e with e|e
      · exact sub e
      · obtain ⟨es,_⟩ := (fromEdgeSet_adj _).mp e
        have eqs : s(x,y)=s(u,v) := es
        apply (SimpleGraph.mem_edgeSet H).mp
        rw [eqs]
        exact (SimpleGraph.mem_edgeSet H).mpr uv
    have kv : K.Adj u v := (sup_adj _ _ _ _).mpr (Or.inr ((fromEdgeSet_adj _).mpr ⟨rfl,uv.ne⟩))
    have glt : G < K := lt_of_le_of_ne gk (fun e=>nu (e.symm ▸ kv))
    have less : graphSize H-graphSize K<n := by
      have smaller := graphSize_lt glt
      have below := graphSize_le kh
      omega
    have nd (x y : V) (e : H.Adj x y) (k : ¬K.Adj x y) :
        Fintype.card V ≤ K.degree x+K.degree y+1 := by
      have orig := hdeg x y e (fun g=>k (gk g))
      have dx := degree_increasing gk x
      have dy := degree_increasing gk y
      omega
    have rr := ih _ less (G:=K) kh nd rfl
    refine traceable_closure_one (u:=u) (v:=v) ?_ (hdeg u v uv nu) rr
    intro x y e
    rcases (sup_adj _ _ x y).mp e with e|e
    · exact Or.inl e
    · exact Or.inr ((fromEdgeSet_adj _).mp e).1

#print axioms traceable_closure
end Graffiti189Ore
