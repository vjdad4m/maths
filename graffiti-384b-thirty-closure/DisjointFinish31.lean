import DisjointSaving31

namespace Graffiti384b.Disjoint30
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- At every order, thirty nonleaves and thirty-one distinct triangle
counts suffice for the catalogue two-domination bound. -/
theorem exact_thirty_nonleaves (conn : G.Connected) (t : (types G).card=31) (q : (nonleaves G).card=30) :
    gamma G≤bound G := by
  classical
  by_contra! bad
  let P := nonleaves G
  let H := G.induce (P:Set V)
  obtain ⟨u,s,du,su,_,ds,ss,_,us,dis,cover⟩ := OneCommon.residual G conn t q bad
  let M : Board H := ⟨u,s,du,su,ds,ss,us,dis⟩
  obtain ⟨n,_,_,fi,pos,g⟩ := Frontier31.positive_core G conn t q bad
  have upper := M.saving n pos fi (fun C cl => (cover C cl).1)
  change gamma H=15 at g
  omega

end Graffiti384b.Disjoint30
#print axioms Graffiti384b.Disjoint30.exact_thirty_nonleaves
