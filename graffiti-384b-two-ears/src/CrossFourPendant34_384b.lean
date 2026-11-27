import CrossFourFrame34_384b
import TwoEdgeLink34_384b
import CrossFourPendantLink34_384b

namespace Graffiti384b.CrossFour34
open Finset SimpleGraph LowSample
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem pendant (n : Fintype.card V=34) (t : (types G).card=33) (h : (high G).card=31)
    {e z a b : V} (ez : e≠z) (ears : twos G={e,z}) (q : (types G).card≤(nonleaves G).card)
    (hi : G.neighborFinset e∪G.neighborFinset z⊆high G)
    (sep : Disjoint (G.neighborFinset e) (G.neighborFinset z))
    (ear : G.neighborFinset e={a,b}) (ab : G.Adj a b) (priv : G.neighborFinset a∩G.neighborFinset b={e})
    (miss : ∀ j∈G.neighborFinset z,¬G.Adj a j) (hit : ∀ j∈G.neighborFinset z,G.Adj b j) :
    gamma G≤bound G := by
  by_contra! fail
  have et : e∈twos G := ears ▸ mem_insert_self ..
  have zt : z∈twos G := ears ▸ mem_insert_of_mem (mem_singleton_self _)
  have thin := pendant_link G ez ears q hi sep ear ab priv miss hit fail
  exact (not_lt_of_ge (finish_frame G n t h et zt ez hi sep ear ab priv (TwoEdge34.half_degree G thin))) fail
end Graffiti384b.CrossFour34
#print axioms Graffiti384b.CrossFour34.pendant
