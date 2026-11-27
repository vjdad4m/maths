import CrossFourPath34_384b
import CrossFourPendant34_384b
import TwoEdgeFinish34_384b

namespace Graffiti384b.CrossFour34
open Finset SimpleGraph LowSample
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The exact #384b bound for the entire two-ear case at order 34. -/
theorem two_ears (n : Fintype.card V=34) (t : (types G).card=33) {y z : V}
    (yz : y≠z) (dy : G.degree y=2) (dz : G.degree z=2)
    (py : 0<trianglesAt G y) (pz : 0<trianglesAt G z) : gamma G≤bound G := by
  classical
  by_cases free : triangleFreeOn G ((twos G).biUnion (G.neighborFinset ·))
  · exact path G n t yz dy dz py pz free
  by_contra! fail
  obtain ⟨q,h,ears,_,hi⟩ := SharedExact34.failure_profile G t yz dy dz py pz fail
  have sep := SharedExact34.separate G n t yz dy dz py pz fail
  obtain ⟨e,f,a,b,which,ear,ab,priv,miss⟩ := Triangle34.end_anchor G n t yz dy dz py pz fail
  rcases which with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have hit := triangle_covers G ears ear dz sep ab miss free
    exact (not_lt_of_ge (pendant G n t h yz ears (by omega) hi sep ear ab priv miss hit)) fail
  · have pair := ears.trans (pair_comm ..)
    have hit := triangle_covers G pair ear dy sep.symm ab miss free
    exact (not_lt_of_ge (pendant G n t h yz.symm pair (by omega) (by rw [union_comm]; exact hi) sep.symm ear ab priv miss hit)) fail

theorem single_ear (res : Minimal.Residual G) (n : Fintype.card V=34) :
    (high G).card=32 ∧ ∃ e,twos G={e} := by
  obtain ⟨_,t,hi⟩ := Frontier34.boundary G res n
  obtain ⟨card,pos,_⟩ := Frontier34.ears G res n
  have one : (twos G).card=1 := by
    by_contra ne
    have many : 1<(twos G).card := by rcases hi with h|h <;> omega
    obtain ⟨y,yt⟩ := card_pos.mp (show 0<(twos G).card by omega)
    obtain ⟨z,zt,zy⟩ := exists_ne_of_one_lt_card many y
    exact (not_lt_of_ge (two_ears G n t zy.symm (LowSample.two_degree G yt) (LowSample.two_degree G zt)
      (by have := pos y yt; omega) (by have := pos z zt; omega))) res.2.2.1
  exact ⟨by rcases hi with h|h <;> omega,card_eq_one.mp one⟩
end Graffiti384b.CrossFour34
#print axioms Graffiti384b.CrossFour34.path
#print axioms Graffiti384b.CrossFour34.pendant
#print axioms Graffiti384b.CrossFour34.two_ears
#print axioms Graffiti384b.CrossFour34.single_ear

