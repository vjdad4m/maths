import SixSingletonQ1Sparse1Cert189
import SixSingletonQ1TemplateWalk189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.Q1Sparse1
open Q1Template SimpleGraph Finset
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000

def fixed : List (Fin 10 × Fin 10) := [(6, 7), (6, 8), (7, 8), (6, 0), (6, 3), (6, 4), (6, 5), (7, 1), (7, 2), (7, 3), (7, 4), (7, 5)]
def ends : Fin 21 → Option (Fin 10 × Fin 10) := ![some (0,1),some (0,2),some (0,3),some (0,4),some (0,5),some (1,2),some (1,3),some (1,4),some (1,5),some (2,3),some (2,4),some (2,5),some (3,4),some (3,5),some (4,5),some (0,9),some (1,9),some (2,9),some (3,9),some (4,9),some (5,9)]
def start (_i : Fin 40) : Fin 10 :=
  9
private theorem ok : ∀ i, (visit i).Nodup ∧ (∀ u,u∈visit i) ∧
    (visit i).Chain' (Allows fixed ends (requirement i)) ∧
    (visit i).head? = some (start i)  := by
  decide



theorem from_template {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (f : Fin 10→V) (inj : Function.Injective f)
    (base : ∀ u v,(u,v)∈fixed → G.Adj (f u) (f v))
    (B : Bit)
    (edge : ∀ k u v,ends k=some (u,v) → B k.val=true → G.Adj (f u) (f v))
    (found : Found B) :
    ∃ i t, RouteOn G (univ.image f) (f (start i)) t  := by
  obtain ⟨i,hi⟩ := found
  obtain ⟨nd,cov,ch,hd⟩ := ok i
  obtain ⟨t,r⟩ := lift_template f inj fixed ends _ B base edge hi _ nd cov ch _ hd
  exact ⟨i,t,r⟩

#print axioms from_template
end Graffiti189LongestPath.CrossSaturation.ThresholdSix.PortCertificates.Q1Sparse1
