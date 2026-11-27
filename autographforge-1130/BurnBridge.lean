import Sharpness
import TraceableBurn
namespace TraceableBurn
open SimpleGraph PathCycleSharpness
theorem burns_of_cover {V : Type*} {G : SimpleGraph V} (hc : G.Connected)
    {k : ℕ} (h : Cover G k) : Burns G k := by
  obtain ⟨c,cover⟩ := h
  let flip : Fin k → Fin k := fun r => ⟨k-1-r.val,by have h := r.isLt; omega⟩
  refine ⟨fun t => c (flip t),?_⟩
  intro x
  obtain ⟨r,hr⟩ := cover x
  have inv : flip (flip r)=r := Fin.ext (by
    have h := r.isLt
    change k-1-(k-1-r.val)=r.val
    omega)
  refine ⟨flip r,?_⟩
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist (c (flip (flip r))) x
  refine ⟨p,?_⟩
  have hp' := hp.trans (congrArg (fun z : Fin k => G.dist (c z) x) inv)
  change p.length≤k-1-(k-1-r.val)
  have h := r.isLt
  calc
    p.length = G.dist (c r) x := hp'
    _ ≤ r.val := hr
    _ = k-1-(k-1-r.val) := by omega
end TraceableBurn
