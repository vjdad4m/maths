import PosaOrderedPair189
import PosaBridges189
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.PosaTracks Graffiti189LongestPath.PosaOrderedPair
set_option warningAsError true
set_option maxHeartbeats 3800000
namespace Graffiti189LongestPath.PosaBridgeAdapter
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Actual two-route existence under singleton deletion connectivity:
bridge objects from the graph feed the finite interval and walk realization. -/
theorem ordered_pair_of_singleton_connected {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (hn : 2≤p.length)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected) :
    Nonempty (OrderedPair p) := by
  classical
  let f : Fin (p.length+1) ↪ V :=
    ⟨fun i => p.getVert i.val,fun i j eq =>
      Fin.ext (hp.getVert_injOn (by change i.val≤p.length; omega)
        (by change j.val≤p.length; omega) eq)⟩
  have fr (z : V) : z∈Set.range f ↔ z∈p.support := by
    constructor
    · rintro ⟨i,rfl⟩
      exact p.getVert_mem_support i.val
    · intro zs
      obtain ⟨i,eq,il⟩ := mem_support_iff_exists_getVert.mp zs
      exact ⟨⟨i,by omega⟩,eq⟩
  obtain ⟨F⟩ := PosaBridges189.exists_family (G:=G) f (by
    intro i _ _
    have eq : (↑({f i}:Finset V):Set V)=({f i}:Set V) := by ext z; simp
    rw [←eq]
    exact conn ({f i}:Finset V) (by simp))
  let l (j : PosaBridges189.Label (G:=G) f) := (PosaBridges189.ends f j).1.val
  let r (j : PosaBridges189.Label (G:=G) f) := (PosaBridges189.ends f j).2.val
  let B (j : PosaBridges189.Label (G:=G) f) (h : j∈F.sources) :=
    Classical.choice (F.detour j h)
  let D (j : PosaBridges189.Label (G:=G) f) (h : j∈F.sources) : Detour p (l j) (r j) :=
    ⟨(B j h).lt,by have e := (PosaBridges189.ends f j).2.isLt; dsimp [r]; omega,
      (B j h).walk,(B j h).isPath,by
        intro z zw zp
        apply Classical.byContradiction
        intro no
        obtain ⟨w,q,_⟩ := (B j h).interior z zw (fun h => no (Or.inl h)) (fun h => no (Or.inr h))
        exact w.property (q.symm ▸ ((fr z).mpr zp))⟩
  have dis : ∀ i (hi : i∈F.sources) j (hj : j∈F.sources), i≠j →
      ∀ z∈(D i hi).walk.support,z∈(D j hj).walk.support → z∈p.support := by
    intro i hi j hj ne z zi zj
    apply Classical.byContradiction
    intro no
    have out (n : Fin (p.length+1)) : z≠f n := fun e =>
      no (e.symm ▸ p.getVert_mem_support n.val)
    exact PosaBridges189.interior_disjoint f (B i hi) (B j hj) ne zi zj
      (out _) (out _) (out _) (out _)
  exact exists_ordered_pair p hp hn F.sources l r D dis F.coverage

#print axioms ordered_pair_of_singleton_connected
end Graffiti189LongestPath.PosaBridgeAdapter
