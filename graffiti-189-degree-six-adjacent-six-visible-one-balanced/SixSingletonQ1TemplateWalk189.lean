import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q1Template
open SimpleGraph SimpleGraph.Walk Finset
open private walk_of_chain from ArticulationClique189

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {n : ℕ}

def Allows (fixed : List (Fin n × Fin n)) (ends : Fin 21 → Option (Fin n × Fin n))
    (requires : List Nat) (u v : Fin n) : Prop :=
  (u,v)∈fixed ∨ (v,u)∈fixed ∨
    ∃ k : Fin 21,k.val∈requires ∧ (ends k=some (u,v) ∨ ends k=some (v,u))

instance (fixed : List (Fin n × Fin n)) (ends : Fin 21 → Option (Fin n × Fin n))
    (requires : List Nat) (u v : Fin n) : Decidable (Allows fixed ends requires u v) := by
  unfold Allows
  infer_instance

theorem lift_template
    (f : Fin n→V) (inj : Function.Injective f)
    (fixed : List (Fin n × Fin n)) (ends : Fin 21 → Option (Fin n × Fin n))
    (required : List Nat) (B : Nat→Bool)
    (base : ∀ u v,(u,v)∈fixed → G.Adj (f u) (f v))
    (edge : ∀ k u v,ends k=some (u,v) → B k.val=true → G.Adj (f u) (f v))
    (truth : ∀ k∈required,B k=true)
    (path : List (Fin n)) (nd : path.Nodup) (coverage : ∀ i,i∈path)
    (adj : path.Chain' (Allows fixed ends required))
    (j : Fin n) (start : path.head?=some j) :
    ∃ t, RouteOn G (univ.image f) (f j) t := by
  classical
  have dir (u v : Fin n) (valid : Allows fixed ends required u v) : G.Adj (f u) (f v) := by
    rcases valid with h|h|⟨k,km,h|h⟩
    · exact base _ _ h
    · exact (base _ _ h).symm
    · exact edge _ _ _ h (truth _ km)
    exact (edge _ _ _ h (truth _ km)).symm
  have ch : (path.map f).Chain' G.Adj := (List.chain'_map f).mpr (adj.imp dir)
  cases path with
  | nil => simp at start
  | cons i tail =>
    have eq : i=j := by simpa using start
    subst i
    obtain ⟨t,w,sp⟩ := walk_of_chain (f j) (tail.map f) ch
    have nodup : (f j :: tail.map f).Nodup := nd.map inj
    refine ⟨t,w,IsPath.mk' (sp.symm ▸ nodup),?_⟩
    intro x
    rw [sp,←List.map_cons,mem_image]
    constructor
    · intro m
      obtain ⟨u,_,e⟩ := List.mem_map.mp m
      exact ⟨u,mem_univ _,e⟩
    rintro ⟨u,_,rfl⟩
    exact List.mem_map_of_mem (coverage u)

end Graffiti189LongestPath.CrossSaturation.ThresholdSix.Q1Template
