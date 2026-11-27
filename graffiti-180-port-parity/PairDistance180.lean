import ParityBudget180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem near_pair (G : SimpleGraph V) (x y v : V) (nz : ({x,y}:Finset V).Nonempty) :
    near G {x,y} nz v=min (G.dist v x) (G.dist v y) := by
  have a : near G {x,y} nz v≤G.dist v x := inf'_le _ (mem_insert_self ..)
  have b : near G {x,y} nz v≤G.dist v y := inf'_le _ (mem_insert_of_mem (mem_singleton_self _))
  obtain ⟨w,hw,eq⟩ := near_attained G {x,y} nz v
  rcases mem_insert.mp hw with h|h
  · subst w; omega
  · obtain rfl := mem_singleton.mp h; omega

/-- For two attachment neighbors at old distance at most two, the
nearest-port parity differs from the parity at x exactly on vertices
one step closer to y than to x. -/
theorem pair_flip (G : SimpleGraph V) (gc : G.Connected) (x y v : V)
    (nz : ({x,y}:Finset V).Nonempty) (close : G.dist x y≤2) (m : Bool) :
    (v∈nearParity G {x,y} nz m ↔ v∈parity G x m) ↔ G.dist v x≠G.dist v y+1 := by
  classical
  have bound := gc.dist_triangle (u:=v) (v:=y) (w:=x)
  rw [dist_comm (u:=y) (v:=x)] at bound
  simp only [nearParity,mem_filter,mem_univ,true_and,near_pair,mem_parity]
  cases m <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega

noncomputable def sector (G : SimpleGraph V) (x y : V) : Finset V := by
  classical exact univ.filter (fun v => G.dist v x=G.dist v y+1)

/-- The cost and the credit in the transfer inequality come from
opposite parity classes of one directed distance sector. -/
theorem pair_changes (G : SimpleGraph V) (gc : G.Connected) (x y : V)
    (nz : ({x,y}:Finset V).Nonempty) (close : G.dist x y≤2) (m : Bool) :
    let P := nearParity G {x,y} nz m
    let Q := parity G x m
    P\Q=sector G x y\Q ∧ Q\P=sector G x y∩Q := by
  classical
  intro P Q
  have flip (v : V) : (v∈P ↔ v∈Q) ↔ v∉sector G x y := by
    simpa only [sector,mem_filter,mem_univ,true_and] using pair_flip G gc x y v nz close m
  constructor <;> ext v <;> specialize flip v <;> simp only [mem_sdiff,mem_inter] <;> tauto

#print axioms near_pair
#print axioms pair_flip
#print axioms pair_changes
end Minimal180.PortParity
