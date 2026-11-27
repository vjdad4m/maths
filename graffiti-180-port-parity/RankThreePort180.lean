import PairDistance180
import RankTwoAssembly180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 RootEar
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For a degree-two root whose deletion has deficit at most two, the
old local inequality is automatic. For ports at old distance at most
two, only one directed sector must pay for the transfer. -/
theorem rank_two_deletion (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (low : Fintype.card V≤bipartiteNum G+2) (x y : V) (close : G.dist x y≤2)
    (A : Finset V) (ind : Indep G A) (a p : Bool) :
    let H := ear G {x,y}
    let Q := parity G x (!p)
    let S := sector G x y
    let C := parity H (.inr ()) p
    bipartiteNum G+(S\Q).card+(a || !p).toNat+(if x∈A∩Q then 1 else 0)
      ≤bipartiteNum H+((S∩Q)∩A).card →
    1+(lift A a).card+C.card≤weightedLeaves H (eligible (lift A a) C (.inr ()))+bipartiteNum H := by
  classical
  intro H Q S C paid
  let N : Finset V := {x,y}
  have nz : N.Nonempty := insert_nonempty _ _
  have ch := pair_changes G gc x y nz close (!p)
  apply transfer_at_port G gc hn N nz A a p x (mem_insert_self ..)
  · exact (family_of_rank G gc (by omega) low).rooted x (!p) A ind
  · rw [ch.1,ch.2]; exact paid

/-- On the actual rank-three branch, removing a vertex to a graph of
deficit at most two preserves bipartite order. Failure at an even root
forces the following inequality in both orientations of a nearby pair. -/
theorem rank_three_even_obstruction (G : SimpleGraph V) (gc : G.Connected)
    (hn : 2<Fintype.card V) (low : Fintype.card V≤bipartiteNum G+2)
    (x y : V) (A : Finset V) (ind : Indep G A) (a : Bool) :
    let H := ear G {x,y}
    let C := parity H (.inr ()) false
    Fintype.card (V⊕Unit)=bipartiteNum H+3 →
    weightedLeaves H (eligible (lift A a) C (.inr ()) )+bipartiteNum H<1+(lift A a).card+C.card →
    bipartiteNum H=bipartiteNum G ∧
    ∀ u v, ({u,v}:Finset V)={x,y} → G.dist u v≤2 →
      ((sector G u v∩parity G u true)∩A).card≤(sector G u v\parity G u true).card := by
  classical
  intro H C rk fail
  have upper : bipartiteNum G≤bipartiteNum H := rank_mono G {x,y}
  rw [Fintype.card_sum,Fintype.card_unit] at rk
  have eq : bipartiteNum H=bipartiteNum G := by omega
  refine ⟨eq,?_⟩
  intro u v pair uv
  by_contra! short
  have self : u∉parity G u true := by simp [mem_parity,dist_self]
  have no : u∉A∩parity G u true := fun h => self (mem_inter.mp h).2
  have get := rank_two_deletion G gc hn low u v uv A ind a false
  rw [pair] at get
  change _ → 1+(lift A a).card+C.card≤weightedLeaves H (eligible _ C _)+bipartiteNum H at get
  apply (Nat.not_le.mpr fail) (get ?_)
  simp only [Bool.not_false,Bool.or_true,Bool.toNat_true,if_neg no,add_zero]
  rw [eq]; omega

#print axioms rank_two_deletion
#print axioms rank_three_even_obstruction
end Minimal180.PortParity
