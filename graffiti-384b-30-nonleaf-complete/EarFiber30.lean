import EarLayout30
namespace Graffiti384b.EarMix.Layout
open Finset SimpleGraph Thin28 HighSquare28
open private Repair.nbr_add from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (M : Layout G)

private theorem contacts {w : V} (wm : w∈M.W) :
    nbr G w M.P=nbr G w M.A ∧ nbr G w M.Q=nbr G w M.B+nbr G w M.C := by
  have nf : ¬G.Adj w M.f := M.rot.nowhere wm
  have ng : ¬G.Adj w M.g := M.rot.rot.nowhere wm
  have ne := M.nowhere wm
  have right := Repair.nbr_add G w M.bc
  constructor
  · simp [P,nbr,filter_union,filter_insert,filter_singleton,nf,ng]
  · simpa [Q,nbr,filter_union,filter_singleton,ne] using right

theorem outside_cost {w : V} (wm : w∈M.W) (k l : ℕ) :
    M.total (hit G M.W) k l w ≤ exterior (nbr G w M.W) (nbr G w M.A) (nbr G w M.B) (nbr G w M.C) k l := by
  have single (N : Layout G) (m : w∈N.W) :
      N.trial (hit G N.W) k l w≤2*bill 21 k (nbr G w N.W) (nbr G w N.A)+
        5*bill 21 l (nbr G w N.W) (nbr G w N.B+nbr G w N.C) := by
    obtain ⟨p,q⟩ := N.contacts m
    have first := bill_bound G N.across.1 m k
    have last := bill_bound G N.across.2 m l
    rw [N.ws,p] at first
    rw [N.ws,q] at last
    unfold trial; omega
  have a := single M wm
  have b := single M.rot wm
  have c := single M.rot.rot wm
  dsimp only [rot] at b c
  unfold total exterior
  change _≤_ at a
  dsimp only [rot]; omega

theorem activation {w : V} (wm : w∈M.W) (sat : trianglesAt G w=(G.degree w).choose 2) :
    allSelected≤M.total (gain G M.W) 9 8 w+M.total (hit G M.W) 8 7 w := by
  have single (N : Layout G) (m : w∈N.W) :
      2*(20:ℕ).choose 8+5*(20:ℕ).choose 7≤N.trial (gain G N.W) 9 8 w+N.trial (hit G N.W) 8 7 w := by
    have a := active_fiber G m (fun h => disjoint_left.mp N.across.1 h m) sat 8
    have b := active_fiber G m (fun h => disjoint_left.mp N.across.2 h m) sat 7
    rw [N.ws] at a b
    change (20:ℕ).choose 8≤gain G N.W N.P 9 w+hit G N.W N.P 8 w at a
    change (20:ℕ).choose 7≤gain G N.W N.Q 8 w+hit G N.W N.Q 7 w at b
    unfold trial; omega
  have a := single M wm
  have b := single M.rot wm
  have c := single M.rot.rot wm
  change _≤M.rot.trial (gain G M.W) 9 8 w+M.rot.trial (hit G M.W) 8 7 w at b
  change _≤M.rot.rot.trial (gain G M.W) 9 8 w+M.rot.rot.trial (hit G M.W) 8 7 w at c
  unfold total allSelected; omega

private theorem paid {W P T : Finset V} {w e : V} (sz : W.card=21) (off : w∉W) (eo : e∉W)
    (we : G.Adj w e) (ep : e∈P) (tp : T⊆P) (et : e∉T) (k : ℕ) :
    hit G W P k w≤oneBill k (nbr G w W) (nbr G w T) := by
  by_cases nh : nbr G w T=0
  · simpa [oneBill,nh,sz,off] using credited G (b:=k) ep eo we
  · obtain ⟨x,xm⟩ := card_pos.mp (Nat.pos_of_ne_zero nh)
    obtain ⟨xt,wx⟩ := mem_filter.mp xm
    have free := covered G (W:=W) (b:=k) (fun h : e=x => et (h ▸ xt)) we wx ep (tp xt)
    simp [free,oneBill,nh]

theorem anchor_cost {w : V} (wm : w∈M.A) : M.total (hit G M.W) 9 8 w≤
    side (nbr G w M.W) (nbr G w M.B) (nbr G w M.C) := by
  have out : w∉M.W := fun m => disjoint_left.mp M.wa m wm
  have ew : M.e∉M.W := fun m => M.ew (M.wh m)
  have we := (M.edge_facts wm).1
  have ep : M.e∈M.Q := mem_union_right _ (mem_singleton_self _)
  have bp : M.e∈M.rot.P := mem_union_right _ (mem_insert_of_mem (mem_singleton_self _))
  have cp : M.e∈M.rot.rot.P := mem_union_right _ (mem_insert_self ..)
  have eb : M.e∉M.B := fun m => M.ew (M.rot.ah m)
  have ec : M.e∉M.C := fun m => M.ew (M.rot.rot.ah m)
  have b := paid M.ws out ew we bp (show M.B⊆M.rot.P from subset_union_left) eb 9
  have c := paid M.ws out ew we cp (show M.C⊆M.rot.rot.P from subset_union_left) ec 9
  have s := paid M.ws out ew we ep (show M.B∪M.C⊆M.Q from subset_union_left) (fun m => (mem_union.mp m).elim eb ec) 8
  rw [Repair.nbr_add G w M.bc] at s
  have az := kept G (W:=M.W) (b:=9) (show w∈M.P from mem_union_left _ wm)
  have bz := kept G (W:=M.W) (b:=8) (show w∈M.rot.Q from mem_union_left _ (mem_union_right _ wm))
  have cz := kept G (W:=M.W) (b:=8) (show w∈M.rot.rot.Q from mem_union_left _ (mem_union_left _ wm))
  unfold total trial side
  omega
end Graffiti384b.EarMix.Layout
#print axioms Graffiti384b.EarMix.Layout.outside_cost
#print axioms Graffiti384b.EarMix.Layout.activation
#print axioms Graffiti384b.EarMix.Layout.anchor_cost
