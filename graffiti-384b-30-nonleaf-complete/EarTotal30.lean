import EarFiber30
namespace Graffiti384b.EarMix.Layout
open Finset SimpleGraph Thin28 HighSquare28
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (M : Layout G)

theorem lower (large : 16≤gamma G) : 14447790+(∑v,M.total (gain G M.W) 9 8 v)≤∑v,M.total (hit G M.W) 9 8 v := by
  have single (N : Layout G) : 4815930+(∑ v,N.trial (gain G N.W) 9 8 v)≤∑ v,N.trial (hit G N.W) 9 8 v := by
    have p := card_union_le N.A ({N.f,N.g}:Finset V)
    have q := card_union_le (N.B∪N.C) ({N.e}:Finset V)
    rw [card_pair N.fg,N.asz] at p
    rw [card_singleton,card_union_of_disjoint N.bc,N.bsz,N.csz] at q
    change N.P.card≤2+2 at p
    change N.Q.card≤2+2+1 at q
    have a := mass G N.W N.P 9 (N.inj.mono N.wh) (by omega)
    have b := mass G N.W N.Q 8 (N.inj.mono N.wh) (by omega)
    rw [N.ws] at a b
    change 881790+(∑v,gain G N.W N.P 9 v)≤_ at a
    change 610470+(∑v,gain G N.W N.Q 8 v)≤_ at b
    simp only [trial,sum_add_distrib,←mul_sum]; omega
  have a := single M
  have b := single M.rot
  have c := single M.rot.rot
  change 4815930+(∑v,M.rot.trial (gain G M.W) 9 8 v)≤∑v,M.rot.trial (hit G M.W) 9 8 v at b
  change 4815930+(∑v,M.rot.rot.trial (gain G M.W) 9 8 v)≤∑v,M.rot.rot.trial (hit G M.W) 9 8 v at c
  simp only [total,sum_add_distrib]; omega

private theorem ear_trial {v : V} (low : v=M.e ∨ v=M.f ∨ v=M.g) :
    M.trial (hit G M.W) 9 8 v=0 := by
  have guarded {z : V} {P : Finset V} {k : ℕ} (sub : G.neighborFinset z⊆P) (size : (G.neighborFinset z).card=2) :
      hit G M.W P k z=0 := by
    apply supported_zero G
    have le := card_le_card (show G.neighborFinset z⊆P.filter (G.Adj z) from
      fun w wm => mem_filter.mpr ⟨sub wm,(G.mem_neighborFinset ..).mp wm⟩)
    simpa only [size,nbr] using le
  rcases low with rfl|rfl|rfl
  · have p := guarded (P:=M.P) (k:=9) (z:=M.e) (M.ea.symm ▸ subset_union_left) (M.ea ▸ M.asz)
    have q := kept G (W:=M.W) (b:=8) (show M.e∈M.Q from mem_union_right _ (mem_singleton_self _))
    simp [trial,p,q]
  · have p := kept G (W:=M.W) (b:=9) (show M.f∈M.P from mem_union_right _ (mem_insert_self ..))
    have q := guarded (P:=M.Q) (k:=8) (z:=M.f) (M.fb.symm ▸ (subset_union_left.trans subset_union_left)) (M.fb ▸ M.bsz)
    simp [trial,p,q]
  · have p := kept G (W:=M.W) (b:=9) (show M.g∈M.P from mem_union_right _ (mem_insert_of_mem (mem_singleton_self _)))
    have q := guarded (P:=M.Q) (k:=8) (z:=M.g) (M.gc.symm ▸ (subset_union_right.trans subset_union_left)) (M.gc ▸ M.csz)
    simp [trial,p,q]

theorem ear_zero {v : V} (out : v∉M.H) : M.total (hit G M.W) 9 8 v=0 := by
  have eq (N : Layout G) (off : v∉N.H) : N.trial (hit G N.W) 9 8 v=0 := by
    have h := mem_univ v; rw [N.full] at h
    exact N.ear_trial (by simpa [off] using h)
  have a := eq M out
  have b := eq M.rot out
  have c := eq M.rot.rot out
  change M.rot.trial (hit G M.W) 9 8 v=0 at b
  change M.rot.rot.trial (hit G M.W) 9 8 v=0 at c
  simp [total,a,b,c]
end Graffiti384b.EarMix.Layout
#print axioms Graffiti384b.EarMix.Layout.lower
#print axioms Graffiti384b.EarMix.Layout.ear_zero
