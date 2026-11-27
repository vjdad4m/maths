import BoardBudget28
import RankBoard28

namespace Graffiti384b.FiveBoard28.Board
open Finset SimpleGraph
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (M : Board G)

theorem saving (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (cover : ∀ C,G.IsNClique 5 C → 3≤(C∩M.B).card) :
    gamma G≤13 := by
  classical
  let pay := payment G M.W M.U M.L M.u M.s
  obtain ⟨us,ls⟩ := M.sizes
  have ws := M.pool_size n
  have bw : Disjoint M.B M.W := disjoint_left.mpr (fun z zi zw => ((M.outside z).mp zw).2.2 zi)
  have uw := bw.mono_left (show M.U⊆M.B from subset_union_left)
  have lw := bw.mono_left (show M.L⊆M.B from subset_union_right)
  have uo : M.u∉M.W := fun m => ((M.outside _).mp m).1 rfl
  have so : M.s∉M.W := fun m => ((M.outside _).mp m).2.1 rfl
  have uL : M.u∉M.L := fun m => M.sep ((G.mem_neighborFinset ..).mp m).symm
  have sU : M.s∉M.U := fun m => M.sep ((G.mem_neighborFinset ..).mp m)
  obtain ⟨r,valid,budget⟩ := M.coverage_rank n pos fi
  have ext (w : V) (wm : w∈M.W) : pay w≤row (r w) := by
    have off := ((M.outside _).mp wm).2.2
    have noU : ¬G.Adj w M.u := fun h => off (mem_union_left _ ((G.mem_neighborFinset ..).mpr h.symm))
    have noL : ¬G.Adj w M.s := fun h => off (mem_union_right _ ((G.mem_neighborFinset ..).mpr h.symm))
    have cost := exterior_cost G ws us ls M.dis uw lw uo so wm noU noL
    obtain ⟨rr,lb⟩ := valid w (mem_union_left _ wm)
    obtain ⟨sc,cap⟩ := M.pool_score wm cover
    have d := (HighSquare28.pool_degree G wm).trans_le ws.le
    have i : nbr G w M.U≤3 := (card_filter_le ..).trans us.le
    have j : nbr G w M.L≤3 := (card_filter_le ..).trans ls.le
    exact cost.trans (table.1 ⟨r w,rr⟩ ⟨_,d⟩ ⟨_,Nat.lt_succ_of_le i⟩ ⟨_,Nat.lt_succ_of_le j⟩ (lb.trans sc)
      (fun few small => lb.trans (cap few small)))
  have side {T O : Finset V} {t o z : V} (tN : T=G.neighborFinset t) (oN : O=G.neighborFinset o)
      (ts : T.card=3) (os : O.card=3) (sep : Disjoint T O) (tw : Disjoint T M.W) (ow : Disjoint O M.W)
      (tW : t∉M.W) (oW : o∉M.W) (tO : t∉O) (no : ¬G.Adj t o) (zT : z∈T)
      (low : 1≤nbr G z T) (bcov : T∪O=M.B) (pair : {t,o}=({M.u,M.s}:Finset V)) :
      payment G M.W T O t o z+95238≤row (r z) := by
    have zb : z∈M.B := bcov ▸ mem_union_left O zT
    obtain ⟨rr,lb⟩ := valid z (mem_union_right _ zb)
    have sc := M.side_score tN oN no zT sep bcov pair
    have wt := ((G.mem_neighborFinset ..).mp (tN ▸ zT)).symm
    have excess := boundary_cost G ws os sep tw ow tW oW tO wt zT low
    have d : nbr G z M.W≤20 := (card_filter_le ..).trans ws.le
    have j : nbr G z O≤3 := (card_filter_le ..).trans os.le
    have sub : T.filter (G.Adj z)⊆T.erase z := fun _ h => mem_erase.mpr ⟨(mem_filter.mp h).2.ne.symm,(mem_filter.mp h).1⟩
    have i := card_le_card sub
    rw [card_erase_of_mem zT,ts] at i
    change nbr G z T≤2 at i
    exact (Nat.add_le_add_right excess _).trans (table.2.1 ⟨r z,rr⟩ ⟨_,Nat.lt_succ_of_le d⟩ ⟨_,Nat.lt_succ_of_le i⟩
      ⟨_,Nat.lt_succ_of_le j⟩ low (lb.trans sc))
  have anchors (w : V) (wm : w∈M.B) : pay w+95238≤row (r w) := by
    rcases mem_union.mp wm with wU|wL
    · have low := (M.one_U wU).trans (by apply Repair.nbr_mono G w (erase_subset ..))
      exact side (t:=M.u) (o:=M.s) (T:=M.U) (O:=M.L) rfl rfl us ls M.dis uw lw uo so uL M.sep wU low rfl rfl
    · have low : 1≤nbr G w M.L := by
        obtain ⟨z,zm,ne⟩ := exists_ne_of_one_lt_card (show 1<M.L.card by omega) w
        exact card_pos.mpr ⟨z,mem_filter.mpr ⟨zm,EarAnchor.full_neighbors G M.ds M.ss
          ((G.mem_neighborFinset ..).mp wL) ((G.mem_neighborFinset ..).mp zm) ne.symm⟩⟩
      change payment G M.W M.U M.L M.u M.s w+95238≤_
      rw [payment_swap G M.W M.U M.L M.u M.s]
      exact side (t:=M.s) (o:=M.u) (T:=M.L) (O:=M.U) rfl rfl ls us M.dis.symm lw uw so uo sU
        (fun h => M.sep h.symm) wL low (union_comm ..) (pair_comm ..)
  have totalU := sum_le_sum ext
  have totalB := sum_le_sum anchors
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,M.bc] at totalB
  have cu : pay M.u=0 := center_zero G M.W M.L M.s us
  have cv : pay M.s=0 := (payment_swap G M.W M.U M.L M.u M.s M.s).trans (center_zero G M.W M.U M.u ls)
  have whole : (∑ z∈M.W,pay z)+(∑ z∈M.B,pay z)=∑ z,pay z := by
    rw [←sum_union bw.symm]
    apply sum_subset (subset_univ _); intro z _ zm
    by_cases zu : z=M.u
    · exact zu ▸ cu
    by_cases zv : z=M.s
    · exact zv ▸ cv
    have zb : z∉M.B := fun h => zm (mem_union_right _ h)
    exact (zm (mem_union_left _ ((M.outside z).mpr ⟨zu,zv,zb⟩))).elim
  apply Nat.le_of_not_gt; intro large
  have needed := lower_mass G M.u M.s ws us ls large
  change 10814040≤∑ z,pay z at needed
  omega

end Graffiti384b.FiveBoard28.Board
#print axioms Graffiti384b.FiveBoard28.Board.saving
