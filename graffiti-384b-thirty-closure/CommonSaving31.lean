import CommonBudget31
import CommonRepair31

namespace Graffiti384b.OneCommon.Board
open Finset SimpleGraph
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (M : Board G)

private theorem coverage_rank (n : Fintype.card V=30) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) :
    ∃ r : V→ℕ,(∀ v∈M.W∪M.U,r v<25 ∧ mark (r v)≤trianglesAt G v) ∧
      (∑ v∈M.W,row (r v))+(∑ v∈M.U,row (r v))+2*153340=7551356 := by
  have sub : M.U⊆M.B := fun _ vm => mem_union_left _ (mem_erase.mp vm).2
  have dis : Disjoint M.W M.U := disjoint_left.mpr (fun v wm um => ((M.outside v).mp wm).2.2 (sub um))
  have size : (M.W∪M.U).card=25 := by rw [card_union_of_disjoint dis,M.pool_size n,M.sizes.1]
  have no (v : V) (vm : v∈M.W∪M.U) : v≠M.u ∧ v≠M.s := by
    rcases mem_union.mp vm with w|u
    · exact ⟨((M.outside v).mp w).1,((M.outside v).mp w).2.1⟩
    · have uv := (G.mem_neighborFinset ..).mp (mem_erase.mp u).2
      exact ⟨uv.ne.symm,fun eq => M.sep (eq ▸ uv)⟩
  have scores (v : V) (vm : v∈M.W∪M.U) : trianglesAt G v=1 ∨ 4≤trianglesAt G v := by
    have unc := no v vm
    have a : trianglesAt G v≠2 := fun h => unc.1 (fi (h.trans M.su.symm))
    have b : trianglesAt G v≠3 := fun h => unc.2 (fi (h.trans M.ss.symm))
    have p := pos v; omega
  obtain ⟨r,valid,budget⟩ := ranks G size fi scores
  rw [sum_union dis] at budget
  exact ⟨r,valid,budget⟩

/-- Four choices of three pins and eight more vertices from a pool of 23
suffice. The bound allows three repairs in at least one of these choices. -/
theorem saving (n : Fintype.card V=30) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (cover : ∀ C,G.IsNClique 5 C → 3≤(C∩M.B).card) :
    gamma G≤14 := by
  classical
  let K := M.W.powersetCard 8
  let bad (x y w : V) := (K.filter (fun k => w∈M.failed x y k)).card
  let add (x y : V) := (K.filter (fun k => x∈M.extra x y k)).card
  have ws := M.pool_size n
  obtain ⟨us,ls⟩ := M.sizes
  obtain ⟨r,valid,budget⟩ := M.coverage_rank n pos fi
  have exterior (w : V) (wm : w∈M.W) : (∑ x∈M.U,∑ y∈M.L,bad x y w)≤row (r w) := by
    obtain ⟨rr,markle⟩ := valid w (mem_union_left _ wm)
    let b := nbr G w M.W
    let f := nbr G w {M.c}
    let i := nbr G w M.U
    let j := nbr G w M.L
    have sub : M.W.filter (G.Adj w)⊆M.W.erase w := fun v vm => mem_erase.mpr ⟨(mem_filter.mp vm).2.ne.symm,(mem_filter.mp vm).1⟩
    have bb := card_le_card sub
    rw [card_erase_of_mem wm,ws] at bb
    change b≤23-1 at bb
    have ff : f≤1 := (card_filter_le ..).trans (card_singleton _).le
    have ii : i≤2 := (card_filter_le ..).trans us.le
    have jj : j≤2 := (card_filter_le ..).trans ls.le
    obtain ⟨plain,cap⟩ := M.pool_score wm cover
    have a := table.1 ⟨r w,rr⟩ ⟨b,by omega⟩ ⟨f,by omega⟩ ⟨i,by omega⟩ ⟨j,by omega⟩
      (markle.trans plain) (fun low small => markle.trans (cap low small))
    apply LE.le.trans ?_ a
    simpa only [bad,K,failed,M.pin_count] using
      four_fibers G us ls ws wm (fun v => nbr G v {M.c})
  have boundary (x : V) (xm : x∈M.U) : (∑ y∈M.L,add x y)≤row (r x)+153340 := by
    obtain ⟨rr,markle⟩ := valid x (mem_union_right _ xm)
    have z := M.extra_fiber ws xm
    change (∑ y∈M.L,add x y)≤_ at z
    apply z.trans
    split_ifs with available
    · have b : nbr G x M.W≤23 := (card_filter_le ..).trans ws.le
      exact table.2.1 ⟨r x,rr⟩ ⟨nbr G x M.W,by omega⟩
        ((markle.trans (Repair.triangles_le_choose G x)).trans (Nat.choose_le_choose 2 available))
    · exact Nat.zero_le _
  have flip (T : Finset V) (F : Finset V → Finset V) (sub : ∀ k∈K,F k⊆T) :
      (∑ k∈K,(F k).card)=∑ w∈T,(K.filter (fun k => w∈F k)).card := by
    calc _ = ∑ k∈K,∑ w∈T,if w∈F k then 1 else 0 := by
            apply sum_congr rfl; intro k km; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub k km)]
         _ = _ := by rw [sum_comm]; simp [sum_boole]
  have extId (x y : V) : (∑ k∈K,(M.failed x y k).card)=∑ w∈M.W,bad x y w :=
    flip M.W (M.failed x y) (fun _ _ => (filter_subset ..).trans sdiff_subset)
  have addId (x y : V) : (∑ k∈K,(M.extra x y k).card)=add x y := by
    simpa [add] using flip {x} (M.extra x y) (fun _ _ => filter_subset ..)
  have swap : (∑ x∈M.U,∑ y∈M.L,∑ w∈M.W,bad x y w)=∑ w∈M.W,∑ x∈M.U,∑ y∈M.L,bad x y w := by
    calc _ = ∑ x∈M.U,∑ w∈M.W,∑ y∈M.L,bad x y w := sum_congr rfl (fun _ _ => sum_comm)
         _ = _ := sum_comm
  by_contra! no
  have lower (x : V) (xm : x∈M.U) (y : V) (ym : y∈M.L) (k : Finset V) (km : k∈K) :
      4≤(M.failed x y k).card+(M.extra x y k).card := by
    have h := M.trial xm ym km; omega
  have necessary := sum_le_sum (s:=M.U) (fun x xm => sum_le_sum (s:=M.L) (fun y ym => sum_le_sum (s:=K) (lower x xm y ym)))
  simp_rw [sum_add_distrib,extId,addId] at necessary
  rw [swap] at necessary
  have kc : K.card=(23:ℕ).choose 8 := by rw [show K=M.W.powersetCard 8 from rfl,card_powersetCard,ws]
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,us,ls,kc] at necessary
  have A := sum_le_sum exterior
  have B := sum_le_sum boundary
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,us] at B
  have strict := table.2.2.2
  omega

end Graffiti384b.OneCommon.Board
#print axioms Graffiti384b.OneCommon.Board.saving
