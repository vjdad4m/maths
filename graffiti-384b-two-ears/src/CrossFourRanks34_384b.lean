import CrossFourTable34_384b

namespace Graffiti384b.CrossFour34
open Finset SimpleGraph CliqueChoice LowSample
open private LowSample.delta from LowSample384b
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Count both permanently retained anchors by upper bounds on their triangle
counts, including when their degrees exceed the threshold. -/
theorem ranks {p : Finset V} (ch : Choice G p Boundary.levels) {w b : V} (wb : w≠b)
    (pins : ({w,b} : Finset V)⊆high G\p) {A B : ℕ} (aw : trianglesAt G w≤A) (ab : trianglesAt G b≤B)
    (h : (high G).card=31) (t : (types G).card=33) (m : ℕ) :
    let s := (high G\p)\{w,b}
    let f := p.image (G.degree ·)
    let flag := decide (3∈f)
    charge m (fun j => (s.filter (fun v => G.degree v≤j)).card) +
      rank m flag A+rank m flag B ≤ charge m (SharedRanks34.limit f) := by
  classical
  let s := (high G\p)\{w,b}
  let f := p.image (G.degree ·)
  let flag := decide (3∈f)
  have wm := pins (mem_insert_self ..)
  have bm := pins (mem_insert_of_mem (mem_singleton_self b))
  obtain ⟨inj,pos,_,_⟩ := Repair.maximal_diversity G (by omega)
  have each (j : ℕ) (_ : j∈range 9) :
      rate m j*(s.filter (fun v => G.degree v≤j)).card+
      (if A<TwoEdge34.ceiling flag j then rate m j else 0)+
      (if B<TwoEdge34.ceiling flag j then rate m j else 0) ≤
      rate m j*SharedRanks34.limit f j := by
    by_cases big : 3≤j
    · let cap := slots f j Boundary.levels
      let T := (high G).filter (fun v => trianglesAt G v<cap)
      let L := s.filter (fun v => G.degree v≤j)
      let P := p.filter (fun v => G.degree v≤j)
      let E := (({w,b} : Finset V).filter (fun x => if x=w then A<TwoEdge34.ceiling flag j else B<TwoEdge34.ceiling flag j))
      have ceil : TwoEdge34.ceiling flag j≤cap := by
        simp only [cap,slots,TwoEdge34.ceiling,flag]
        split <;> split <;> simp_all
      have below (v : V) (dv : G.degree v≤j) : trianglesAt G v<cap := by
        have base := Repair.triangles_le_choose G v
        have le := base.trans (Nat.choose_le_choose 2 dv)
        unfold cap slots
        split
        · rename_i absent
          by_cases eq : G.degree v=j
          · have ne : trianglesAt G v≠(G.degree v).choose 2 := fun sat => absent.2 (eq ▸ ch.covers v (eq ▸ absent.1) sat)
            rw [eq] at base ne; omega
          · have rec := Nat.choose_succ_succ' (j-1) 1
            rw [show j-1+1=j by omega,Nat.choose_one_right] at rec
            have pred := base.trans (Nat.choose_le_choose 2 (show G.degree v≤j-1 by omega))
            change j.choose 2=_+_ at rec
            norm_num at rec
            omega
        · omega
      have inL : L⊆T := fun _ v => mem_filter.mpr ⟨(mem_sdiff.mp (mem_sdiff.mp (mem_filter.mp v).1).1).1,below _ (mem_filter.mp v).2⟩
      have inP : P⊆T := fun _ v => mem_filter.mpr ⟨ch.high_sub (mem_filter.mp v).1,below _ (mem_filter.mp v).2⟩
      have inE : E⊆T := by
        intro x xm
        obtain ⟨xe,small⟩ := mem_filter.mp xm
        have hi := (mem_sdiff.mp (pins xe)).1
        simp only [mem_insert,mem_singleton] at xe
        rcases xe with rfl|rfl
        · simp only [if_pos rfl] at small
          exact mem_filter.mpr ⟨hi,lt_of_le_of_lt aw (small.trans_le ceil)⟩
        · simp only [if_neg wb.symm] at small
          exact mem_filter.mpr ⟨hi,lt_of_le_of_lt ab (small.trans_le ceil)⟩
      have lp : Disjoint L P := disjoint_left.mpr (fun _ l p0 =>
        (mem_sdiff.mp (mem_sdiff.mp (mem_filter.mp l).1).1).2 (mem_filter.mp p0).1)
      have le : Disjoint L E := disjoint_left.mpr (fun _ l e0 =>
        (mem_sdiff.mp (mem_filter.mp l).1).2 (mem_filter.mp e0).1)
      have pe : Disjoint P E := disjoint_left.mpr (fun _ p0 e0 =>
        (mem_sdiff.mp (pins (mem_filter.mp e0).1)).2 (mem_filter.mp p0).1)
      have subset := card_le_card (union_subset (union_subset inL inP) inE)
      rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨le,pe⟩),card_union_of_disjoint lp] at subset
      have ts : T.image (trianglesAt G)⊆Ico 2 cap := by
        intro k km
        obtain ⟨v,vm,rfl⟩ := mem_image.mp km
        exact mem_Ico.mpr ⟨pos v (mem_filter.mp vm).1,(mem_filter.mp vm).2⟩
      have count := card_le_card ts
      rw [card_image_of_injOn (inj.mono (show (T : Set V)⊆high G from filter_subset _ _)),Nat.card_Ico] at count
      have cc : P.card=(f.filter (·≤j)).card := by
        have eq : P.image (G.degree ·)=f.filter (·≤j) := by ext d; simp [P,f]; aesop
        rw [←eq,card_image_of_injOn (ch.unique.mono (show (P : Set V)⊆p from filter_subset _ _))]
      have ec : E.card=(if A<TwoEdge34.ceiling flag j then 1 else 0)+(if B<TwoEdge34.ceiling flag j then 1 else 0) := by
        by_cases a : A<TwoEdge34.ceiling flag j <;> by_cases b' : B<TwoEdge34.ceiling flag j <;> simp [E,filter_insert,filter_singleton,a,b',wb,wb.symm]
      have num : L.card+(if A<TwoEdge34.ceiling flag j then 1 else 0)+(if B<TwoEdge34.ceiling flag j then 1 else 0)≤SharedRanks34.limit f j := by
        rw [ec,cc] at subset
        change T.card≤slots f j Boundary.levels-2 at count
        unfold SharedRanks34.limit
        omega
      have mul := Nat.mul_le_mul_left (rate m j) num
      rw [Nat.mul_add,Nat.mul_add] at mul
      by_cases a : A<TwoEdge34.ceiling flag j <;> by_cases b' : B<TwoEdge34.ceiling flag j <;> simpa [L,a,b'] using mul
    · simp [rate,LowSample.delta,big]
  have total := sum_le_sum each
  simp only [sum_add_distrib] at total
  dsimp only
  unfold charge rank
  simpa only [Nat.add_assoc] using Nat.add_le_add_left total (m*base m)

end Graffiti384b.CrossFour34
#print axioms Graffiti384b.CrossFour34.ranks


