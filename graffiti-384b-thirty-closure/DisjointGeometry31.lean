import CommonFinish31

namespace Graffiti384b.Disjoint30
open Finset SimpleGraph HighEar
open private ThreeChoice.pair_turan from ThreeGeometry33
open private Repair.nbr_add Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure Board (G : SimpleGraph V) [DecidableRel G.Adj] where
  u : V
  s : V
  du : G.degree u=3
  su : trianglesAt G u=2
  ds : G.degree s=3
  ss : trianglesAt G s=3
  sep : ¬G.Adj u s
  dis : Disjoint (G.neighborFinset u) (G.neighborFinset s)

namespace Board
variable (M : Board G)
def U := G.neighborFinset M.u
def L := G.neighborFinset M.s
def B := M.U∪M.L
def W := (insert M.u (insert M.s M.B))ᶜ
def pins (x y : V) := M.U.erase x∪M.L.erase y

theorem sizes : M.U.card=3 ∧ M.L.card=3 := ⟨(card_neighborFinset_eq_degree ..).trans M.du,(card_neighborFinset_eq_degree ..).trans M.ds⟩
theorem outside (v : V) : v∈M.W ↔ v≠M.u ∧ v≠M.s ∧ v∉M.B := by simp [W,not_or]
theorem bc : M.B.card=6 := by rw [B,card_union_of_disjoint (show Disjoint M.U M.L from M.dis),M.sizes.1,M.sizes.2]
theorem pool_size (n : Fintype.card V=30) : M.W.card=22 := by
  have us : M.u≠M.s := by intro eq; have := M.su; rw [eq,M.ss] at this; contradiction
  have ui : M.u∉M.B := by simp [B,U,L,(show ¬G.Adj M.s M.u from fun h => M.sep h.symm)]
  have si : M.s∉M.B := by simp [B,U,L,M.sep]
  rw [W,card_compl,card_insert_of_not_mem (show M.u∉insert M.s M.B by simp [us,ui]),card_insert_of_not_mem si,M.bc,n]

theorem pin_count (v x y : V) :
    nbr G v (M.pins x y)=nbr G v (M.U.erase x)+nbr G v (M.L.erase y) :=
  Repair.nbr_add G v (M.dis.mono (erase_subset ..) (erase_subset ..))

theorem pin_subset (x y : V) : M.pins x y⊆M.B := union_subset_union (erase_subset ..) (erase_subset ..)
theorem split (x y : V) (xm : x∈M.U) (ym : y∈M.L) : M.B=M.pins x y∪{x,y} := by
  rw [B,pins]; ext z
  simp only [mem_union,mem_singleton,mem_erase,mem_insert]
  by_cases a : z=x <;> by_cases b : z=y <;> simp_all

theorem pool_score {w : V} (wm : w∈M.W)
    (cover : ∀ C,G.IsNClique 5 C → 3≤(C∩M.B).card) :
    let b := nbr G w M.W
    let h := nbr G w M.U+nbr G w M.L
    trianglesAt G w≤(b+h).choose 2 ∧
      (h≤2 → b+h≤10 → trianglesAt G w≤RankTable.cap (b+h) 3) := by
  classical
  let N := G.neighborFinset w
  have wu : ¬G.Adj w M.u := fun e => ((M.outside w).mp wm).2.2 (mem_union_left _ ((G.mem_neighborFinset ..).mpr e.symm))
  have ws : ¬G.Adj w M.s := fun e => ((M.outside w).mp wm).2.2 (mem_union_right _ ((G.mem_neighborFinset ..).mpr e.symm))
  have wb : Disjoint M.W M.B := disjoint_left.mpr (fun z zm => ((M.outside z).mp zm).2.2)
  have eq : (M.W∪M.B).filter (G.Adj w)=N := by
    ext z; simp only [N,mem_filter,mem_neighborFinset]
    constructor
    · exact And.right
    · intro wz
      by_cases zb : z∈M.B
      · exact ⟨mem_union_right _ zb,wz⟩
      · exact ⟨mem_union_left _ ((M.outside z).mpr ⟨fun h => wu (h ▸ wz),fun h => ws (h ▸ wz),zb⟩),wz⟩
  have sum : nbr G w (M.W∪M.B)=G.degree w := (congrArg card eq).trans (card_neighborFinset_eq_degree ..)
  have bs : nbr G w M.B=nbr G w M.U+nbr G w M.L := Repair.nbr_add G w M.dis
  rw [Repair.nbr_add G w wb,bs] at sum
  refine ⟨(sum.symm ▸ Repair.triangles_le_choose G w),?_⟩
  intro small dsmall
  have free (Q : Finset V) (sub : Q⊆N) (clique : G.IsNClique (3+1) Q) : False := by
    have five := clique.insert (fun z zm => (G.mem_neighborFinset ..).mp (sub zm))
    have many := cover _ five
    have inc : (insert w Q)∩M.B⊆M.B.filter (G.Adj w) := by
      intro z zm; obtain ⟨zq,zb⟩ := mem_inter.mp zm
      have ne : z≠w := fun h => ((M.outside w).mp wm).2.2 (h ▸ zb)
      exact mem_filter.mpr ⟨zb,(G.mem_neighborFinset ..).mp (sub ((mem_insert.mp zq).resolve_left ne))⟩
    have up : 3≤nbr G w M.B := many.trans (card_le_card inc)
    omega
  have hi := ThreeChoice.pair_turan G N (by decide : 0<3) free
  have ns : N.card=G.degree w := card_neighborFinset_eq_degree ..
  change trianglesAt G w≤_ at hi
  rw [ns,←sum] at hi
  exact hi.trans_eq (RankTable.cap_table ⟨_,by omega⟩ ⟨3,by decide⟩ (by decide))


/-- Removing a cubic center from an anchor's neighborhood deletes exactly
the triangles it shares with that center. -/
theorem side_score {t o x : V} {T O : Finset V}
    (hT : T=G.neighborFinset t) (hO : O=G.neighborFinset o) (toff : ¬G.Adj t o)
    (tx : x∈T) (sep : Disjoint T O) (bcov : T∪O=M.B) (pair : {t,o}=({M.u,M.s}:Finset V)) :
    trianglesAt G x≤nbr G x T+(nbr G x M.W+(nbr G x T+nbr G x O)).choose 2 := by
  classical
  have xt : G.Adj x t := ((G.mem_neighborFinset ..).mp (hT ▸ tx)).symm
  have xo : ¬G.Adj x o := fun e => disjoint_left.mp sep tx (hO ▸ (G.mem_neighborFinset ..).mpr e.symm)
  let D := (G.neighborFinset x).erase t
  have tm : t∈G.neighborFinset x := (G.mem_neighborFinset ..).mpr xt
  have tn : t∉D := Finset.not_mem_erase t (G.neighborFinset x) 
  have eq : G.neighborFinset x=insert t D := (insert_erase tm).symm
  have tscore := HighEar.pairs_insert G (D:=D) tn
  have credits : nbr G t D=nbr G x T := by
    have eqf : D.filter (G.Adj t)=T.filter (G.Adj x) := by
      ext z; simp [D,hT,and_comm,and_left_comm,and_assoc]
      exact fun tz _ => tz.ne.symm
    exact congrArg card eqf
  have wb : Disjoint M.W M.B := disjoint_left.mpr (fun v vm => ((M.outside v).mp vm).2.2)
  have N : D=(M.W∪M.B).filter (G.Adj x) := by
    ext z; constructor
    · intro m
      obtain ⟨zt,zn⟩ := mem_erase.mp m
      have xz := (G.mem_neighborFinset ..).mp zn
      have zo : z≠o := fun e => xo (e ▸ xz)
      have out : z∉({M.u,M.s}:Finset V) := by rw [←pair]; simp [zt,zo]
      have zs : z≠M.u ∧ z≠M.s := by simpa [not_or] using out
      refine mem_filter.mpr ⟨?_,xz⟩
      by_cases b : z∈M.B
      · exact mem_union_right _ b
      · exact mem_union_left _ ((M.outside z).mpr ⟨zs.1,zs.2,b⟩)
    · intro m
      obtain ⟨side,xz⟩ := mem_filter.mp m
      apply mem_erase.mpr; refine ⟨?_,(G.mem_neighborFinset ..).mpr xz⟩
      intro eqz; subst z
      rcases mem_union.mp side with w|b
      · have ts : t∈({M.u,M.s}:Finset V) := pair ▸ mem_insert_self ..
        rcases (show t=M.u ∨ t=M.s by simpa using ts) with e|e
        · exact ((M.outside t).mp w).1 e
        · exact ((M.outside t).mp w).2.1 e
      · rw [←bcov,hT,hO] at b; simp [show ¬G.Adj o t from fun e => toff e.symm] at b
  have ds : D.card=nbr G x M.W+(nbr G x T+nbr G x O) := by
    rw [N]; change nbr G x (M.W∪M.B)=_
    rw [Repair.nbr_add G x wb,←bcov,Repair.nbr_add G x sep]
  have cap := card_le_card (show HighEar.pairs G D⊆D.powersetCard 2 from filter_subset ..)
  rw [card_powersetCard,ds] at cap
  change (HighEar.pairs G (G.neighborFinset x)).card≤_
  rw [eq,tscore,credits]; omega

theorem anchor_score {x : V} (xm : x∈M.B) :
    trianglesAt G x≤2+(nbr G x M.W+5).choose 2 := by
  have sub (S : Finset V) (sm : x∈S) : S.filter (G.Adj x)⊆S.erase x :=
    fun _ h => mem_erase.mpr ⟨(mem_filter.mp h).2.ne.symm,(mem_filter.mp h).1⟩
  have all := card_le_card (sub M.B xm)
  rw [card_erase_of_mem xm,M.bc] at all
  change nbr G x M.B≤6-1 at all
  have counts : nbr G x M.B=nbr G x M.U+nbr G x M.L := Repair.nbr_add G x M.dis
  rcases mem_union.mp xm with um|lm
  · have h := M.side_score (t:=M.u) (o:=M.s) (T:=M.U) (O:=M.L) rfl rfl M.sep um M.dis rfl rfl
    have sz := card_le_card (sub M.U um)
    rw [card_erase_of_mem um,M.sizes.1] at sz
    change nbr G x M.U≤3-1 at sz
    apply h.trans; exact Nat.add_le_add (by omega) (Nat.choose_le_choose 2 (by omega))
  · have h := M.side_score (t:=M.s) (o:=M.u) (T:=M.L) (O:=M.U) rfl rfl
      (fun e => M.sep e.symm) lm M.dis.symm (union_comm ..) (pair_comm ..)
    have sz := card_le_card (sub M.L lm)
    rw [card_erase_of_mem lm,M.sizes.2] at sz
    change nbr G x M.L≤3-1 at sz
    apply h.trans; exact Nat.add_le_add (by omega) (Nat.choose_le_choose 2 (by omega))

end Board
end Graffiti384b.Disjoint30
#print axioms Graffiti384b.Disjoint30.Board.pool_score
#print axioms Graffiti384b.Disjoint30.Board.side_score
