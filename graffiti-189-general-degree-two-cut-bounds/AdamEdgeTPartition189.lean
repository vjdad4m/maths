import AdamEdgeTight189

namespace Graffiti189.AdamEdge
open Finset SimpleGraph SimpleGraph.Walk
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem tight_shore_partition (hc : G.Connected) {a b x z p q : V} (dab : G.dist a b=3)
    (Y : Finset V) (x2 : G.dist b x=2) (z2 : G.dist a z=2)
    (xcross : ∀ w∈Y,G.dist x w=min (1+G.dist a w) (G.dist b x+G.dist b w))
    (zcross : ∀ w∈Y,G.dist z w=min (1+G.dist b w) (G.dist a z+G.dist a w))
    (rgap : ∀ w∈Remote G Y a p,G.dist a w=G.dist b w+3)
    (xp : ∀ w∈Y,w∈E G x ↔ w∈Ports G Y a∪Remote G Y a p)
    (zp : ∀ w∈Y,w∈E G z ↔ w∈Ports G Y b∪Remote G Y b q) :
    Disjoint (Ports G Y a∪Remote G Y a p) (Ports G Y b∪Remote G Y b q) ∧
    Y=(Ports G Y a∪Remote G Y a p) ∪ (Ports G Y b∪Remote G Y b q) ∪ Mid G Y a b ∧
    Disjoint ((Ports G Y a∪Remote G Y a p) ∪ (Ports G Y b∪Remote G Y b q)) (Mid G Y a b) := by
  classical
  let P := Ports G Y a∪Remote G Y a p
  let Q := Ports G Y b∪Remote G Y b q
  let M := Mid G Y a b
  have psub : P⊆Y := union_subset (filter_subset _ _) (filter_subset _ _)
  have qsub : Q⊆Y := union_subset (filter_subset _ _) (filter_subset _ _)
  have metric (w : V) (wy : w∈Y) :
      (w∈P ∨ w∈Q ∨ w∈M) ∧ ¬(w∈P ∧ w∈Q) ∧ ¬((w∈P ∨ w∈Q) ∧ w∈M) := by
    have xx := xcross w wy
    have zz := zcross w wy
    have ab := hc.dist_triangle (u:=a) (v:=b) (w:=w)
    have ba := hc.dist_triangle (u:=b) (v:=a) (w:=w)
    rw [G.dist_comm (u:=b) (v:=a),dab] at ba
    rw [dab] at ab
    have xp' := xp w wy
    have zp' := zp w wy
    change w∈E G x ↔ w∈P at xp'
    change w∈E G z ↔ w∈Q at zp'
    have diagonal : G.dist a w=G.dist b w → G.dist a w%2=0 := by
      intro e
      by_contra ne
      have xEven : w∈E G x := (mem_E G).mpr (by
        rw [x2,Nat.min_def] at xx
        split at xx <;> omega)
      rcases mem_union.mp ((xp w wy).mp xEven) with po|rm
      · have one := SimpleGraph.dist_eq_one_iff_adj.mpr (mem_filter.mp po).2
        have t := hc.dist_triangle (u:=a) (v:=w) (w:=b)
        rw [dab,G.dist_comm (u:=w) (v:=b)] at t
        omega
      · have r := rgap w rm
        omega
    simp only [←xp',←zp',mem_E,M,Mid,mem_filter,wy,true_and]
    rw [x2,Nat.min_def] at xx
    rw [z2,Nat.min_def] at zz
    split at xx <;> split at zz <;> omega
  constructor
  · exact disjoint_left.mpr (fun w hp hq=>(metric w (psub hp)).2.1 ⟨hp,hq⟩)
  constructor
  · apply Subset.antisymm
    · intro w wy
      rcases (metric w wy).1 with wp|wq|wm
      · exact mem_union.mpr (.inl (mem_union.mpr (.inl wp)))
      · exact mem_union.mpr (.inl (mem_union.mpr (.inr wq)))
      · exact mem_union.mpr (.inr wm)
    · exact union_subset (union_subset psub qsub) (filter_subset _ _)
  apply disjoint_left.mpr
  intro w wq wm
  exact (metric w (mem_filter.mp wm).1).2.2 ⟨mem_union.mp wq,wm⟩

theorem cut_sum_cards {a b : V} (ab : a≠b) (X Y : Finset V)
    (aX : a∉X) (bX : b∉X) (aY : a∉Y) (bY : b∉Y) (dis : Disjoint X Y)
    (cover : ∀ w : V,w=a ∨ w=b ∨ w∈X ∨ w∈Y) :
    Fintype.card V=X.card+Y.card+2 := by
  have eq : (univ:Finset V)=insert a (insert b (X∪Y)) := by
    apply Subset.antisymm
    · intro w _
      rcases cover w with rfl|rfl|wx|wy
      · simp
      · simp
      · exact mem_insert.mpr (.inr (mem_insert.mpr (.inr (mem_union.mpr (.inl wx)))))
      · exact mem_insert.mpr (.inr (mem_insert.mpr (.inr (mem_union.mpr (.inr wy)))))
    · exact subset_univ _
  have bn : b∉X∪Y := fun h=>(mem_union.mp h).elim bX bY
  have an : a∉insert b (X∪Y) := fun h=>(mem_insert.mp h).elim ab (fun e=>(mem_union.mp e).elim aX aY)
  have cc := congrArg Finset.card eq
  rw [card_univ,card_insert_of_not_mem an,card_insert_of_not_mem bn,card_union_of_disjoint dis] at cc
  omega

theorem degree_near_universal [DecidableRel G.Adj] {a b x : V} (_hc : G.Connected)
    (_ax : G.Adj a x) (near : G.dist b x=2) (X : Finset V)
    (aX : a∉X) (xX : x∈X)
    (closed : ∀ u∈X,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈X) :
    G.degree x≤X.card := by
  have sub : G.neighborFinset x⊆insert a (X.erase x) := by
    intro w wm
    have xw := (G.mem_neighborFinset x w).mp wm
    rcases closed x xX w xw with wa|wb|wx
    · exact mem_insert.mpr (.inl wa)
    · have h := SimpleGraph.dist_eq_one_iff_adj.mpr (wb ▸ xw.symm)
      omega
    · exact mem_insert.mpr (.inr (mem_erase.mpr ⟨xw.symm.ne,wx⟩))
  have h := card_le_card sub
  rw [SimpleGraph.card_neighborFinset_eq_degree,
    card_insert_of_not_mem (fun h=>aX (mem_erase.mp h).2),card_erase_of_mem xX] at h
  have pos := card_pos.mpr (show X.Nonempty from ⟨x,xX⟩)
  omega

#print axioms tight_shore_partition
end Graffiti189.AdamEdge
