import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Card

namespace Graffiti189.AdamEdge
open Finset SimpleGraph
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def E (a : V) : Finset V := by
  classical exact univ.filter (fun w => G.dist a w % 2 = 0)

noncomputable def OO (a p : V) : Finset V := by
  classical exact univ.filter (fun w => G.dist a w % 2 = 1 ∧ G.dist p w % 2 = 1)

@[simp] theorem mem_E {a w : V} : w∈E G a ↔ G.dist a w % 2 = 0 := by
  classical simp [E]
@[simp] theorem mem_OO {a p w : V} : w∈OO G a p ↔ G.dist a w % 2 = 1 ∧ G.dist p w % 2 = 1 := by
  classical simp [OO]

theorem adjacent_even_balance (a p : V) :
    Fintype.card V + (E G a ∩ E G p).card =
      (E G a).card + (E G p).card + (OO G a p).card := by
  have comp : OO G a p = univ \ (E G a ∪ E G p) := by
    ext w
    simp only [mem_OO, mem_sdiff, mem_univ, true_and, mem_union, mem_E]
    omega
  have h := card_sdiff_add_card_eq_card (subset_univ (E G a ∪ E G p))
  have h' := card_union_add_card_inter (E G a) (E G p)
  rw [←comp,card_univ] at h
  omega

noncomputable def XOdd (X : Finset V) (a b p : V) : Finset V := by
  classical exact X.filter (fun w => G.dist a w = G.dist b w + G.dist b p ∧ G.dist a w % 2 = 1)
noncomputable def BFlag (b : V) (P : Prop) : Finset V := by
  classical exact ({b}:Finset V).filter (fun _ => P)
noncomputable def Common (Y : Finset V) (a p : V) : Finset V := by
  classical exact Y.filter (fun w => G.Adj a w ∧ G.Adj p w)
noncomputable def Remote (Y : Finset V) (a p : V) : Finset V := by
  classical exact Y.filter (fun w => G.dist a w = G.dist p w ∧ G.dist a w % 2 = 1 ∧ 3 ≤ G.dist a w)
noncomputable def Ports (Y : Finset V) (a : V) : Finset V := by
  classical exact Y.filter (G.Adj a)
noncomputable def Missing (Y : Finset V) (a p : V) : Finset V := by
  classical exact (Ports G Y a).filter (fun w => w ≠ p ∧ ¬G.Adj p w)
noncomputable def Base (Y : Finset V) (a b x : V) : Finset V :=
  insert x (BFlag b (G.dist x b % 2 = 0) ∪ Ports G Y a)
noncomputable def Extra (Y : Finset V) (a b x p : V) : Finset V :=
  E G x \ (Base G Y a b x ∪ Remote G Y a p)

@[simp] theorem mem_flag {w b : V} {P : Prop} : w∈BFlag b P ↔ w=b ∧ P := by
  classical
  by_cases h : P <;> simp [BFlag,h]

theorem card_flag (b : V) (P : Prop) [Decidable P] : (BFlag b P).card = if P then 1 else 0 := by
  classical
  by_cases h : P <;> simp [BFlag,h]

variable {G}
theorem oo_partition (hc : G.Connected) {a b p : V} (ap : G.Adj a p) (dab : G.dist a b = 3)
    (X Y : Finset V) (bX : b∉X) (bY : b∉Y)
    (dis : Disjoint X Y) (cover : ∀ w : V,w=a ∨ w=b ∨ w∈X ∨ w∈Y)
    (cross : ∀ w∈X,G.dist p w = min (1 + G.dist a w) (G.dist b p + G.dist b w)) :
    (OO G a p).card = (XOdd G X a b p).card + (BFlag b (G.dist b p = 3)).card +
      (Common G Y a p).card + (Remote G Y a p).card := by
  classical
  let X₀ := XOdd G X a b p
  let B := BFlag b (G.dist b p = 3)
  let C := Common G Y a p
  let R := Remote G Y a p
  have ap1 := SimpleGraph.dist_eq_one_iff_adj.mpr ap
  have equi {w : V} (h : w∈OO G a p) : G.dist a w = G.dist p w := by
    have l := hc.dist_triangle (u:=a) (v:=p) (w:=w)
    have r := hc.dist_triangle (u:=p) (v:=a) (w:=w)
    rw [ap1] at l
    rw [G.dist_comm (u:=p) (v:=a),ap1] at r
    rw [mem_OO] at h
    omega
  have eq : OO G a p = (X₀∪B)∪(C∪R) := by
    ext w
    constructor
    · intro wm
      have odd := ((mem_OO G).mp wm).1
      have same := equi wm
      rcases cover w with rfl|rfl|wx|wy
      · simp [SimpleGraph.dist_self] at odd
      · exact mem_union.mpr (.inl (mem_union.mpr (.inr (mem_flag.mpr ⟨rfl,by
          rw [G.dist_comm (u:=p)] at same; omega⟩))))
      · have c := cross w wx
        simp only [Nat.min_def] at c
        have e : G.dist a w = G.dist b w + G.dist b p := by split at c <;> omega
        exact mem_union.mpr (.inl (mem_union.mpr (.inl (mem_filter.mpr ⟨wx,e,odd⟩))))
      · apply mem_union.mpr
        apply Or.inr
        by_cases h : G.dist a w = 1
        · exact mem_union.mpr (.inl (mem_filter.mpr ⟨wy,SimpleGraph.dist_eq_one_iff_adj.mp h,
            SimpleGraph.dist_eq_one_iff_adj.mp (same.symm.trans h)⟩))
        exact mem_union.mpr (.inr (mem_filter.mpr ⟨wy,same,odd,by omega⟩))
    · intro wm
      rcases mem_union.mp wm with xb|cr
      · rcases mem_union.mp xb with wx|wb
        · obtain ⟨wx,e,odd⟩ := mem_filter.mp wx
          have c := cross w wx
          have same : G.dist p w = G.dist a w := by rw [c]; omega
          exact (mem_OO G).mpr ⟨odd,by rwa [same]⟩
        · obtain ⟨rfl,dp⟩ := mem_flag.mp wb
          apply (mem_OO G).mpr
          rw [dab,G.dist_comm (u:=p),dp]
          decide
      · rcases mem_union.mp cr with wc|wr
        · obtain ⟨_,aw,pw⟩ := mem_filter.mp wc
          apply (mem_OO G).mpr
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr aw,SimpleGraph.dist_eq_one_iff_adj.mpr pw]
          decide
        · obtain ⟨_,e,odd,_⟩ := mem_filter.mp wr
          exact (mem_OO G).mpr ⟨odd,e ▸ odd⟩
  have xb : Disjoint X₀ B := disjoint_left.mpr (fun w wx wb => bX ((mem_flag.mp wb).1 ▸ (mem_filter.mp wx).1))
  have cr : Disjoint C R := by
    apply disjoint_left.mpr
    intro w wc wr
    have h := SimpleGraph.dist_eq_one_iff_adj.mpr (mem_filter.mp wc).2.1
    have k := (mem_filter.mp wr).2.2.2
    omega
  have both : Disjoint (X₀∪B) (C∪R) := by
    apply disjoint_left.mpr
    intro w wl wr
    have wy : w∈Y := (mem_union.mp wr).elim (fun h=>(mem_filter.mp h).1) (fun h=>(mem_filter.mp h).1)
    exact (mem_union.mp wl).elim (fun h=>disjoint_left.mp dis (mem_filter.mp h).1 wy)
      (fun h=>bY ((mem_flag.mp h).1 ▸ wy))
  rw [eq,card_union_of_disjoint both,card_union_of_disjoint xb,card_union_of_disjoint cr]
  simp [X₀,B,C,R,Nat.add_assoc]


theorem edge_identity (hc : G.Connected) {a b x p : V} (ap : G.Adj a p) (ax : G.Adj a x)
    (dab : G.dist a b = 3) (X Y : Finset V) (xX : x∈X) (pY : p∈Y) (bX : b∉X) (bY : b∉Y)
    (dis : Disjoint X Y) (cover : ∀ w : V,w=a ∨ w=b ∨ w∈X ∨ w∈Y)
    (pcross : ∀ w∈X,G.dist p w = min (1 + G.dist a w) (G.dist b p + G.dist b w))
    (xcross : ∀ w∈Y,G.dist x w = min (1 + G.dist a w) (G.dist b x + G.dist b w)) :
    Fintype.card V + 2 + (BFlag b (G.dist x b % 2 = 0)).card + (E G a ∩ E G p).card +
      (Extra G Y a b x p).card + (Missing G Y a p).card =
      (E G a).card + (E G p).card + (E G x).card +
      (XOdd G X a b p).card + (BFlag b (G.dist b p = 3)).card +
      (Remote G Y a p \ E G x).card := by
  classical
  let P := Ports G Y a
  let C := Common G Y a p
  let M := Missing G Y a p
  let B := BFlag b (G.dist x b % 2 = 0)
  let T := Base G Y a b x
  let R := Remote G Y a p
  have partition : P=insert p (C∪M) := by
    ext w
    constructor
    · intro hw
      obtain ⟨wy,aw⟩ := mem_filter.mp hw
      by_cases wp : w=p
      · exact mem_insert.mpr (.inl wp)
      by_cases pw : G.Adj p w
      · exact mem_insert.mpr (.inr (mem_union.mpr (.inl (mem_filter.mpr ⟨wy,aw,pw⟩))))
      · exact mem_insert.mpr (.inr (mem_union.mpr (.inr (mem_filter.mpr ⟨hw,wp,pw⟩))))
    · intro hw
      rcases mem_insert.mp hw with rfl|h
      · exact mem_filter.mpr ⟨pY,ap⟩
      · rcases mem_union.mp h with h|h
        · exact mem_filter.mpr ⟨(mem_filter.mp h).1,(mem_filter.mp h).2.1⟩
        · exact (mem_filter.mp h).1
  have pcm : p∉C∪M := by
    intro h
    rcases mem_union.mp h with h|h
    · exact G.loopless p (mem_filter.mp h).2.2
    · exact (mem_filter.mp h).2.1 rfl
  have cm : Disjoint C M := by
    apply disjoint_left.mpr
    intro w wc wm
    exact (mem_filter.mp wm).2.2 (mem_filter.mp wc).2.2
  have cp : P.card=C.card+M.card+1 := by
    rw [partition,card_insert_of_not_mem pcm,card_union_of_disjoint cm]
  have bp : Disjoint B P := by
    apply disjoint_left.mpr
    intro w wb wp
    exact bY ((mem_flag.mp wb).1 ▸ (mem_filter.mp wp).1)
  have xbp : x∉B∪P := by
    intro h
    rcases mem_union.mp h with h|h
    · exact bX ((mem_flag.mp h).1 ▸ xX)
    · exact disjoint_left.mp dis xX (mem_filter.mp h).1
  have cardT : T.card=B.card+P.card+1 := by
    change (insert x (B∪P)).card=_
    rw [card_insert_of_not_mem xbp,card_union_of_disjoint bp]
  have sub : T⊆E G x := by
    intro w hw
    rcases mem_insert.mp hw with rfl|h
    · simp [SimpleGraph.dist_self]
    · rcases mem_union.mp h with h|h
      · obtain ⟨rfl,hb⟩ := mem_flag.mp h
        exact (mem_E G).mpr hb
      · obtain ⟨wy,aw⟩ := mem_filter.mp h
        have c := xcross w wy
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr aw] at c
        have p0 := hc.dist_triangle (u:=a) (v:=x) (w:=b)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr ax,dab, G.dist_comm (u:=x) (v:=b)] at p0
        apply (mem_E G).mpr
        simp only [Nat.min_def] at c
        split at c <;> omega
  have tr : Disjoint T R := by
    apply disjoint_left.mpr
    intro w wt wr
    obtain ⟨wy,_,_,far⟩ := mem_filter.mp wr
    rcases mem_insert.mp wt with rfl|h
    · exact disjoint_left.mp dis xX wy
    · rcases mem_union.mp h with h|h
      · exact bY ((mem_flag.mp h).1 ▸ wy)
      · have near := SimpleGraph.dist_eq_one_iff_adj.mpr (mem_filter.mp h).2
        omega
  have subE : T ∪ (R∩E G x) ⊆ E G x := union_subset sub inter_subset_right
  have eqE : E G x \ (T∪R) = E G x \ (T ∪ (R∩E G x)) := by
    ext w
    simp only [mem_sdiff,mem_union,mem_inter]
    tauto
  have cardE := card_sdiff_add_card_eq_card subE
  have trE := tr.mono_right (show R∩E G x⊆R from inter_subset_left)
  rw [←eqE,card_union_of_disjoint trE] at cardE
  have cardR := card_sdiff_add_card_eq_card (show R∩E G x⊆R from inter_subset_left)
  have eqR : R \ (R∩E G x) = R \ E G x := by
    ext w
    simp only [mem_sdiff,mem_inter]
    tauto
  rw [eqR] at cardR
  have core := adjacent_even_balance G a p
  rw [oo_partition hc ap dab X Y bX bY dis cover pcross] at core
  change Fintype.card V + 2 + B.card + (E G a ∩ E G p).card +
      (E G x \ (T∪R)).card + M.card =
      (E G a).card + (E G p).card + (E G x).card +
      (XOdd G X a b p).card + (BFlag b (G.dist b p = 3)).card + (R \ E G x).card
  change Fintype.card V + (E G a∩E G p).card = _ + _ + 
    ((XOdd G X a b p).card + (BFlag b (G.dist b p = 3)).card + C.card + R.card) at core
  omega

theorem same_terminal_far_order (hc : G.Connected) {a b x p : V} (ap : G.Adj a p) (ax : G.Adj a x)
    (dab : G.dist a b = 3) (X Y : Finset V) (xX : x∈X) (pY : p∈Y) (bX : b∉X) (bY : b∉Y)
    (dis : Disjoint X Y) (cover : ∀ w : V,w=a ∨ w=b ∨ w∈X ∨ w∈Y)
    (pcross : ∀ w∈X,G.dist p w = min (1 + G.dist a w) (G.dist b p + G.dist b w))
    (xcross : ∀ w∈Y,G.dist x w = min (1 + G.dist a w) (G.dist b x + G.dist b w))
    (fx : G.dist b x = 4) (fp : G.dist b p = 4) (d : ℕ)
    (ba : (E G a).card≤d+1) (bp : (E G p).card≤d+1) (bx : (E G x).card≤d+1) :
    Fintype.card V ≤ 3*d := by
  classical
  have bdist (w : V) := hc.dist_triangle (u:=a) (v:=b) (w:=w)
  have noX : XOdd G X a b p = ∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro w hw
    have h := (mem_filter.mp hw).2.1
    have tri := bdist w
    omega
  have noR : Remote G Y a p \ E G x = ∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro w hw
    obtain ⟨wr,wo⟩ := mem_sdiff.mp hw
    obtain ⟨wy,_,odd,_⟩ := mem_filter.mp wr
    have c := xcross w wy
    have t := bdist w
    have e : G.dist x w = 1+G.dist a w := by
      rw [c,fx,min_eq_left]
      omega
    exact wo ((mem_E G).mpr (by omega))
  have h := edge_identity hc ap ax dab X Y xX pY bX bY dis cover pcross xcross
  rw [noX,noR,card_flag,card_flag] at h
  simp only [card_empty] at h
  have f : G.dist x b % 2 = 0 := by rw [G.dist_comm (u:=x) (v:=b),fx]
  simp only [f,if_true,fp,show ¬(4:ℕ)=3 by decide,if_false] at h
  omega


theorem cross_of_closed (hc : G.Connected) {a b x y : V}
    (X : Finset V) (xX : x∈X) (yX : y∉X)
    (closed : ∀ u∈X, ∀ v, G.Adj u v → v=a ∨ v=b ∨ v∈X) :
    G.dist x y = min (G.dist x a + G.dist a y) (G.dist x b + G.dist b y) := by
  open SimpleGraph.Walk in
  have crossing {u v : V} (w : G.Walk u v) (ui : u∈X) (vi : v∉X) :
      a∈w.support ∨ b∈w.support := by
    induction w with
    | nil => exact (vi ui).elim
    | @cons u z v uz w ih =>
      rcases closed u ui z uz with rfl|rfl|zi
      · exact Or.inl (by simp)
      · exact Or.inr (by simp)
      · exact (ih zi vi).imp (fun h => by simp [h]) (fun h => by simp [h])
  apply Nat.le_antisymm
  · exact le_min (hc.dist_triangle (v:=a)) (hc.dist_triangle (v:=b))
  obtain ⟨w,wl⟩ := hc.exists_walk_length_eq_dist x y
  rcases crossing w xX yX with ha|hb
  · obtain ⟨p,q,eq⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp ha
    have hh : w.length=p.length+q.length := by rw [eq,SimpleGraph.Walk.length_append]
    exact (min_le_left _ _).trans (by have hp := G.dist_le p; have hq := G.dist_le q; omega)
  · obtain ⟨p,q,eq⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp hb
    have hh : w.length=p.length+q.length := by rw [eq,SimpleGraph.Walk.length_append]
    exact (min_le_right _ _).trans (by have hp := G.dist_le p; have hq := G.dist_le q; omega)

theorem port_cross_pair (hc : G.Connected) {a b x p : V} (ap : G.Adj a p) (ax : G.Adj a x)
    (X Y : Finset V) (xX : x∈X) (pY : p∈Y) (dis : Disjoint X Y)
    (cover : ∀ w : V,w=a ∨ w=b ∨ w∈X ∨ w∈Y)
    (noEdge : ∀ u∈X,∀ v∈Y,¬G.Adj u v) :
    (∀ w∈X,G.dist p w = min (1 + G.dist a w) (G.dist b p + G.dist b w)) ∧
    (∀ w∈Y,G.dist x w = min (1 + G.dist a w) (G.dist b x + G.dist b w)) := by
  have cx : ∀ u∈X,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈X := by
    intro u hu v uv
    rcases cover v with h|h|h|h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
    · exact (noEdge u hu v h uv).elim
  have cy : ∀ u∈Y,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈Y := by
    intro u hu v uv
    rcases cover v with h|h|h|h
    · exact .inl h
    · exact .inr (.inl h)
    · exact (noEdge v h u hu uv.symm).elim
    · exact .inr (.inr h)
  constructor
  · intro w wx
    have q := cross_of_closed hc Y pY (fun wy=>disjoint_left.mp dis wx wy) cy
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ap.symm,G.dist_comm (u:=p) (v:=b)] at q
    exact q
  · intro w wy
    have q := cross_of_closed hc X xX (fun wx=>disjoint_left.mp dis wx wy) cx
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ax.symm,G.dist_comm (u:=x) (v:=b)] at q
    exact q

theorem edge_identity_of_cut (hc : G.Connected) {a b x p : V} (ap : G.Adj a p) (ax : G.Adj a x)
    (dab : G.dist a b = 3) (X Y : Finset V) (xX : x∈X) (pY : p∈Y) (bX : b∉X) (bY : b∉Y)
    (dis : Disjoint X Y) (cover : ∀ w : V,w=a ∨ w=b ∨ w∈X ∨ w∈Y)
    (noEdge : ∀ u∈X,∀ v∈Y,¬G.Adj u v) :
    Fintype.card V + 2 + (BFlag b (G.dist x b % 2 = 0)).card + (E G a ∩ E G p).card +
      (Extra G Y a b x p).card + (Missing G Y a p).card =
      (E G a).card + (E G p).card + (E G x).card +
      (XOdd G X a b p).card + (BFlag b (G.dist b p = 3)).card +
      (Remote G Y a p \ E G x).card := by
  obtain ⟨pc,xc⟩ := port_cross_pair hc ap ax X Y xX pY dis cover noEdge
  exact edge_identity hc ap ax dab X Y xX pY bX bY dis cover pc xc

theorem same_terminal_far_order_of_cut (hc : G.Connected) {a b x p : V}
    (ap : G.Adj a p) (ax : G.Adj a x) (dab : G.dist a b = 3)
    (X Y : Finset V) (xX : x∈X) (pY : p∈Y) (bX : b∉X) (bY : b∉Y)
    (dis : Disjoint X Y) (cover : ∀ w : V,w=a ∨ w=b ∨ w∈X ∨ w∈Y)
    (noEdge : ∀ u∈X,∀ v∈Y,¬G.Adj u v)
    (fx : G.dist b x = 4) (fp : G.dist b p = 4) (d : ℕ)
    (ba : (E G a).card≤d+1) (bp : (E G p).card≤d+1) (bx : (E G x).card≤d+1) :
    Fintype.card V ≤ 3*d := by
  obtain ⟨pc,xc⟩ := port_cross_pair hc ap ax X Y xX pY dis cover noEdge
  exact same_terminal_far_order hc ap ax dab X Y xX pY bX bY dis cover pc xc fx fp d ba bp bx

#print axioms edge_identity_of_cut
#print axioms same_terminal_far_order_of_cut

#print axioms same_terminal_far_order
#print axioms edge_identity
#print axioms adjacent_even_balance
#print axioms oo_partition
end Graffiti189.AdamEdge
