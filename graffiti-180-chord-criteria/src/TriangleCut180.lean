import MiddleCertificate180
import TriangleRotation180

set_option warningAsError true
set_option maxHeartbeats 500000
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def OnEdges (J : SimpleGraph V) (D : Finset V) (f : V→Bool) : Prop :=
  ∀ a∈D, ∀ b∈D, J.Adj a b → f a=f b
def ConstantOn (D : Finset V) (f : V→Bool) : Prop := ∀ a∈D, ∀ b∈D, f a=f b

omit [Fintype V] [DecidableEq V] in
theorem connected_cuts (J : SimpleGraph V) (D : Finset V) :
    Con J D ↔ D.Nonempty ∧ ∀ f, OnEdges J D f → ConstantOn D f := by
  classical
  let W := ↥(D:Set V)
  let K := J.induce (D:Set V)
  constructor
  · intro con
    obtain ⟨z⟩ := con.nonempty
    refine ⟨⟨z.val,z.property⟩,?_⟩
    intro f hf a ha b hb
    obtain ⟨p⟩ := con (⟨a,ha⟩ : W) ⟨b,hb⟩
    have move {i j : W} (q : K.Walk i j) : f i.val=f j.val := by
      induction q with
      | nil => rfl
      | @cons x y z e _ ih => exact (hf x.val x.property y.val y.property e).trans ih
    exact move p
  · rintro ⟨⟨a,ha⟩,cuts⟩
    let z : W := ⟨a,ha⟩
    apply (connected_iff_exists_forall_reachable K).mpr
    refine ⟨z,?_⟩
    let f (v:V) := if h : v∈D then decide (K.Reachable z ⟨v,h⟩) else false
    have stable : OnEdges J D f := by
      intro x hx y hy e
      have edge : K.Adj (⟨x,hx⟩ : W) ⟨y,hy⟩ := e
      simp only [f,dif_pos hx,dif_pos hy,decide_eq_decide]
      exact ⟨fun q => q.trans edge.reachable,fun q => q.trans edge.symm.reachable⟩
    intro b
    have same := cuts f stable a ha b.val b.property
    have yes : f a=true := by simp [f,ha,z,Reachable.refl]
    have good := same ▸ yes
    have hb : b.val∈D := b.property
    have val : f b.val=decide (K.Reachable z b) := dif_pos hb
    exact of_decide_eq_true (val ▸ good)

theorem leaf_core (G T : SimpleGraph V) (sub : T≤G) (tr : T.IsTree) (hn : 2<Fintype.card V)
    (C : Finset V) (lf : C⊆leaves T) :
    Con G (univ\C) ∧ ∀ x∈C, Dominates G (univ\C) x := by
  classical
  have dom (x : V) (xc : x∈C) : Dominates G (univ\C) x := by
    obtain ⟨y,e⟩ := exists_adj T tr.isConnected (by omega) x
    have out : y∉C := fun k => leaves_nonadjacent T tr hn e (lf xc) (lf k)
    exact ⟨y,mem_sdiff.mpr ⟨mem_univ _,out⟩,sub e⟩
  have positive : (univ\C).Nonempty := by
    obtain ⟨x⟩ := tr.isConnected.nonempty
    by_cases xc : x∈C
    · obtain ⟨y,hy,_⟩ := dom x xc; exact ⟨y,hy⟩
    · exact ⟨x,mem_sdiff.mpr ⟨mem_univ _,xc⟩⟩
  refine ⟨(connected_cuts G _).mpr ⟨positive,?_⟩,dom⟩
  intro f stable a ha b hb
  exact leaf_cut_constant G T sub tr hn C lf f (fun i hi j hj => stable i (by simp [hi]) j (by simp [hj]))
    a (mem_sdiff.mp ha).2 b (mem_sdiff.mp hb).2

/-- The old induced core has two components separated by u,v. Its
Boolean edge-constant functions are all constant once the ends agree. -/
def TwoSides (J : SimpleGraph V) (D : Finset V) (u v : V) : Prop :=
  u∈D ∧ v∈D ∧ ¬Con J D ∧ ∀ f, OnEdges J D f → f u=f v → ConstantOn D f

/-- The old core is connected and misses domination of exactly x among
the proposed leaves. The other tip y belongs to the core. -/
def NeedsTip (J : SimpleGraph V) (C D : Finset V) (x y : V) : Prop :=
  x∈C ∧ y∈D ∧ Con J D ∧ ¬Dominates J D x ∧ ∀ z∈C, z≠x → Dominates J D z

private theorem core_score (J : SimpleGraph V) (C U : Finset V) (cu : C⊆U)
    (con : Con J (univ\C)) (dom : ∀ x∈C, Dominates J (univ\C) x) : C.card≤weightedLeaves J U := by
  classical
  have bound := weightedCore J (univ\C) U con (by intro x hx; apply dom; simpa using hx)
  exact (card_le_card (show C⊆U\(univ\C) from fun x hx => mem_sdiff.mpr ⟨cu hx,by simp [hx]⟩)).trans bound

/-- Exact unrestricted gain criterion for a triangle. It quantifies over a
single proposed eligible leaf set, with only cuts and domination checked
in the lower graph. Every common middle belongs to each winning leaf set. -/
theorem triangle_gain_iff_core (J : SimpleGraph V) (jc : J.Connected) (hn : 2<Fintype.card V)
    (u v w : V) (uv : u≠v) (old : ¬J.Adj u v) (uw : J.Adj u w) (wv : J.Adj w v) (U : Finset V) :
    weightedLeaves J U<weightedLeaves (J⊔SimpleGraph.edge u v) U ↔
    ∃ C⊆U, w∈C ∧ C.card=weightedLeaves J U+1 ∧
      let D := univ\C
      ((TwoSides J D u v ∧ ∀ x∈C, Dominates J D x) ∨ NeedsTip J C D u v ∨ NeedsTip J C D v u) := by
  classical
  let G := J⊔SimpleGraph.edge u v
  have upper : G.Adj u v := Or.inr ((edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,uv⟩)
  have liftD {D : Finset V} {x : V} (h : Dominates J D x) : Dominates G D x := by
    obtain ⟨y,hy,e⟩ := h; exact ⟨y,hy,Or.inl e⟩
  have edgeCases {a b : V} (e : G.Adj a b) : J.Adj a b ∨ (a=u ∧ b=v) ∨ (a=v ∧ b=u) :=
    e.elim Or.inl (fun h => Or.inr ((edge_adj ..).mp h).1)
  have shrink {D : Finset V} (con : Con G D) (clean : ∀ a∈D, ∀ b∈D, G.Adj a b → J.Adj a b) : Con J D :=
    con.mono (fun a b e => clean a.val a.property b.val b.property e)
  constructor
  · intro gain
    obtain ⟨T,tg,tr,opt⟩ := tree_opt G (jc.mono le_sup_left) U
    have win : weightedLeaves J U<(U∩leaves T).card := opt ▸ gain
    obtain ⟨middle,chord,S,_,_,score,absent,sets,_⟩ := common_neighbor_rotation J T (by omega) u v w uv old uw wv U tg tr win
    let C := U∩leaves T
    let D := univ\C
    have size : C.card=weightedLeaves J U+1 := by
      change (U∩leaves T).card=_; rw [sets,card_insert_of_not_mem absent,score]
    have cu : C⊆U := inter_subset_left
    obtain ⟨con,dom⟩ := leaf_core G T tg tr hn C inter_subset_right
    have fail (oldCon : Con J D) (oldDom : ∀ x∈C, Dominates J D x) : False := by
      have := core_score J C U cu oldCon oldDom; omega
    refine ⟨C,cu,middle,size,?_⟩
    have single {x y : V} (xc : x∈C) (yc : y∉C) (xy : (x=u ∧ y=v) ∨ (x=v ∧ y=u)) :
        NeedsTip J C D x y := by
      have yd : y∈D := by simp [D,yc]
      have xd : x∉D := by simp [D,xc]
      have pair {a b : V} (e : G.Adj a b) : J.Adj a b ∨ (a=x ∧ b=y) ∨ (a=y ∧ b=x) := by
        have cases := edgeCases e
        rcases xy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact cases
        · exact cases.imp_right Or.symm
      have oldCon := shrink con (fun a ha b hb e => by
        rcases pair e with j|⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact j
        · exact (xd ha).elim
        · exact (xd hb).elim)
      have others (z : V) (zc : z∈C) (zx : z≠x) : Dominates J D z := by
        obtain ⟨i,hi,e⟩ := dom z zc
        rcases pair e with j|⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact ⟨i,hi,j⟩
        · exact (zx rfl).elim
        · exact (yc zc).elim
      refine ⟨xc,yd,oldCon,?_,others⟩
      intro all
      apply fail oldCon
      intro z hz
      by_cases h : z=x
      · exact h ▸ all
      · exact others z hz h
    by_cases a : u∈C
    · have b : v∉C := fun k => leaves_nonadjacent T tr hn chord (mem_inter.mp a).2 (mem_inter.mp k).2
      exact Or.inr (Or.inl (single a b (Or.inl ⟨rfl,rfl⟩)))
    by_cases b : v∈C
    · exact Or.inr (Or.inr (single b a (Or.inr ⟨rfl,rfl⟩)))
    have oldDom (x : V) (xc : x∈C) : Dominates J D x := by
      obtain ⟨i,hi,e⟩ := dom x xc
      rcases edgeCases e with j|⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨i,hi,j⟩
      · exact (a xc).elim
      · exact (b xc).elim
    refine Or.inl ⟨⟨by simp [D,a],by simp [D,b],fun k => fail k oldDom,?_⟩,oldDom⟩
    intro f hf equal
    apply ((connected_cuts G D).mp con).2
    intro x hx y hy e
    rcases edgeCases e with j|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact hf x hx y hy j
    · exact equal
    · exact equal.symm
  · rintro ⟨C,cu,_,size,cert⟩
    let D := univ\C
    have finish (con : Con G D) (dom : ∀ x∈C, Dominates G D x) : weightedLeaves J U<weightedLeaves G U := by
      have := core_score G C U cu con dom; omega
    have one {x y : V} (edge : G.Adj x y) (h : NeedsTip J C D x y) : weightedLeaves J U<weightedLeaves G U := by
      obtain ⟨_,yd,con,_,others⟩ := h
      apply finish (con.mono (fun _ _ e => Or.inl e))
      intro z zc
      by_cases eq : z=x
      · exact eq ▸ ⟨y,yd,edge⟩
      · exact liftD (others z zc eq)
    rcases cert with ⟨⟨ud,vd,_,cuts⟩,dom⟩|s|s
    · apply finish _ (fun x xc => liftD (dom x xc))
      apply (connected_cuts G D).mpr
      refine ⟨⟨u,ud⟩,?_⟩
      intro f good
      exact cuts f (fun x hx y hy e => good x hx y hy (Or.inl e)) (good u ud v vd upper)
    · exact one upper s
    · exact one upper.symm s

#print axioms connected_cuts
#print axioms leaf_core
#print axioms triangle_gain_iff_core
end Minimal180
