import RemoteT2SideCompletionCuts
import RemoteT2Scope
import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteT2CompletionTransfer
open SquareCap (HasFactor SmallTrivial boundary)
open RemoteT2PairCounts (innerCut mismatch OutsideTwo)
open RemoteT2SideCompletionCuts (same_side_completion_cut)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

abbrev Surv (x y : V) := {z : V // z≠x ∧ z≠y}

def marked {W : Type*} (a b u v : W) : Prop := (u=a∧v=b) ∨ (u=b∧v=a)

theorem marked_symm {W : Type*} {a b u v : W} :
    marked a b u v ↔ marked a b v u := by unfold marked; aesop

def eraseEdge {W : Type*} (H : SimpleGraph W) (a b : W) : SimpleGraph W where
  Adj u v := H.Adj u v ∧ ¬marked a b u v
  symm := fun _ _ h => ⟨h.1.symm,fun n=>h.2 (marked_symm.mpr n)⟩
  loopless := fun v h=>H.loopless v h.1

omit [Fintype V] [DecidableEq V] in
def completion {x y : V} (a b d e : Surv x y) (ab : a≠b) (de : d≠e) :
    SimpleGraph (Surv x y) where
  Adj u v := G.Adj u.val v.val ∨ marked a b u v ∨ marked d e u v
  symm := fun _ _ h => h.elim (fun h=>Or.inl h.symm) (fun h=>Or.inr
    (h.elim (fun h=>Or.inl (marked_symm.mp h)) (fun h=>Or.inr (marked_symm.mp h))))
  loopless := by
    intro u h
    rcases h with h|h|h
    · exact G.loopless u.val h
    · rcases h with ⟨e,f⟩|⟨e,f⟩
      · exact ab (e.symm.trans f)
      · exact ab (f.symm.trans e)
    · rcases h with ⟨u₁,u₂⟩|⟨u₁,u₂⟩
      · exact de (u₁.symm.trans u₂)
      · exact de (u₂.symm.trans u₁)

omit [Fintype V] [DecidableEq V] in
theorem restoration_identity {x y : V} (a b d e u v : Surv x y)
    (ab : a≠b) (de : d≠e) (newAB : ¬G.Adj a.val b.val) (newDE : ¬G.Adj d.val e.val) :
    eraseEdge (eraseEdge (eraseEdge (completion G a b d e ab de) a b) d e) u v =
      eraseEdge (G.induce {z : V | z≠x∧z≠y}) u v := by
  ext m n
  change ((((G.Adj m.val n.val ∨ marked a b m n ∨ marked d e m n) ∧ ¬marked a b m n) ∧
    ¬marked d e m n) ∧ ¬marked u v m n) ↔ (G.Adj m.val n.val ∧ ¬marked u v m n)
  constructor
  · rintro ⟨⟨⟨h,hab⟩,hde⟩,huv⟩
    exact ⟨h.elim id (fun h=>h.elim (fun h=>(hab h).elim) (fun h=>(hde h).elim)),huv⟩
  · rintro ⟨mn,uv⟩
    refine ⟨⟨⟨Or.inl mn,?_⟩,?_⟩,uv⟩
    · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
      · exact newAB mn
      · exact newAB mn.symm
    · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
      · exact newDE mn
      · exact newDE mn.symm

/-- Exact translation, in both directions, between remote pair deletion and
the same-side completion avoiding all three specified edges. Avoiding only
the inherited edge, or only it and one added edge, is not this statement. -/
theorem completion_factor_iff {x y : V} (a b d e u v : Surv x y)
    (ab : a≠b) (de : d≠e) (newAB : ¬G.Adj a.val b.val) (newDE : ¬G.Adj d.val e.val) :
    HasFactor (eraseEdge (eraseEdge (eraseEdge (completion G a b d e ab de) a b) d e) u v) ↔
      HasFactor (eraseEdge (G.induce {z : V | z≠x∧z≠y}) u v) := by
  rw [restoration_identity G a b d e u v ab de newAB newDE]


private def liftedColor {x y : V} (f : Surv x y→Bool) (z : V) : Bool :=
  if h : z≠x∧z≠y then f ⟨z,h⟩ else false

omit [Fintype V] in
private theorem lifted_eq {x y : V} (f : Surv x y→Bool) (z : Surv x y) :
    liftedColor f z.val=f z := by simp [liftedColor,z.property]

omit [Fintype V] [DecidableEq V] in
private def pairIncl (x y : V) : (Surv x y×Surv x y) ↪ V×V :=
  ⟨fun p=>(p.1.val,p.2.val),fun _ _ h=>Prod.ext (Subtype.ext (congrArg Prod.fst h))
    (Subtype.ext (congrArg Prod.snd h))⟩

private theorem cut_interior_exact {x y : V} (f : Surv x y→Bool) :
    (boundary (G.induce {z : V | z≠x∧z≠y}) f).map (pairIncl x y) =
      innerCut G (liftedColor f) x y := by
  classical
  ext ⟨u,v⟩
  constructor
  · intro h
    obtain ⟨⟨p,q⟩,mem,eq⟩ := mem_map.mp h
    have e : (p.val,q.val)=(u,v) := eq
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj e
    simp only [boundary,mem_filter,mem_univ,true_and] at mem
    exact mem_filter.mpr ⟨by
      simp only [boundary,mem_filter,mem_univ,true_and,lifted_eq]
      exact mem, p.property.1,p.property.2,q.property.1,q.property.2⟩
  · intro h
    obtain ⟨mem,ux,uy,vx,vy⟩ := mem_filter.mp h
    let p : Surv x y := ⟨u,ux,uy⟩
    let q : Surv x y := ⟨v,vx,vy⟩
    apply mem_map.mpr
    refine ⟨(p,q),?_,rfl⟩
    simp only [boundary,mem_filter,mem_univ,true_and]
    simp only [boundary,mem_filter,mem_univ,true_and] at mem
    exact ⟨(lifted_eq f p).symm.trans mem.1,(lifted_eq f q).symm.trans mem.2.1,mem.2.2⟩

private def wireCut {W : Type*} (f : W→Bool) (a b : W) : Finset (W×W) :=
  if f a=f b then ∅ else if f a then {(a,b)} else {(b,a)}

private theorem wire_mem {W : Type*} (f : W→Bool) (a b u v : W) :
    (u,v)∈wireCut f a b ↔ f u=true∧f v=false∧marked a b u v := by
  unfold wireCut
  cases aa : f a <;> cases bb : f b
  · simp [aa,bb,marked]
    rintro h k
    constructor <;> rintro rfl rfl <;> simp_all
  · simp only [aa,bb,reduceCtorEq,if_false,mem_singleton,Prod.mk.injEq,marked]
    constructor
    · rintro ⟨rfl,rfl⟩
      exact ⟨bb,aa,Or.inr ⟨rfl,rfl⟩⟩
    · rintro ⟨ut,vf,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
      · rw [aa] at ut
        contradiction
      · exact ⟨rfl,rfl⟩
  · simp only [aa,bb,reduceCtorEq,if_false,ite_true,mem_singleton,Prod.mk.injEq,marked]
    constructor
    · rintro ⟨rfl,rfl⟩
      exact ⟨aa,bb,Or.inl ⟨rfl,rfl⟩⟩
    · rintro ⟨ut,vf,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
      · exact ⟨rfl,rfl⟩
      · rw [bb] at ut
        contradiction
  · simp [aa,bb,marked]
    rintro h k
    constructor <;> rintro rfl rfl <;> simp_all

private theorem wire_card {W : Type*} (f : W→Bool) (a b : W) :
    (wireCut f a b).card=mismatch (f a) (f b) := by
  cases aa : f a <;> cases bb : f b <;> simp [wireCut,mismatch,aa,bb]

theorem completion_boundary_exact {x y : V} (f : Surv x y→Bool) (a b d e : Surv x y)
    (ab : a≠b) (de : d≠e) (newAB : ¬G.Adj a.val b.val) (newDE : ¬G.Adj d.val e.val)
    (ad : a≠d) (ae : a≠e) :
    (boundary (completion G a b d e ab de) f).card =
      (innerCut G (liftedColor f) x y).card+mismatch (f a) (f b)+mismatch (f d) (f e) := by
  classical
  let I := boundary (G.induce {z : V | z≠x∧z≠y}) f
  let A := wireCut f a b
  let B := wireCut f d e
  have eq : boundary (completion G a b d e ab de) f=(I∪A)∪B := by
    ext ⟨u,v⟩
    simp only [I,A,B,wire_mem,boundary,mem_union,mem_filter,mem_univ,true_and]
    change (f u=true∧f v=false∧(G.Adj u.val v.val∨marked a b u v∨marked d e u v)) ↔ _
    tauto
  have di : Disjoint I A := by
    apply disjoint_left.mpr
    rintro ⟨u,v⟩ hi ha
    simp only [I,boundary,mem_filter,mem_univ,true_and] at hi
    rcases (wire_mem f a b u v).mp ha with ⟨_,_,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩
    · exact newAB hi.2.2
    · exact newAB hi.2.2.symm
  have ds : Disjoint (I∪A) B := by
    apply disjoint_left.mpr
    rintro ⟨u,v⟩ h hb
    obtain ⟨_,_,bd⟩ := (wire_mem f d e u v).mp hb
    rcases mem_union.mp h with hi|ha
    · simp only [I,boundary,mem_filter,mem_univ,true_and] at hi
      rcases bd with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact newDE hi.2.2
      · exact newDE hi.2.2.symm
    · obtain ⟨_,_,ac⟩ := (wire_mem f a b u v).mp ha
      rcases ac with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rcases bd with ⟨e1,e2⟩|⟨e1,e2⟩
      · exact ad e1
      · exact ae e1
      · exact ae e2
      · exact ad e2
  have ic : I.card=(innerCut G (liftedColor f) x y).card := by
    rw [←cut_interior_exact G f,card_map]
  rw [eq,card_union_of_disjoint ds,card_union_of_disjoint di,ic,wire_card,wire_card]

/-- Cyclic-five geometry really yields the cyclic-four small-cut property
for the same-side completion, not merely an abstract four-unit cut budget. -/
theorem cyclic_five_completion_smallTrivial [DecidableRel G.Adj]
    (small : SmallTrivial G) (cyc5 : PentagonCap.SmallFourTrivial G)
    {x y : V} (xy : G.Adj x y) (cx : G.degree x=3) (cy : G.degree y=3)
    (a b d e : Surv x y)
    (X : (G.neighborFinset x).erase y={a.val,b.val})
    (Y : (G.neighborFinset y).erase x={d.val,e.val})
    (ab : a≠b) (de : d≠e) (newAB : ¬G.Adj a.val b.val) (newDE : ¬G.Adj d.val e.val)
    (ad : a≠d) (ae : a≠e) :
    SmallTrivial (completion G a b d e ab de) := by
  classical
  intro f low
  by_contra! both
  obtain ⟨⟨p,q,hp,hq,pq⟩,⟨m,n,hm,hn,mn⟩⟩ := both
  have nontriv (u v : Surv x y) (uv : u≠v) (b : Bool) (hu : f u=b) (hv : f v=b) :
      OutsideTwo (liftedColor f) x y b := by
    exact ⟨u.val,v.val,u.property.1,u.property.2,v.property.1,v.property.2,
      fun eq=>uv (Subtype.ext eq),(lifted_eq f u).trans hu,(lifted_eq f v).trans hv⟩
  have bound := same_side_completion_cut G small cyc5 (liftedColor f) xy cx cy X Y
    (nontriv p q pq true hp hq) (nontriv m n mn false hm hn)
  rw [completion_boundary_exact G f a b d e ab de newAB newDE ad ae] at low
  simp only [lifted_eq] at bound
  omega

#print axioms completion_boundary_exact
#print axioms cyclic_five_completion_smallTrivial


section Cubic
open RemoteT2Scope (cyclic_four_pair_no_common)
variable [DecidableRel G.Adj]

/-- Distinct genuine completion wires restore cubicity. The ordinary
neighbors of the removed vertices are specified exactly, not just included. -/
theorem cyclic_four_completion_cubic (small : SmallTrivial G) (big : 5≤Fintype.card V)
    (cub : ∀ z : V,G.degree z=3) {x y : V} (xy : G.Adj x y)
    (a b d e : Surv x y)
    (X : (G.neighborFinset x).erase y={a.val,b.val})
    (Y : (G.neighborFinset y).erase x={d.val,e.val})
    (ab : a≠b) (de : d≠e) (ad : a≠d) (ae : a≠e) (bd : b≠d) (be : b≠e)
    (newAB : ¬G.Adj a.val b.val) (newDE : ¬G.Adj d.val e.val)
    (z : Surv x y) : @SimpleGraph.degree _ (completion G a b d e ab de) z
      (Fintype.ofFinite _) = 3 := by
  classical
  let H := completion G a b d e ab de
  have degArgs : (Fintype.ofFinite (H.neighborSet z)) =
      (inferInstance : Fintype (H.neighborSet z)) := Subsingleton.elim _ _
  change @SimpleGraph.degree _ H z (Fintype.ofFinite _) = 3
  rw [degArgs,←card_neighborFinset_eq_degree]
  let I : Finset (Surv x y) := univ.filter (fun u=>G.Adj z.val u.val)
  let B : Finset (Surv x y) := univ.filter (fun u=>marked a b z u ∨ marked d e z u)
  have edges : H.neighborFinset z=I∪B := by
    ext u
    simp only [I,B,mem_neighborFinset,mem_union,mem_filter,mem_univ,true_and]
    rfl
  have apart : Disjoint I B := by
    apply disjoint_left.mpr
    intro u ui ue
    have edge : G.Adj z.val u.val := (mem_filter.mp ui).2
    have fresh : marked a b z u ∨ marked d e z u := (mem_filter.mp ue).2
    rcases fresh with m|m
    · rcases m with ⟨hz,hu⟩|⟨hz,hu⟩
      · exact newAB (by simpa only [hz,hu] using edge)
      · exact newAB (by simpa only [hz,hu] using edge.symm)
    · rcases m with ⟨hz,hu⟩|⟨hz,hu⟩
      · exact newDE (by simpa only [hz,hu] using edge)
      · exact newDE (by simpa only [hz,hu] using edge.symm)
  have old :
      I.map (Function.Embedding.subtype (fun u : V=>u≠x∧u≠y)) =
        ((G.neighborFinset z.val).erase x).erase y := by
    ext u
    constructor
    · intro m
      obtain ⟨w,iw,eq⟩ := mem_map.mp m
      change w.val=u at eq
      subst u
      exact mem_erase.mpr ⟨w.property.2,mem_erase.mpr ⟨w.property.1,
        (mem_neighborFinset _ _ _).mpr ((mem_filter.mp iw).2)⟩⟩
    · intro m
      obtain ⟨uy,m⟩ := mem_erase.mp m
      obtain ⟨ux,m⟩ := mem_erase.mp m
      exact mem_map.mpr ⟨⟨u,ux,uy⟩,mem_filter.mpr ⟨mem_univ _,
        (mem_neighborFinset _ _ _).mp m⟩,rfl⟩
  have oldCard : I.card=(((G.neighborFinset z.val).erase x).erase y).card := by
    rw [←old,card_map]
  have portX : G.Adj z.val x ↔ z=a∨z=b := by
    have mem : z.val∈(G.neighborFinset x).erase y ↔ G.Adj z.val x :=
      ⟨fun h=>((mem_neighborFinset _ _ _).mp (mem_erase.mp h).2).symm,
        fun h=> mem_erase.mpr ⟨z.property.2,(mem_neighborFinset _ _ _).mpr h.symm⟩⟩
    rw [X,mem_insert,mem_singleton] at mem
    exact mem.symm.trans (or_congr ⟨Subtype.ext,congrArg Subtype.val⟩
      ⟨Subtype.ext,congrArg Subtype.val⟩)
  have portY : G.Adj z.val y ↔ z=d∨z=e := by
    have mem : z.val∈(G.neighborFinset y).erase x ↔ G.Adj z.val y :=
      ⟨fun h=>((mem_neighborFinset _ _ _).mp (mem_erase.mp h).2).symm,
        fun h=> mem_erase.mpr ⟨z.property.1,(mem_neighborFinset _ _ _).mpr h.symm⟩⟩
    rw [Y,mem_insert,mem_singleton] at mem
    exact mem.symm.trans (or_congr ⟨Subtype.ext,congrArg Subtype.val⟩
      ⟨Subtype.ext,congrArg Subtype.val⟩)
  have noCommon : ¬(G.Adj z.val x∧G.Adj z.val y) := fun p=>
    cyclic_four_pair_no_common small big cub xy z.val ⟨p.1.symm,p.2.symm⟩
  rw [edges,card_union_of_disjoint apart,oldCard]
  by_cases h₁ : G.Adj z.val x
  · have h₂ : ¬G.Adj z.val y := fun h=>noCommon ⟨h₁,h⟩
    have ny : y∉(G.neighborFinset z.val).erase x :=
      fun m=>h₂ ((mem_neighborFinset _ _ _).mp (mem_erase.mp m).2)
    rw [erase_eq_of_not_mem ny,card_erase_of_mem ((mem_neighborFinset _ _ _).mpr h₁),
      card_neighborFinset_eq_degree,cub]
    rcases portX.mp h₁ with rfl|rfl
    · have singleton : B={b} := by ext t; simp [B,marked,ab,ad,ae,eq_comm]
      rw [singleton,card_singleton]
    · have singleton : B={a} := by ext t; simp [B,marked,ab.symm,bd,be,eq_comm]
      rw [singleton,card_singleton]
  · by_cases h₂ : G.Adj z.val y
    · have nx : x∉G.neighborFinset z.val := fun m=>h₁ ((mem_neighborFinset _ _ _).mp m)
      rw [erase_eq_of_not_mem nx,card_erase_of_mem ((mem_neighborFinset _ _ _).mpr h₂),
        card_neighborFinset_eq_degree,cub]
      rcases portY.mp h₂ with rfl|rfl
      · have singleton : B={e} := by ext t; simp [B,marked,ad.symm,bd.symm,de,eq_comm]
        rw [singleton,card_singleton]
      · have singleton : B={d} := by ext t; simp [B,marked,ae.symm,be.symm,de.symm,eq_comm]
        rw [singleton,card_singleton]
    · have nx : x∉G.neighborFinset z.val := fun m=>h₁ ((mem_neighborFinset _ _ _).mp m)
      have ny : y∉G.neighborFinset z.val := fun m=>h₂ ((mem_neighborFinset _ _ _).mp m)
      rw [erase_eq_of_not_mem nx,erase_eq_of_not_mem ny,card_neighborFinset_eq_degree,cub]
      have zA : z≠a := fun h=>h₁ (portX.mpr (Or.inl h))
      have zB : z≠b := fun h=>h₁ (portX.mpr (Or.inr h))
      have zD : z≠d := fun h=>h₂ (portY.mpr (Or.inl h))
      have zE : z≠e := fun h=>h₂ (portY.mpr (Or.inr h))
      have empty : B=∅ := by ext t; simp [B,marked,zA,zB,zD,zE]
      rw [empty,card_empty]

#print axioms cyclic_four_completion_cubic
end Cubic


section Promise
universe u
variable {W : Type u} [Fintype W] [DecidableEq W]

/-- Strictly smaller order-zero cyclic-four three-edge avoidance, where
one of the marked edges is disjoint from both others and the latter
two may meet. It is stronger than ordinary two-edge avoidance. -/
def SmallerIsolatedAvoid3 (n : ℕ) : Prop :=
  ∀ (T : Type u) [Fintype T] [DecidableEq T] (H : SimpleGraph T) [DecidableRel H.Adj],
    Fintype.card T<n → (∀ z,H.degree z=3) → SquareCap.ThreeConnected H → SmallTrivial H →
    Fintype.card T%6=0 →
    ∀ a b d e r s : T, H.Adj a b → H.Adj d e → H.Adj r s →
      a≠d → a≠e → b≠d → b≠e →
      a≠r → a≠s → b≠r → b≠s → ¬marked d e r s →
      HasFactor (eraseEdge (eraseEdge (eraseEdge H a b) d e) r s)

private theorem survivor_card {x y : W} (xy : x≠y) :
    Fintype.card (Surv x y) = Fintype.card W-2 := by
  have hs : ∀ z : W,z∈(univ.erase x).erase y ↔ z≠x∧z≠y := by
    intro z
    simp [and_comm]
  have hx := Fintype.subtype_card _ hs
  rw [Subsingleton.elim (Fintype.subtype ((univ.erase x).erase y) hs)
    (inferInstance : Fintype (Surv x y))] at hx
  have eq : Fintype.card (Surv x y)=((univ.erase x).erase y).card := hx
  rw [eq,card_erase_of_mem (mem_erase.mpr ⟨xy.symm,mem_univ _⟩),
    card_erase_of_mem (mem_univ _),card_univ]
  omega

/-- The cyclic-five same-side completion translates the exact remote case
to strictly smaller cubic cyclic-four order-zero three-edge avoidance,
with the x-side new edge isolated among the three specified edges.
No claim of deriving that promise from ordinary two-edge avoidance;
all three omissions are used in restoration. -/
theorem cyclic_five_remote_of_smaller_avoid_three (G : SimpleGraph W) [DecidableRel G.Adj]
    (small : SmallTrivial G) (cyc5 : PentagonCap.SmallFourTrivial G)
    (big : 5≤Fintype.card W) (cub : ∀ z : W,G.degree z=3) (rem : Fintype.card W%6=2)
    {x y : W} (xy : G.Adj x y) (a b d e r s : Surv x y)
    (X : (G.neighborFinset x).erase y={a.val,b.val})
    (Y : (G.neighborFinset y).erase x={d.val,e.val})
    (ab : a≠b) (de : d≠e) (ad : a≠d) (ae : a≠e) (bd : b≠d) (be : b≠e)
    (newAB : ¬G.Adj a.val b.val) (newDE : ¬G.Adj d.val e.val)
    (real : G.Adj r.val s.val)
    (remoteR : ¬G.Adj x r.val) (remoteS : ¬G.Adj x s.val)
    (smaller : SmallerIsolatedAvoid3.{u} (Fintype.card W)) :
    HasFactor (eraseEdge (G.induce {z : W | z≠x∧z≠y}) r s) := by
  classical
  let H := completion G a b d e ab de
  have n := survivor_card xy.ne
  have smallH : SmallTrivial H :=
    cyclic_five_completion_smallTrivial G small cyc5 xy (cub x) (cub y)
      a b d e X Y ab de newAB newDE ad ae
  have cubH (z : Surv x y) : H.degree z=3 := by
    have h := cyclic_four_completion_cubic G small big cub xy a b d e X Y ab de
      ad ae bd be newAB newDE z
    change @SimpleGraph.degree _ H z (Fintype.ofFinite (H.neighborSet z))=3 at h
    rw [Subsingleton.elim (Fintype.ofFinite (H.neighborSet z)) (inferInstance : Fintype (H.neighborSet z))] at h
    exact h
  have vc := SquareCap.three_connected_of_small_trivial H cubH (by omega) smallH
  have less : Fintype.card (Surv x y)<Fintype.card W := by omega
  have rem' : Fintype.card (Surv x y)%6=0 := by omega
  have nea : G.Adj x a.val := by
    have h : a.val∈(G.neighborFinset x).erase y := by rw [X]; simp
    exact (mem_neighborFinset _ _ _).mp (mem_erase.mp h).2
  have neb : G.Adj x b.val := by
    have h : b.val∈(G.neighborFinset x).erase y := by rw [X]; simp
    exact (mem_neighborFinset _ _ _).mp (mem_erase.mp h).2
  have A : H.Adj a b := Or.inr (Or.inl (Or.inl ⟨rfl,rfl⟩))
  have D : H.Adj d e := Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩))
  have E : H.Adj r s := Or.inl real
  have third : ¬marked d e r s := by
    rintro (⟨q,t⟩|⟨q,t⟩)
    · exact newDE (by simpa only [q,t] using real)
    · exact newDE (by simpa only [q,t] using real.symm)
  apply (completion_factor_iff G a b d e r s ab de newAB newDE).mp
  exact smaller (Surv x y) H less cubH vc smallH rem'
    a b d e r s A D E ad ae bd be (fun t=>remoteR (t ▸ nea)) (fun t=>remoteS (t ▸ nea))
    (fun t=>remoteR (t ▸ neb)) (fun t=>remoteS (t ▸ neb)) third


/-- Automatic version: all four ports are chosen from the original
cubic shape. Cyclic-four triangle-freeness makes them distinct and
ensures both replacement edges are genuinely new. -/
theorem cyclic_five_remote_automatic (G : SimpleGraph W) [DecidableRel G.Adj]
    (small : SmallTrivial G) (cyc5 : PentagonCap.SmallFourTrivial G)
    (big : 5≤Fintype.card W) (cub : ∀ z : W,G.degree z=3) (rem : Fintype.card W%6=2)
    {x y : W} (xy : G.Adj x y) (r s : Surv x y) (real : G.Adj r.val s.val)
    (remoteR : ¬G.Adj x r.val) (remoteS : ¬G.Adj x s.val)
    (smaller : SmallerIsolatedAvoid3.{u} (Fintype.card W)) :
    HasFactor (eraseEdge (G.induce {z : W | z≠x∧z≠y}) r s) := by
  classical
  have pick {x y : W} (edge : G.Adj x y) :
      ∃ a b : W,a≠b∧(G.neighborFinset x).erase y={a,b} := by
    apply card_eq_two.mp
    rw [card_erase_of_mem ((mem_neighborFinset _ _ _).mpr edge),card_neighborFinset_eq_degree,cub]
  obtain ⟨a,b,ab,X⟩ := pick xy
  obtain ⟨d,e,de,Y⟩ := pick xy.symm
  have get {t p q : W} (h : t∈(G.neighborFinset p).erase q) :
      t≠p ∧ t≠q ∧ G.Adj p t := by
    obtain ⟨n,m⟩ := mem_erase.mp h
    have ed := (mem_neighborFinset _ _ _).mp m
    exact ⟨ed.ne.symm,n,ed⟩
  have hp : a∈(G.neighborFinset x).erase y := by rw [X]; simp
  have hq : b∈(G.neighborFinset x).erase y := by rw [X]; simp
  have hD : d∈(G.neighborFinset y).erase x := by rw [Y]; simp
  have hE : e∈(G.neighborFinset y).erase x := by rw [Y]; simp
  obtain ⟨ax,ay,xa⟩ := get hp
  obtain ⟨bx,by',xb⟩ := get hq
  obtain ⟨dy,dx,yd⟩ := get hD
  obtain ⟨ey,ex,ye⟩ := get hE
  let A : Surv x y := ⟨a,ax,ay⟩
  let B : Surv x y := ⟨b,bx,by'⟩
  let D : Surv x y := ⟨d,dx,dy⟩
  let E : Surv x y := ⟨e,ex,ey⟩
  have uniq {u v : W} (xu : G.Adj x u) (yv : G.Adj y v) : u≠v := by
    rintro rfl
    exact RemoteT2Scope.cyclic_four_pair_no_common small big cub xy u ⟨xu,yv⟩
  have notA : ¬G.Adj a b := fun h=>
    RemoteT2Scope.cyclic_four_pair_no_common small big cub xa b ⟨xb,h⟩
  have notB : ¬G.Adj d e := fun h=>
    RemoteT2Scope.cyclic_four_pair_no_common small big cub yd e ⟨ye,h⟩
  exact cyclic_five_remote_of_smaller_avoid_three G small cyc5 big cub rem xy A B D E r s X Y
    (fun h=>ab (congrArg Subtype.val h)) (fun h=>de (congrArg Subtype.val h))
    (fun h=>uniq xa yd (congrArg Subtype.val h)) (fun h=>uniq xa ye (congrArg Subtype.val h))
    (fun h=>uniq xb yd (congrArg Subtype.val h)) (fun h=>uniq xb ye (congrArg Subtype.val h))
    notA notB real remoteR remoteS smaller

#print axioms cyclic_five_remote_automatic

#print axioms cyclic_five_remote_of_smaller_avoid_three
end Promise

#print axioms restoration_identity
#print axioms completion_factor_iff
end KelmansCactus.AtomicBridge.RemoteT2CompletionTransfer
