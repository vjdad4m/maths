import BicycleSingletonMean133
import BicycleTriangleCapsules1133
import BicycleTriangleCapsules2133
import BicycleTriangleCapsules3133

namespace Graffiti133TriangleCritical
open SimpleGraph Finset Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def TriangleContraction (S : Finset V) : SimpleGraph (Option {x : V // x∉S}) where
  Adj u v := match u,v with
    | none,none => False
    | none,some v => ∃ x∈S, G.Adj x v.val
    | some u,none => ∃ x∈S, G.Adj x u.val
    | some u,some v => G.Adj u.val v.val
  symm := by intro u v e; cases u <;> cases v <;> first | exact e | exact e.symm
  loopless := by intro x e; cases x with
    | none => exact e
    | some x => exact (G.loopless x.val) e

noncomputable instance triangleContractionDec (S : Finset V) :
    DecidableRel (TriangleContraction G S).Adj := Classical.decRel _

def collapse (S : Finset V) (x : V) : Option {x : V // x∉S} :=
  if h : x∈S then none else some ⟨x,h⟩

theorem collapse_surj (S : Finset V) (hs : S.Nonempty) :
    Function.Surjective (collapse S) := by
  intro q
  cases q with
  | none =>
    obtain ⟨x,hx⟩ := hs
    exact ⟨x,by simp [collapse,hx]⟩
  | some x => exact ⟨x.val,by simp [collapse,x.property]⟩

theorem collapse_adj_or_eq {S : Finset V} {x y : V} (h : G.Adj x y) :
    (TriangleContraction G S).Adj (collapse S x) (collapse S y) ∨ collapse S x=collapse S y := by
  by_cases hx : x∈S <;> by_cases hy : y∈S <;> simp only [collapse,hx,hy,dif_pos,dif_neg]
  · exact Or.inr trivial
  · exact Or.inl ⟨x,hx,h⟩
  · exact Or.inl ⟨y,hy,h.symm⟩
  · exact Or.inl h

theorem triangle_contraction_connected (S : Finset V) (hs : S.Nonempty) (hc : G.Connected) :
    (TriangleContraction G S).Connected := by
  let J := TriangleContraction G S
  have transfer {x y : V} (p : G.Walk x y) :
      J.Reachable (collapse S x) (collapse S y) := by
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons e p ih =>
      rcases collapse_adj_or_eq G e with a|a
      · exact (SimpleGraph.Adj.reachable a).trans ih
      · rw [a]
        exact ih
  refine ⟨?_⟩
  intro p q
  obtain ⟨x,rfl⟩ := collapse_surj S hs p
  obtain ⟨y,rfl⟩ := collapse_surj S hs q
  obtain ⟨w⟩ := hc.preconnected x y
  exact transfer w

theorem triangle_single_external_neighbor (h4 : FourCycleFree G)
    (a b c : V) (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a)
    (x : V) (out : x∉({a,b,c}:Finset V)) :
    ∀ u v, u∈({a,b,c}:Finset V) → v∈({a,b,c}:Finset V) →
      G.Adj x u → G.Adj x v → u=v := by
  have xa : x≠a := fun h=>out (by simp [h])
  have xb : x≠b := fun h=>out (by simp [h])
  have xc : x≠c := fun h=>out (by simp [h])
  have noab (hx : G.Adj x a) (hy : G.Adj x b) : False :=
    xc (h4 a b x c ab.ne hx.symm hy.symm ca.symm bc)
  have noac (hx : G.Adj x a) (hy : G.Adj x c) : False :=
    xb (h4 a c x b ca.ne.symm hx.symm hy.symm ab bc.symm)
  have nobc (hx : G.Adj x b) (hy : G.Adj x c) : False :=
    xa (h4 b c x a bc.ne hx.symm hy.symm ab.symm ca)
  intro u v hu hv xu xv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
  rcases hu with rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl
  all_goals first | rfl | exact (noab xu xv).elim | exact (noab xv xu).elim |
    exact (noac xu xv).elim | exact (noac xv xu).elim |
    exact (nobc xu xv).elim | exact (nobc xv xu).elim

theorem external_degree_in_contraction (S : Finset V) (x : {x : V // x∉S})
    (unique : ∀ u v, u∈S → v∈S → G.Adj x.val u → G.Adj x.val v → u=v) :
    (TriangleContraction G S).degree (some x) = G.degree x.val := by
  classical
  rw [←G.card_neighborFinset_eq_degree,←(TriangleContraction G S).card_neighborFinset_eq_degree]
  symm
  apply Finset.card_bij (fun y _=>collapse S y)
  · intro y hy
    have e := (G.mem_neighborFinset _ _).mp hy
    apply ((TriangleContraction G S).mem_neighborFinset _ _).mpr
    by_cases yy : y∈S
    · simpa only [collapse,dif_pos yy] using
        (show (TriangleContraction G S).Adj (some x) none from ⟨y,yy,e.symm⟩)
    · simpa only [collapse,dif_neg yy] using
        (show (TriangleContraction G S).Adj (some x) (some ⟨y,yy⟩) from e)
  · intro u hu v hv eq
    by_cases uu : u∈S <;> by_cases vv : v∈S
    · exact unique u v uu vv ((G.mem_neighborFinset _ _).mp hu) ((G.mem_neighborFinset _ _).mp hv)
    · simp [collapse,uu,vv] at eq
    · simp [collapse,uu,vv] at eq
    · simpa [collapse,uu,vv] using eq
  · intro y hy
    have e := ((TriangleContraction G S).mem_neighborFinset _ _).mp hy
    cases y with
    | none =>
      obtain ⟨u,uu,eu⟩ := e
      exact ⟨u,(G.mem_neighborFinset _ _).mpr eu.symm,by simp [collapse,uu]⟩
    | some u =>
      exact ⟨u.val,(G.mem_neighborFinset _ _).mpr e,by simp [collapse,u.property]⟩

#print axioms triangle_contraction_connected
#print axioms external_degree_in_contraction
end Graffiti133TriangleCritical


namespace Graffiti133TriangleCritical
open SimpleGraph Finset Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem two_inside_triangle (a b c : V) (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) :
    (G.neighborFinset a \ ({a,b,c}:Finset V)).card +2=G.degree a := by
  have t : (G.neighborFinset a \ ({a,b,c}:Finset V)) = G.neighborFinset a \ ({b,c}:Finset V) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    exact ⟨fun ⟨mem,notm⟩ => ⟨mem,fun h=>notm (Or.inr h)⟩,
      fun ⟨mem,notm⟩ => ⟨mem, fun h=>h.elim
        (fun e=>G.loopless a (e ▸ (G.mem_neighborFinset a x).mp mem)) notm⟩⟩
  have sub : ({b,c}:Finset V)⊆G.neighborFinset a := by
    intro x hx
    rcases Finset.mem_insert.mp hx with e|q
    · subst x
      exact (G.mem_neighborFinset a b).mpr ab
    · have e := Finset.mem_singleton.mp q
      subst x
      exact (G.mem_neighborFinset a c).mpr ca.symm
  have e := Finset.card_sdiff_add_card_eq_card sub
  rw [G.card_neighborFinset_eq_degree] at e
  rw [t]
  simpa [bc.ne] using e

theorem triangle_hub_degree (h4 : FourCycleFree G)
    (a b c : V) (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) :
    (TriangleContraction G ({a,b,c}:Finset V)).degree none+6 =
      G.degree a+G.degree b+G.degree c := by
  classical
  let S : Finset V := {a,b,c}
  let U (x : V) := G.neighborFinset x \ S
  let J := TriangleContraction G S
  have ab' : Disjoint (U a) (U b) := by
    apply Finset.disjoint_left.mpr
    intro x ax bx
    exact ab.ne (triangle_single_external_neighbor G h4 a b c ab bc ca x
      (Finset.mem_sdiff.mp ax).2 a b (by simp [S]) (by simp [S])
      ((G.mem_neighborFinset a x).mp (Finset.mem_sdiff.mp ax).1).symm
      ((G.mem_neighborFinset b x).mp (Finset.mem_sdiff.mp bx).1).symm)
  have ac' : Disjoint (U a) (U c) := by
    apply Finset.disjoint_left.mpr
    intro x ax cx
    exact ca.ne.symm (triangle_single_external_neighbor G h4 a b c ab bc ca x
      (Finset.mem_sdiff.mp ax).2 a c (by simp [S]) (by simp [S])
      ((G.mem_neighborFinset a x).mp (Finset.mem_sdiff.mp ax).1).symm
      ((G.mem_neighborFinset c x).mp (Finset.mem_sdiff.mp cx).1).symm)
  have bc' : Disjoint (U b) (U c) := by
    apply Finset.disjoint_left.mpr
    intro x bx cx
    exact bc.ne (triangle_single_external_neighbor G h4 a b c ab bc ca x
      (Finset.mem_sdiff.mp bx).2 b c (by simp [S]) (by simp [S])
      ((G.mem_neighborFinset b x).mp (Finset.mem_sdiff.mp bx).1).symm
      ((G.mem_neighborFinset c x).mp (Finset.mem_sdiff.mp cx).1).symm)
  have member (x : V) : x∈U a ∪ U b ∪ U c ↔ x∉S ∧ ∃ z∈S,G.Adj z x := by
    simp only [Finset.mem_union,U,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ((⟨p,h⟩|⟨p,h⟩)|⟨p,h⟩)
      · exact ⟨h,a,by simp [S],p⟩
      · exact ⟨h,b,by simp [S],p⟩
      · exact ⟨h,c,by simp [S],p⟩
    · rintro ⟨h,z,zm,p⟩
      simp only [S,Finset.mem_insert,Finset.mem_singleton] at zm
      rcases zm with za|zb|zc
      · exact Or.inl (Or.inl ⟨za ▸ p,h⟩)
      · exact Or.inl (Or.inr ⟨zb ▸ p,h⟩)
      · exact Or.inr ⟨zc ▸ p,h⟩
  have cnt : (U a ∪ U b ∪ U c).card = J.degree none := by
    rw [←J.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun x _=>collapse S x)
    · intro x hx
      obtain ⟨xo,hx'⟩ := (member x).mp hx
      apply (J.mem_neighborFinset none _).mpr
      simpa only [collapse,dif_neg xo] using
        (show J.Adj none (some ⟨x,xo⟩) from hx')
    · intro x hx y hy eq
      have xo := ((member x).mp hx).1
      have yo := ((member y).mp hy).1
      simpa [collapse,xo,yo] using eq
    · intro y hy
      have p := (J.mem_neighborFinset none y).mp hy
      cases y with
      | none => exact (J.loopless _ p).elim
      | some y =>
        exact ⟨y.val,(member _).mpr ⟨y.property,p⟩,by simp [collapse,y.property]⟩
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨ac',bc'⟩),
    Finset.card_union_of_disjoint ab'] at cnt
  have da : (U a).card+2=G.degree a := two_inside_triangle G a b c ab bc ca
  have db : (U b).card+2=G.degree b := by
    have eq : ({b,c,a}:Finset V)=S := by ext x; simp [S,or_comm,or_left_comm]
    simpa only [eq,U] using two_inside_triangle G b c a bc ca ab
  have dc : (U c).card+2=G.degree c := by
    have eq : ({c,a,b}:Finset V)=S := by ext x; simp [S,or_comm,or_left_comm]
    simpa only [eq,U] using two_inside_triangle G c a b ca ab bc
  change J.degree none+6=_
  omega

#print axioms triangle_hub_degree
end Graffiti133TriangleCritical


namespace Graffiti133ExpandedTriangle
open SimpleGraph Finset Graffiti133 Graffiti133Bicycle Graffiti133TriangleCritical
open scoped Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def outsideVal {S : Finset V} (a : Option {x : V // x∉S}) (ne : a≠none) : {x : V // x∉S} :=
  match a with
  | none => False.elim (ne rfl)
  | some x => x

@[simp] theorem outsideVal_some {S : Finset V} (a : Option {x : V // x∉S}) (ne : a≠none) :
    some (outsideVal a ne)=a := by cases a with
  | none => contradiction
  | some x => rfl

def thetaInterior {S : Finset V} {w : {x : V // x∉S}}
    (P : ThetaRelays (TriangleContraction G S) none (some w)) (k : Fin 3)
    (i : Fin (P.rel k).n) : {x : V // x∉S} :=
  outsideVal ((P.rel k).f i) (fun e => (P.rel k).off i (by simp [e]))

theorem thetaInterior_ne_hub {S : Finset V} {w : {x : V // x∉S}}
    (P : ThetaRelays (TriangleContraction G S) none (some w)) (k : Fin 3)
    (i : Fin (P.rel k).n) : thetaInterior P k i ≠ w := by
  intro e
  have h := outsideVal_some ((P.rel k).f i) (fun ne => (P.rel k).off i (by simp [ne]))
  change some (thetaInterior P k i)=_ at h
  exact (P.rel k).off i (by rw [←h,e]; simp)

theorem thetaInterior_adj {S : Finset V} {w : {x : V // x∉S}}
    (P : ThetaRelays (TriangleContraction G S) none (some w)) (k l : Fin 3)
    (i : Fin (P.rel k).n) (j : Fin (P.rel l).n) :
    G.Adj (thetaInterior P k i).val (thetaInterior P l j).val ↔
    (TriangleContraction G S).Adj ((P.rel k).f i) ((P.rel l).f j) := by
  have hi : some (thetaInterior P k i)=(P.rel k).f i := outsideVal_some _ _
  have hj : some (thetaInterior P l j)=(P.rel l).f j := outsideVal_some _ _
  rw [← hi,← hj]
  rfl

theorem thetaInterior_len_le {S : Finset V} {w : {x : V // x∉S}}
    (P : ThetaRelays (TriangleContraction G S) none (some w))
    (no9 : ¬∃ p : Fin 9 → V, InducedPath G p) (k : Fin 3) : (P.rel k).n≤8 := by
  by_contra! bad
  apply no9
  have path : InducedPath G (fun i : Fin (P.rel k).n => (thetaInterior P k i).val) := by
    refine ⟨?_,fun i j lt=>(thetaInterior_adj P k k i j).trans ((P.rel k).path.2 i j lt)⟩
    intro i j h
    apply (P.rel k).path.1
    have hi : some (thetaInterior P k i)=(P.rel k).f i := outsideVal_some _ _
    have hj : some (thetaInterior P k j)=(P.rel k).f j := outsideVal_some _ _
    rw [←hi,←hj]
    exact congrArg some (Subtype.ext h)
  exact Graffiti133Revisit.trim_path (by omega) path

def thetaFirst {S : Finset V} {w : {x : V // x∉S}}
    (P : ThetaRelays (TriangleContraction G S) none (some w)) (k : Fin 3) : {x : V // x∉S} :=
  if h : 0<(P.rel k).n then thetaInterior P k ⟨0,h⟩ else w

theorem thetaFirst_adj {S : Finset V} {w : {x : V // x∉S}}
    (P : ThetaRelays (TriangleContraction G S) none (some w)) (k : Fin 3) :
    ∃ t∈S,G.Adj t (thetaFirst P k).val := by
  by_cases h : 0<(P.rel k).n
  · rw [thetaFirst,dif_pos h]
    have next := ((P.rel k).attached ⟨0,h⟩ none (by simp)).mpr (Or.inl ⟨rfl,rfl⟩)
    have eq : some (thetaInterior P k ⟨0,h⟩)=(P.rel k).f ⟨0,h⟩ := outsideVal_some _ _
    rw [←eq] at next
    exact next
  · rw [thetaFirst,dif_neg h]
    exact P.direct.mpr ⟨k,by omega⟩

theorem thetaFirst_injective {S : Finset V} {w : {x : V // x∉S}}
    (P : ThetaRelays (TriangleContraction G S) none (some w)) :
    Function.Injective (thetaFirst P) := by
  intro i j e
  by_cases hi : 0<(P.rel i).n <;> by_cases hj : 0<(P.rel j).n
  · by_contra ne
    apply (P.sep i j ne ⟨0,hi⟩ ⟨0,hj⟩).1
    have ai : some (thetaInterior P i ⟨0,hi⟩)=(P.rel i).f ⟨0,hi⟩ := outsideVal_some _ _
    have aj : some (thetaInterior P j ⟨0,hj⟩)=(P.rel j).f ⟨0,hj⟩ := outsideVal_some _ _
    rw [←ai,←aj]
    exact congrArg some (by simpa only [thetaFirst,dif_pos hi,dif_pos hj] using e)
  · exact (thetaInterior_ne_hub P i ⟨0,hi⟩
      (by simpa only [thetaFirst,dif_pos hi,dif_neg hj] using e)).elim
  · exact (thetaInterior_ne_hub P j ⟨0,hj⟩
      (by simpa only [thetaFirst,dif_pos hj,dif_neg hi] using e.symm)).elim
  · exact P.atMostOneEmpty i j (by omega) (by omega)

#print axioms thetaInterior_len_le
#print axioms thetaFirst_adj
#print axioms thetaFirst_injective
end Graffiti133ExpandedTriangle


namespace Graffiti133ExpandedTriangle
open SimpleGraph Finset Graffiti133 Graffiti133Bicycle Graffiti133TriangleCritical
open scoped Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

abbrev ExpandedIndex (sz : Fin 3→Nat) := Sum (Option (Fin 3)) (Σ k : Fin 3, Fin (sz k))

def expandedThetaAdj (sz : Fin 3→Nat) : ExpandedIndex sz → ExpandedIndex sz → Prop
  | .inl (some k), .inl (some l) => k≠l
  | .inl (some k), .inl none | .inl none, .inl (some k) => sz k=0
  | .inl none,.inl none => False
  | .inl (some l), .inr ⟨k,i⟩ | .inr ⟨k,i⟩, .inl (some l) => k=l ∧ i.val=0
  | .inl none, .inr ⟨k,i⟩ | .inr ⟨k,i⟩, .inl none => i.val+1=sz k
  | .inr ⟨k,i⟩, .inr ⟨l,j⟩ => k=l ∧ (i.val+1=j.val ∨ j.val+1=i.val)

instance (sz : Fin 3→Nat) (x y : ExpandedIndex sz) : Decidable (expandedThetaAdj sz x y) := by
  cases x with
  | inl x => cases x <;> cases y with
    | inl y => cases y <;> unfold expandedThetaAdj <;> infer_instance
    | inr y => rcases y with ⟨k,i⟩; unfold expandedThetaAdj; infer_instance
  | inr x =>
    rcases x with ⟨k,i⟩
    cases y with
    | inl y => cases y <;> unfold expandedThetaAdj <;> infer_instance
    | inr y => rcases y with ⟨l,j⟩; unfold expandedThetaAdj; infer_instance

def expandThetaVertex {S : Finset V} {w : {x : V // x∉S}}
    (P : ThetaRelays (TriangleContraction G S) none (some w)) (t : Fin 3→V) :
    ExpandedIndex P.network.sizes → V
  | .inl (some k) => t k
  | .inl none => w.val
  | .inr ⟨k,i⟩ => (thetaInterior P k i).val

private theorem interior_pos {S : Finset V} {w : {x : V // x∉S}}
    (P : ThetaRelays (TriangleContraction G S) none (some w))
    (k : Fin 3) (i : Fin (P.rel k).n) : 0<(P.rel k).n := by have := i.isLt; omega

theorem expandThetaVertex_inj {S : Finset V} {w : {x : V // x∉S}}
    (P : ThetaRelays (TriangleContraction G S) none (some w)) (t : Fin 3→V)
    (ts : ∀ k,t k∈S) (ti : Function.Injective t) :
    Function.Injective (expandThetaVertex P t) := by
  rintro (a|⟨k,i⟩) (b|⟨l,j⟩) eq
  · cases a <;> cases b
    · rfl
    · rename_i z
      change w.val=t z at eq
      exact (w.property (Eq.mp (congrArg (fun x=>x∈S) eq.symm) (ts z))).elim
    · rename_i z
      change t z=w.val at eq
      exact (w.property (Eq.mp (congrArg (fun x=>x∈S) eq) (ts z))).elim
    · exact congrArg Sum.inl (congrArg some (ti eq))
  · cases a
    · exact (thetaInterior_ne_hub P l j (Subtype.ext eq.symm)).elim
    · rename_i z
      change t z=(thetaInterior P l j).val at eq
      exact ((thetaInterior P l j).property (Eq.mp (congrArg (fun x=>x∈S) eq) (ts z))).elim
  · cases b
    · exact (thetaInterior_ne_hub P k i (Subtype.ext eq)).elim
    · rename_i z
      change (thetaInterior P k i).val=t z at eq
      exact ((thetaInterior P k i).property (Eq.mp (congrArg (fun x=>x∈S) eq.symm) (ts z))).elim
  · have he : (P.rel k).f i=(P.rel l).f j := by
      rw [←outsideVal_some ((P.rel k).f i) (fun e => (P.rel k).off i (by simp [e])),
        ←outsideVal_some ((P.rel l).f j) (fun e => (P.rel l).off j (by simp [e]))]
      exact congrArg some (Subtype.ext eq)
    by_cases kl : k=l
    · subst l
      have e := (P.rel k).path.1 he
      subst j
      rfl
    · exact ((P.sep k l kl i j).1 he).elim

theorem expandThetaVertex_adj {S : Finset V} {w : {x : V // x∉S}}
    (P : ThetaRelays (TriangleContraction G S) none (some w)) (t : Fin 3→V)
    (ts : ∀ k,t k∈S) (ti : Function.Injective t)
    (tc : ∀ k l,k≠l → G.Adj (t k) (t l))
    (port : ∀ k,G.Adj (t k) (thetaFirst P k).val)
    (unique : ∀ x∉S,∀ a b,a∈S→b∈S→G.Adj a x→G.Adj b x→a=b)
    (i j : ExpandedIndex P.network.sizes) :
    G.Adj (expandThetaVertex P t i) (expandThetaVertex P t j) ↔
      expandedThetaAdj P.network.sizes i j := by
  have head (l k : Fin 3) (i : Fin (P.rel k).n) :
      G.Adj (t l) (thetaInterior P k i).val ↔ k=l ∧ i.val=0 := by
    have e : some (thetaInterior P k i)=(P.rel k).f i := outsideVal_some _ _
    have hit := (P.rel k).attached i none (by simp)
    rw [←e] at hit
    change (∃ a∈S,G.Adj a (thetaInterior P k i).val) ↔ _ at hit
    constructor
    · intro edge
      have ind : i.val=0 := by
        rcases hit.mp ⟨t l,ts _,edge⟩ with hh|hh
        · exact hh.1
        · cases hh.2
      have pos := interior_pos P k i
      have iz : i=(⟨0,pos⟩:Fin (P.rel k).n) := Fin.ext ind
      have tk := port k
      rw [thetaFirst,dif_pos pos,←iz] at tk
      exact ⟨ti (unique _ (thetaInterior P k i).property _ _ (ts k) (ts l) tk edge),ind⟩
    · rintro ⟨rfl,h⟩
      have pos := interior_pos P k i
      have iz : i=(⟨0,pos⟩:Fin (P.rel k).n) := Fin.ext h
      simpa only [thetaFirst,dif_pos pos,←iz] using port k
  have tail (k : Fin 3) (i : Fin (P.rel k).n) :
      G.Adj w.val (thetaInterior P k i).val ↔ i.val+1=(P.rel k).n := by
    have e : some (thetaInterior P k i)=(P.rel k).f i := outsideVal_some _ _
    have hit := (P.rel k).attached i (some w) (by simp)
    rw [←e] at hit
    simpa using hit
  have direct (k : Fin 3) : G.Adj (t k) w.val ↔ (P.rel k).n=0 := by
    constructor
    · intro ed
      obtain ⟨l,el⟩ := P.direct.mp ⟨t k,ts k,ed⟩
      have lw := port l
      rw [thetaFirst,dif_neg (by omega : ¬0<(P.rel l).n)] at lw
      have eq := ti (unique _ w.property _ _ (ts k) (ts l) ed lw)
      simpa [eq] using el
    · intro e
      simpa only [thetaFirst,dif_neg (by omega : ¬0<(P.rel k).n)] using port k
  rcases i with a|⟨k,i⟩ <;> rcases j with b|⟨l,j⟩
  · cases a with
    | none =>
      cases b with
      | none => exact ⟨G.loopless _,False.elim⟩
      | some l => exact (G.adj_comm _ _).trans (direct l)
    | some k =>
      cases b with
      | none => exact direct k
      | some l => exact ⟨fun h kl=>h.ne (congrArg t kl),tc k l⟩
  · cases a with
    | none => exact tail l j
    | some k => exact head k l j
  · cases b with
    | none => exact (G.adj_comm _ _).trans (tail k i)
    | some l => exact (G.adj_comm _ _).trans (head l k i)
  · change G.Adj (thetaInterior P k i).val (thetaInterior P l j).val ↔ _
    rw [thetaInterior_adj]
    by_cases kl : k=l
    · subst l
      simpa [expandedThetaAdj,ThetaRelays.network,TripleNetwork.sizes] using
        induced_adj_both_orders (P.rel k).path i j
    · exact ⟨fun e=>((P.sep k l kl i j).2 e).elim,fun h=>(kl h.1).elim⟩

#print axioms expandThetaVertex_inj
#print axioms expandThetaVertex_adj
end Graffiti133ExpandedTriangle


namespace Graffiti133ExpandedTriangle
open SimpleGraph Finset Graffiti133 Graffiti133Bicycle Graffiti133TriangleCritical
open scoped Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem one_port (h b c : V) (hb : G.Adj h b) (hc : G.Adj h c) (ne : b≠c)
    (degree : G.degree h=3)
    (x y : V) (xb : x≠b) (xc : x≠c) (yb : y≠b) (yc : y≠c)
    (hx : G.Adj h x) (hy : G.Adj h y) : x=y := by
  have subset : ({b,c}:Finset V)⊆G.neighborFinset h := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl
    · exact (G.mem_neighborFinset h _).mpr hb
    · exact (G.mem_neighborFinset h _).mpr hc
  let T := G.neighborFinset h \ ({b,c}:Finset V)
  have card : T.card=1 := by
    have e := Finset.card_sdiff_add_card_eq_card subset
    rw [G.card_neighborFinset_eq_degree,degree] at e
    simpa [T,ne] using (show (G.neighborFinset h \ ({b,c}:Finset V)).card=1 by
      have card₂ : ({b,c}:Finset V).card=2 := by simp [ne]
      omega)
  have xT : x∈T := Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset h x).mpr hx,by simp [xb,xc]⟩
  have yT : y∈T := Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset h y).mpr hy,by simp [yb,yc]⟩
  obtain ⟨t,te⟩ := Finset.card_eq_one.mp card
  rw [te] at xT yT
  exact (Finset.mem_singleton.mp xT).trans (Finset.mem_singleton.mp yT).symm

theorem degree_three_triangle_has_unique_port
    (a b c : V) (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a)
    (da : G.degree a=3) (db : G.degree b=3) (dc : G.degree c=3)
    (h x y : V) (hh : h∈({a,b,c}:Finset V)) (xo : x∉({a,b,c}:Finset V)) (yo : y∉({a,b,c}:Finset V))
    (hx : G.Adj h x) (hy : G.Adj h y) : x=y := by
  have xa : x≠a := fun e=>xo (by simp [e])
  have xb : x≠b := fun e=>xo (by simp [e])
  have xc : x≠c := fun e=>xo (by simp [e])
  have ya : y≠a := fun e=>yo (by simp [e])
  have yb : y≠b := fun e=>yo (by simp [e])
  have yc : y≠c := fun e=>yo (by simp [e])
  simp only [Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with e|e|e <;> subst h
  · exact one_port a b c ab ca.symm bc.ne da x y xb xc yb yc hx hy
  · exact one_port b a c ab.symm bc ca.ne.symm db x y xa xc ya yc hx hy
  · exact one_port c a b ca bc.symm ab.ne dc x y xa xb ya yb hx hy

theorem choose_theta_triangle_ports
    (a b c : V) (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a)
    (da : G.degree a=3) (db : G.degree b=3) (dc : G.degree c=3)
    {w : {x : V // x∉({a,b,c}:Finset V)}}
    (P : ThetaRelays (TriangleContraction G ({a,b,c}:Finset V)) none (some w)) :
    ∃ t : Fin 3→V, (∀ k,t k∈({a,b,c}:Finset V)) ∧ Function.Injective t ∧
      (∀ k l,k≠l → G.Adj (t k) (t l)) ∧ (∀ k,G.Adj (t k) (thetaFirst P k).val) := by
  choose t tm tp using thetaFirst_adj P
  have ti : Function.Injective t := by
    intro k l e
    apply thetaFirst_injective P
    apply Subtype.ext
    exact degree_three_triangle_has_unique_port a b c ab bc ca da db dc _ _ _
      (tm k) (thetaFirst P k).property (thetaFirst P l).property (tp k) (e.symm ▸ tp l)
  have e (x y : V) (hx : x∈({a,b,c}:Finset V)) (hy : y∈({a,b,c}:Finset V)) (ne : x≠y) :
      G.Adj x y := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with h|h|h <;> subst x <;> rcases hy with h|h|h <;> subst y
    all_goals first | contradiction | exact ab | exact ab.symm | exact bc | exact bc.symm | exact ca | exact ca.symm
  exact ⟨t,tm,ti,fun k l ne=>e _ _ (tm k) (tm l) (ti.ne ne),tp⟩

#print axioms choose_theta_triangle_ports
end Graffiti133ExpandedTriangle


namespace Graffiti133ExpandedTriangle
open Graffiti133 Graffiti133Bicycle
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def numTheta (a b c : Nat) (i : Fin (4+a+b+c)) : ExpandedIndex (sizeVec a b c) :=
  if h : i.val<3 then .inl (some ⟨i.val,h⟩) else
  if h3 : i.val=3 then .inl none else
  if h : i.val<4+a then .inr ⟨0,⟨i.val-4,by change i.val-4<a; omega⟩⟩ else
  if h : i.val<4+a+b then .inr ⟨1,⟨i.val-(4+a),by change i.val-(4+a)<b; omega⟩⟩ else
  .inr ⟨2,⟨i.val-(4+a+b),by change i.val-(4+a+b)<c; omega⟩⟩

def numThetaAdj (a b c : Nat) (i j : Fin (4+a+b+c)) :=
  expandedThetaAdj (sizeVec a b c) (numTheta a b c i) (numTheta a b c j)

instance (a b c : Nat) (i j : Fin (4+a+b+c)) : Decidable (numThetaAdj a b c i j) := by
  unfold numThetaAdj
  infer_instance

def atlasGood : List (Nat×Nat×Nat) := [(1,1,1),(1,1,2),(1,1,3),(1,1,4),(1,2,2),(1,2,3),(2,2,2),(0,2,2),(0,2,3),(0,2,4),(0,3,3)]

def atlasData : List ((Nat×Nat×Nat)×List Nat) := [
 ((1,1,5),[1,0,1,5,3,10,9,8,7,6]),
 ((1,1,6),[1,0,1,5,3,11,10,9,8,7]),
 ((1,1,7),[1,0,1,5,3,12,11,10,9,8]),
 ((1,1,8),[1,0,1,5,3,13,12,11,10,9]),
 ((1,2,4),[1,0,1,5,6,3,10,9,8,7]),
 ((1,2,5),[1,0,1,5,6,3,11,10,9,8]),
 ((1,2,6),[1,0,1,5,6,3,12,11,10,9]),
 ((1,2,7),[1,0,1,5,6,3,13,12,11,10]),
 ((1,2,8),[1,0,1,5,6,3,14,13,12,11]),
 ((1,3,3),[1,0,1,5,6,7,3,10,9,8]),
 ((1,3,4),[1,0,1,5,6,7,3,11,10,9]),
 ((1,3,5),[1,0,1,5,6,7,3,12,11,10]),
 ((1,3,6),[1,0,1,5,6,7,3,13,12,11]),
 ((1,3,7),[1,0,1,5,6,7,3,14,13,12]),
 ((1,3,8),[1,0,1,5,6,7,3,15,14,13]),
 ((1,4,4),[1,0,1,5,6,7,8,3,12,11]),
 ((1,4,5),[1,0,1,5,6,7,8,3,13,12]),
 ((1,4,6),[1,0,1,5,6,7,8,3,14,13]),
 ((1,4,7),[1,0,1,5,6,7,8,3,15,14]),
 ((1,4,8),[1,0,1,5,6,7,8,3,16,15]),
 ((1,5,5),[1,0,1,5,6,7,8,9,3,14]),
 ((1,5,6),[1,0,1,5,6,7,8,9,3,15]),
 ((1,5,7),[1,0,1,5,6,7,8,9,3,16]),
 ((1,5,8),[1,0,1,5,6,7,8,9,3,17]),
 ((1,6,6),[1,0,1,5,6,7,8,9,10,3]),
 ((1,6,7),[1,0,1,5,6,7,8,9,10,3]),
 ((1,6,8),[1,0,1,5,6,7,8,9,10,3]),
 ((1,7,7),[1,0,1,5,6,7,8,9,10,11]),
 ((1,7,8),[1,0,1,5,6,7,8,9,10,11]),
 ((1,8,8),[1,0,1,5,6,7,8,9,10,11]),
 ((2,2,3),[1,4,0,1,6,7,3,10,9,8]),
 ((2,2,4),[1,0,1,6,7,3,11,10,9,8]),
 ((2,2,5),[1,0,1,6,7,3,12,11,10,9]),
 ((2,2,6),[1,0,1,6,7,3,13,12,11,10]),
 ((2,2,7),[1,0,1,6,7,3,14,13,12,11]),
 ((2,2,8),[1,0,1,6,7,3,15,14,13,12]),
 ((2,3,3),[1,0,1,6,7,8,3,11,10,9]),
 ((2,3,4),[1,0,1,6,7,8,3,12,11,10]),
 ((2,3,5),[1,0,1,6,7,8,3,13,12,11]),
 ((2,3,6),[1,0,1,6,7,8,3,14,13,12]),
 ((2,3,7),[1,0,1,6,7,8,3,15,14,13]),
 ((2,3,8),[1,0,1,6,7,8,3,16,15,14]),
 ((2,4,4),[1,0,1,6,7,8,9,3,13,12]),
 ((2,4,5),[1,0,1,6,7,8,9,3,14,13]),
 ((2,4,6),[1,0,1,6,7,8,9,3,15,14]),
 ((2,4,7),[1,0,1,6,7,8,9,3,16,15]),
 ((2,4,8),[1,0,1,6,7,8,9,3,17,16]),
 ((2,5,5),[1,0,1,6,7,8,9,10,3,5]),
 ((2,5,6),[1,0,1,6,7,8,9,10,3,5]),
 ((2,5,7),[1,0,1,6,7,8,9,10,3,5]),
 ((2,5,8),[1,0,1,6,7,8,9,10,3,5]),
 ((2,6,6),[1,0,1,6,7,8,9,10,11,3]),
 ((2,6,7),[1,0,1,6,7,8,9,10,11,3]),
 ((2,6,8),[1,0,1,6,7,8,9,10,11,3]),
 ((2,7,7),[1,0,1,6,7,8,9,10,11,12]),
 ((2,7,8),[1,0,1,6,7,8,9,10,11,12]),
 ((2,8,8),[1,0,1,6,7,8,9,10,11,12]),
 ((3,3,3),[1,0,1,7,8,9,3,12,11,10]),
 ((3,3,4),[1,0,1,7,8,9,3,13,12,11]),
 ((3,3,5),[1,0,1,7,8,9,3,14,13,12]),
 ((3,3,6),[1,0,1,7,8,9,3,15,14,13]),
 ((3,3,7),[1,0,1,7,8,9,3,16,15,14]),
 ((3,3,8),[1,0,1,7,8,9,3,17,16,15]),
 ((3,4,4),[1,0,1,7,8,9,10,3,6,5]),
 ((3,4,5),[1,0,1,7,8,9,10,3,6,5]),
 ((3,4,6),[1,0,1,7,8,9,10,3,6,5]),
 ((3,4,7),[1,0,1,7,8,9,10,3,6,5]),
 ((3,4,8),[1,0,1,7,8,9,10,3,6,5]),
 ((3,5,5),[1,0,1,7,8,9,10,11,3,6]),
 ((3,5,6),[1,0,1,7,8,9,10,11,3,6]),
 ((3,5,7),[1,0,1,7,8,9,10,11,3,6]),
 ((3,5,8),[1,0,1,7,8,9,10,11,3,6]),
 ((3,6,6),[1,0,1,7,8,9,10,11,12,3]),
 ((3,6,7),[1,0,1,7,8,9,10,11,12,3]),
 ((3,6,8),[1,0,1,7,8,9,10,11,12,3]),
 ((3,7,7),[1,0,1,7,8,9,10,11,12,13]),
 ((3,7,8),[1,0,1,7,8,9,10,11,12,13]),
 ((3,8,8),[1,0,1,7,8,9,10,11,12,13]),
 ((4,4,4),[1,0,1,8,9,10,11,3,7,6]),
 ((4,4,5),[1,0,1,8,9,10,11,3,7,6]),
 ((4,4,6),[1,0,1,8,9,10,11,3,7,6]),
 ((4,4,7),[1,0,1,8,9,10,11,3,7,6]),
 ((4,4,8),[1,0,1,8,9,10,11,3,7,6]),
 ((4,5,5),[1,0,1,8,9,10,11,12,3,7]),
 ((4,5,6),[1,0,1,8,9,10,11,12,3,7]),
 ((4,5,7),[1,0,1,8,9,10,11,12,3,7]),
 ((4,5,8),[1,0,1,8,9,10,11,12,3,7]),
 ((4,6,6),[1,0,1,8,9,10,11,12,13,3]),
 ((4,6,7),[1,0,1,8,9,10,11,12,13,3]),
 ((4,6,8),[1,0,1,8,9,10,11,12,13,3]),
 ((4,7,7),[1,0,1,8,9,10,11,12,13,14]),
 ((4,7,8),[1,0,1,8,9,10,11,12,13,14]),
 ((4,8,8),[1,0,1,8,9,10,11,12,13,14]),
 ((5,5,5),[1,0,1,9,10,11,12,13,3,8]),
 ((5,5,6),[1,0,1,9,10,11,12,13,3,8]),
 ((5,5,7),[1,0,1,9,10,11,12,13,3,8]),
 ((5,5,8),[1,0,1,9,10,11,12,13,3,8]),
 ((5,6,6),[1,0,1,9,10,11,12,13,14,3]),
 ((5,6,7),[1,0,1,9,10,11,12,13,14,3]),
 ((5,6,8),[1,0,1,9,10,11,12,13,14,3]),
 ((5,7,7),[1,0,1,9,10,11,12,13,14,15]),
 ((5,7,8),[1,0,1,9,10,11,12,13,14,15]),
 ((5,8,8),[1,0,1,9,10,11,12,13,14,15]),
 ((6,6,6),[1,0,1,10,11,12,13,14,15,3]),
 ((6,6,7),[1,0,1,10,11,12,13,14,15,3]),
 ((6,6,8),[1,0,1,10,11,12,13,14,15,3]),
 ((6,7,7),[1,0,1,10,11,12,13,14,15,16]),
 ((6,7,8),[1,0,1,10,11,12,13,14,15,16]),
 ((6,8,8),[1,0,1,10,11,12,13,14,15,16]),
 ((7,7,7),[1,0,1,11,12,13,14,15,16,17]),
 ((7,7,8),[1,0,1,11,12,13,14,15,16,17]),
 ((7,8,8),[1,0,1,11,12,13,14,15,16,17]),
 ((8,8,8),[1,0,1,12,13,14,15,16,17,18]),
 ((0,0,0),[0,1,0,2,3]),
 ((0,0,1),[0,1,0,2,3]),
 ((0,0,2),[0,1,0,2,3]),
 ((0,0,3),[0,1,0,2,3]),
 ((0,0,4),[0,1,0,2,3]),
 ((0,0,5),[0,1,0,2,3]),
 ((0,0,6),[0,1,0,2,3]),
 ((0,0,7),[0,1,0,2,3]),
 ((0,0,8),[0,1,0,2,3]),
 ((0,1,1),[0,3,1,0,4]),
 ((0,1,2),[0,3,1,0,4]),
 ((0,1,3),[0,3,1,0,4]),
 ((0,1,4),[0,3,1,0,4]),
 ((0,1,5),[0,3,1,0,4]),
 ((0,1,6),[0,3,1,0,4]),
 ((0,1,7),[0,3,1,0,4]),
 ((0,1,8),[0,3,1,0,4]),
 ((0,2,5),[1,1,2,6,7,8,9,10,3,5]),
 ((0,2,6),[1,1,0,3,11,10,9,8,7,6]),
 ((0,2,7),[1,0,2,6,7,8,9,10,11,12]),
 ((0,2,8),[1,0,2,6,7,8,9,10,11,12]),
 ((0,3,4),[1,1,2,7,8,9,10,3,6,5]),
 ((0,3,5),[1,1,2,7,8,9,10,11,3,6]),
 ((0,3,6),[1,1,0,3,12,11,10,9,8,7]),
 ((0,3,7),[1,0,2,7,8,9,10,11,12,13]),
 ((0,3,8),[1,0,2,7,8,9,10,11,12,13]),
 ((0,4,4),[1,1,2,8,9,10,11,3,7,6]),
 ((0,4,5),[1,1,2,8,9,10,11,12,3,7]),
 ((0,4,6),[1,1,0,3,13,12,11,10,9,8]),
 ((0,4,7),[1,0,2,8,9,10,11,12,13,14]),
 ((0,4,8),[1,0,2,8,9,10,11,12,13,14]),
 ((0,5,5),[1,1,2,9,10,11,12,13,3,8]),
 ((0,5,6),[1,1,0,3,14,13,12,11,10,9]),
 ((0,5,7),[1,0,2,9,10,11,12,13,14,15]),
 ((0,5,8),[1,0,2,9,10,11,12,13,14,15]),
 ((0,6,6),[1,1,0,3,15,14,13,12,11,10]),
 ((0,6,7),[1,0,2,10,11,12,13,14,15,16]),
 ((0,6,8),[1,0,2,10,11,12,13,14,15,16]),
 ((0,7,7),[1,0,1,4,5,6,7,8,9,10]),
 ((0,7,8),[1,0,1,4,5,6,7,8,9,10]),
 ((0,8,8),[1,0,1,4,5,6,7,8,9,10])
]

def idx (a b c i : Nat) : Fin (4+a+b+c) := ⟨i%(4+a+b+c),Nat.mod_lt _ (by omega)⟩

def atlasRejects (a b c : Nat) : List Nat → Prop
  | [0,i,j,x,y] =>
      numTheta a b c (idx a b c i)≠numTheta a b c (idx a b c j) ∧
      numTheta a b c (idx a b c x)≠numTheta a b c (idx a b c y) ∧
      numThetaAdj a b c (idx a b c i) (idx a b c x) ∧
      numThetaAdj a b c (idx a b c j) (idx a b c x) ∧
      numThetaAdj a b c (idx a b c i) (idx a b c y) ∧
      numThetaAdj a b c (idx a b c j) (idx a b c y)
  | 1::L =>
      (∀ i j : Fin 9, numTheta a b c (idx a b c (L.getD i.val 0)) =
        numTheta a b c (idx a b c (L.getD j.val 0)) → i=j) ∧
      ∀ i j : Fin 9, i<j →
        (numThetaAdj a b c (idx a b c (L.getD i.val 0)) (idx a b c (L.getD j.val 0)) ↔ i.val+1=j.val)
  | _ => False

instance (a b c : Nat) (L : List Nat) : Decidable (atlasRejects a b c L) := by
  unfold atlasRejects
  split <;> infer_instance

def atlasLookup (a b c : Nat) : List Nat :=
  atlasData.lookup (a,b,c) |>.getD []

theorem atlas_checked : ∀ a b c : Fin 9, a≤b → b≤c →
    (a.val,b.val,c.val)∈atlasGood ∨ atlasRejects a.val b.val c.val (atlasLookup a.val b.val c.val) := by
  decide

theorem atlas_rejection_lift {V : Type*} {G : SimpleGraph V} (a b c : Nat)
    (f : ExpandedIndex (sizeVec a b c)→V) (fi : Function.Injective f)
    (edge : ∀ x y, G.Adj (f x) (f y) ↔ expandedThetaAdj _ x y)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (L : List Nat) (bad : atlasRejects a b c L) : False := by
  unfold atlasRejects at bad
  split at bad
  · obtain ⟨ne,ne2,ac,bc,ad,bd⟩ := bad
    exact ne2 (fi (h4 _ _ _ _ (fi.ne ne) ((edge _ _).mpr ac) ((edge _ _).mpr bc)
      ((edge _ _).mpr ad) ((edge _ _).mpr bd)))
  · exact h9 ⟨_, fun i j e=>bad.1 i j (fi e),fun i j lt=>(edge _ _).trans (bad.2 i j lt)⟩
  · exact bad

#print axioms atlas_checked
#print axioms atlas_rejection_lift
end Graffiti133ExpandedTriangle


namespace Graffiti133ExpandedTriangle
open SimpleGraph Graffiti133 Graffiti133NoFive Graffiti133Bicycle
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem good_theta_model_has_nine (a b c : Nat) (key : (a,b,c)∈atlasGood)
    (f : ExpandedIndex (sizeVec a b c) → V)
    (fi : Function.Injective f)
    (adj : ∀ i j,G.Adj (f i) (f j) ↔ expandedThetaAdj _ i j)
    (H : Hole G 7) (h4 : FourCycleFree G)
    (out : ∀ x, Outside H.c (f x))
    (singleton : ∀ x, ∃ k,∀ j,G.Adj (f x) (H.c j) ↔ k=j) :
    ∃ p : Fin 9→V,InducedPath G p := by
  choose site attach using singleton
  simp only [atlasGood,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at key
  rcases key with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  · let num := numTheta 1 1 1
    have ni : ∀ i j : Fin 7, num i=num j → i=j := by decide
    have nr : ∀ i j : Fin 7, expandedThetaAdj _ (num i) (num j) ↔
        bit Triangle0222.canonicalRows i.val j.val=true := by decide
    exact Triangle0222.extension H h4 (f ∘ num) (fi.comp (fun _ _ => ni _ _))
      (fun i=>out (num i)) (site ∘ num) (fun i=>attach (num i))
      (fun i j=>(adj _ _).trans (nr i j))
  · let num := numTheta 1 1 2
    have ni : ∀ i j : Fin 8, num i=num j → i=j := by decide
    have nr : ∀ i j : Fin 8, expandedThetaAdj _ (num i) (num j) ↔
        bit Triangle0223.canonicalRows i.val j.val=true := by decide
    exact Triangle0223.extension H h4 (f ∘ num) (fi.comp (fun _ _ => ni _ _))
      (fun i=>out (num i)) (site ∘ num) (fun i=>attach (num i))
      (fun i j=>(adj _ _).trans (nr i j))
  · let num := numTheta 1 1 3
    have ni : ∀ i j : Fin 9, num i=num j → i=j := by decide
    have nr : ∀ i j : Fin 9, expandedThetaAdj _ (num i) (num j) ↔
        bit Triangle0224.canonicalRows i.val j.val=true := by decide
    exact Triangle0224.extension H h4 (f ∘ num) (fi.comp (fun _ _ => ni _ _))
      (fun i=>out (num i)) (site ∘ num) (fun i=>attach (num i))
      (fun i j=>(adj _ _).trans (nr i j))
  · let num := numTheta 1 1 4
    have ni : ∀ i j : Fin 10, num i=num j → i=j := by decide
    have nr : ∀ i j : Fin 10, expandedThetaAdj _ (num i) (num j) ↔
        bit Triangle0225.canonicalRows i.val j.val=true := by decide
    exact Triangle0225.extension H h4 (f ∘ num) (fi.comp (fun _ _ => ni _ _))
      (fun i=>out (num i)) (site ∘ num) (fun i=>attach (num i))
      (fun i j=>(adj _ _).trans (nr i j))
  · let num := numTheta 1 2 2
    have ni : ∀ i j : Fin 9, num i=num j → i=j := by decide
    have nr : ∀ i j : Fin 9, expandedThetaAdj _ (num i) (num j) ↔
        bit Triangle0233.canonicalRows i.val j.val=true := by decide
    exact Triangle0233.extension H h4 (f ∘ num) (fi.comp (fun _ _ => ni _ _))
      (fun i=>out (num i)) (site ∘ num) (fun i=>attach (num i))
      (fun i j=>(adj _ _).trans (nr i j))
  · let num := numTheta 1 2 3
    have ni : ∀ i j : Fin 10, num i=num j → i=j := by decide
    have nr : ∀ i j : Fin 10, expandedThetaAdj _ (num i) (num j) ↔
        bit Triangle0234.canonicalRows i.val j.val=true := by decide
    exact Triangle0234.extension H h4 (f ∘ num) (fi.comp (fun _ _ => ni _ _))
      (fun i=>out (num i)) (site ∘ num) (fun i=>attach (num i))
      (fun i j=>(adj _ _).trans (nr i j))
  · let num := numTheta 2 2 2
    have ni : ∀ i j : Fin 10, num i=num j → i=j := by decide
    have nr : ∀ i j : Fin 10, expandedThetaAdj _ (num i) (num j) ↔
        bit Triangle0333.canonicalRows i.val j.val=true := by decide
    exact Triangle0333.extension H h4 (f ∘ num) (fi.comp (fun _ _ => ni _ _))
      (fun i=>out (num i)) (site ∘ num) (fun i=>attach (num i))
      (fun i j=>(adj _ _).trans (nr i j))
  · let num := numTheta 0 2 2
    have ni : ∀ i j : Fin 8, num i=num j → i=j := by decide
    have nr : ∀ i j : Fin 8, expandedThetaAdj _ (num i) (num j) ↔
        bit Triangle0133.canonicalRows i.val j.val=true := by decide
    exact Triangle0133.extension H h4 (f ∘ num) (fi.comp (fun _ _ => ni _ _))
      (fun i=>out (num i)) (site ∘ num) (fun i=>attach (num i))
      (fun i j=>(adj _ _).trans (nr i j))
  · let num := numTheta 0 2 3
    have ni : ∀ i j : Fin 9, num i=num j → i=j := by decide
    have nr : ∀ i j : Fin 9, expandedThetaAdj _ (num i) (num j) ↔
        bit Triangle0134.canonicalRows i.val j.val=true := by decide
    exact Triangle0134.extension H h4 (f ∘ num) (fi.comp (fun _ _ => ni _ _))
      (fun i=>out (num i)) (site ∘ num) (fun i=>attach (num i))
      (fun i j=>(adj _ _).trans (nr i j))
  · let num := numTheta 0 2 4
    have ni : ∀ i j : Fin 10, num i=num j → i=j := by decide
    have nr : ∀ i j : Fin 10, expandedThetaAdj _ (num i) (num j) ↔
        bit Triangle0135.canonicalRows i.val j.val=true := by decide
    exact Triangle0135.extension H h4 (f ∘ num) (fi.comp (fun _ _ => ni _ _))
      (fun i=>out (num i)) (site ∘ num) (fun i=>attach (num i))
      (fun i j=>(adj _ _).trans (nr i j))
  · let num := numTheta 0 3 3
    have ni : ∀ i j : Fin 10, num i=num j → i=j := by decide
    have nr : ∀ i j : Fin 10, expandedThetaAdj _ (num i) (num j) ↔
        bit Triangle0144.canonicalRows i.val j.val=true := by decide
    exact Triangle0144.extension H h4 (f ∘ num) (fi.comp (fun _ _ => ni _ _))
      (fun i=>out (num i)) (site ∘ num) (fun i=>attach (num i))
      (fun i j=>(adj _ _).trans (nr i j))

#print axioms good_theta_model_has_nine
end Graffiti133ExpandedTriangle


namespace Graffiti133ExpandedTriangle
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Bicycle Graffiti133TriangleCritical
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem arrange_three (d : Fin 3 → Nat) :
    ∃ e : Fin 3 ≃ Fin 3, d (e 0)≤d (e 1) ∧ d (e 1)≤d (e 2) := by
  let E01 := Equiv.swap (0:Fin 3) 1
  let E02 := Equiv.swap (0:Fin 3) 2
  let E12 := Equiv.swap (1:Fin 3) 2
  by_cases a : d 0≤d 1
  · by_cases b : d 1≤d 2
    · exact ⟨Equiv.refl _,a,b⟩
    · by_cases c : d 0≤d 2
      · exact ⟨E12,c,by change d 2≤d 1; omega⟩
      · exact ⟨E02.trans E01,by change d 2≤d 0; omega,by change d 0≤d 1; exact a⟩
  · by_cases c : d 0≤d 2
    · exact ⟨E01,by change d 1≤d 0; omega,c⟩
    · by_cases b : d 1≤d 2
      · exact ⟨E01.trans E02,b,by change d 2≤d 0; omega⟩
      · exact ⟨E02,by change d 2≤d 1; omega,by change d 1≤d 0; omega⟩

private theorem numbered_transport (s t : Fin 3→Nat)
    (he : s=t) (f : ExpandedIndex s→V) (fi : Function.Injective f)
    (fr : ∀ i j,G.Adj (f i) (f j) ↔ expandedThetaAdj s i j) :
    ∃ g : ExpandedIndex t→V, Function.Injective g ∧
      (∀ i j,G.Adj (g i) (g j) ↔ expandedThetaAdj t i j) := by
  subst t
  exact ⟨f,fi,fr⟩

theorem expanded_theta_excluded
    (a b c : V) (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a)
    (da : G.degree a=3) (db : G.degree b=3) (dc : G.degree c=3)
    {w : {x : V // x∉({a,b,c}:Finset V)}}
    (P : ThetaRelays (TriangleContraction G ({a,b,c}:Finset V)) none (some w))
    {W : Type*} [Fintype W] {A : SimpleGraph W}
    (emb : V→W) (ei : Function.Injective emb)
    (ind : ∀ x y,A.Adj (emb x) (emb y) ↔ G.Adj x y)
    (H : Hole A 7) (four : FourCycleFree A) (nine : ¬∃ p : Fin 9→W,InducedPath A p)
    (out : ∀ x,Outside H.c (emb x))
    (single : ∀ x,∃ k,∀ j,A.Adj (emb x) (H.c j) ↔ k=j) : False := by
  have fourG : FourCycleFree G := by
    intro u v x y ne ux vx uy vy
    exact ei (four _ _ _ _ (ei.ne ne) ((ind _ _).mpr ux) ((ind _ _).mpr vx) ((ind _ _).mpr uy) ((ind _ _).mpr vy))
  have nineG : ¬∃ p : Fin 9→V,InducedPath G p := by
    rintro ⟨p,h⟩
    exact nine ⟨emb ∘ p,ei.comp h.1,fun i j lt=>(ind _ _).trans (h.2 i j lt)⟩
  obtain ⟨e,xy,yz⟩ := arrange_three fun i=>(P.rel i).n
  let Q := P.reorder e
  let x := (Q.rel 0).n
  let y := (Q.rel 1).n
  let z := (Q.rel 2).n
  have xx : x<9 := Nat.lt_succ_of_le (thetaInterior_len_le Q nineG 0)
  have yy : y<9 := Nat.lt_succ_of_le (thetaInterior_len_le Q nineG 1)
  have zz : z<9 := Nat.lt_succ_of_le (thetaInterior_len_le Q nineG 2)
  obtain ⟨t,ts,ti,tc,tp⟩ := choose_theta_triangle_ports a b c ab bc ca da db dc Q
  have unique (j : V) (jo : j∉({a,b,c}:Finset V)) :
      ∀ l m,l∈({a,b,c}:Finset V)→m∈({a,b,c}:Finset V)→G.Adj l j→G.Adj m j→l=m :=
    fun l m ls ms lj mj=>triangle_single_external_neighbor G fourG a b c ab bc ca j jo l m ls ms lj.symm mj.symm
  have sz : Q.network.sizes=sizeVec x y z := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨f,fi,fadj⟩ := numbered_transport Q.network.sizes (sizeVec x y z) sz
    (expandThetaVertex Q t) (expandThetaVertex_inj Q t ts ti) (expandThetaVertex_adj Q t ts ti tc tp unique)
  rcases atlas_checked ⟨x,xx⟩ ⟨y,yy⟩ ⟨z,zz⟩ xy yz with good|bad
  · exact nine (good_theta_model_has_nine x y z good (emb ∘ f) (ei.comp fi)
      (fun i j=>(ind _ _).trans (fadj i j)) H four (fun i=>out (f i)) (fun i=>single (f i)))
  · exact atlas_rejection_lift x y z f fi fadj fourG nineG _ bad

#print axioms expanded_theta_excluded
end Graffiti133ExpandedTriangle


namespace Graffiti133ExpandedTriangle
open SimpleGraph Finset Graffiti133 Graffiti133Bicycle Graffiti133TriangleCritical
open scoped Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {S : Finset V} {w : {x : V // x∉S}}
local notation "J" => TriangleContraction G S
local notation "B" => @insert _ _ (@Finset.instInsert (Option {x : V // x∉S}) (Classical.decEq _)) none {some w}

def liftRelay {a b} (P : Relay J B a b) (i : Fin P.n) : {x : V // x∉S} :=
  outsideVal (P.f i) (fun e=>P.off i (by simp [e]))

theorem liftRelay_eq {a b} (P : Relay J B a b) (i : Fin P.n) :
    some (liftRelay P i)=P.f i := outsideVal_some _ _

theorem liftRelay_inj {a b} (P : Relay J B a b) :
    Function.Injective (fun i => (liftRelay P i).val) := by
  intro i j eq
  apply P.path.1
  rw [←liftRelay_eq P i,←liftRelay_eq P j]
  exact congrArg some (Subtype.ext eq)

theorem liftRelay_off_hub {a b} (P : Relay J B a b) (i : Fin P.n) :
    (liftRelay P i).val≠w.val := by
  intro eq
  have hs : liftRelay P i=w := Subtype.ext eq
  apply P.off i
  rw [←liftRelay_eq P i,hs]
  simp

theorem liftRelay_pair_adj {a b c d} (P : Relay J B a b) (Q : Relay J B c d)
    (i : Fin P.n) (j : Fin Q.n) :
    G.Adj (liftRelay P i).val (liftRelay Q j).val ↔ (J).Adj (P.f i) (Q.f j) := by
  rw [←liftRelay_eq P i,←liftRelay_eq Q j]
  rfl

theorem liftRelay_path {a b} (P : Relay J B a b) :
    InducedPath G (fun i => (liftRelay P i).val) :=
  ⟨liftRelay_inj P,fun i j lt=>(liftRelay_pair_adj P P i j).trans (P.path.2 i j lt)⟩

theorem liftRelay_sep {a b c d} {P : Relay J B a b} {Q : Relay J B c d} (S : P.Separated Q)
    (i : Fin P.n) (j : Fin Q.n) :
    (liftRelay P i).val≠(liftRelay Q j).val ∧ ¬G.Adj (liftRelay P i).val (liftRelay Q j).val := by
  refine ⟨?_,fun h=>(S i j).2 ((liftRelay_pair_adj P Q i j).mp h)⟩
  intro h
  apply (S i j).1
  rw [←liftRelay_eq P i,←liftRelay_eq Q j]
  exact congrArg some (Subtype.ext h)

theorem liftRelay_ext_hub {a b} (P : Relay J B a b) (i : Fin P.n) :
    G.Adj w.val (liftRelay P i).val ↔
      (i.val=0 ∧ some w=a) ∨ (i.val+1=P.n ∧ some w=b) := by
  have h := P.attached i (some w) (by simp)
  rw [←liftRelay_eq] at h
  exact h

theorem liftRelay_triangle {a b} (P : Relay J B a b) (i : Fin P.n) :
    (∃ x∈S,G.Adj x (liftRelay P i).val) ↔
      (i.val=0 ∧ none=a) ∨ (i.val+1=P.n ∧ none=b) := by
  have h := P.attached i none (by simp)
  rw [←liftRelay_eq] at h
  exact h

#print axioms liftRelay_path
#print axioms liftRelay_sep
end Graffiti133ExpandedTriangle


namespace Graffiti133ExpandedTriangle
open SimpleGraph Finset Graffiti133 Graffiti133Bicycle Graffiti133TriangleCritical
open scoped Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {S : Finset V} {w : {x : V // x∉S}}

def dumbStartVertex (P : DumbRelays (TriangleContraction G S) none (some w)) :
    {x : V // x∉S} :=
  if h : 0<P.mid.n then liftRelay (G:=G) (S:=S) (w:=w) P.mid ⟨0,h⟩ else w

structure DumbPorts (P : DumbRelays (TriangleContraction G S) none (some w)) where
  left : V
  right : V
  join : V
  leftMem : left∈S
  rightMem : right∈S
  joinMem : join∈S
  leftHit : G.Adj left (liftRelay (G:=G) (S:=S) (w:=w) P.first ⟨0,by have := P.longFirst; omega⟩).val
  rightHit : G.Adj right (liftRelay (G:=G) (S:=S) (w:=w) P.first ⟨P.first.n-1,by have := P.longFirst; omega⟩).val
  joinHit : G.Adj join (dumbStartVertex P).val
  lr : left≠right
  lj : left≠join
  rj : right≠join

theorem choose_dumb_ports
    (P : DumbRelays (TriangleContraction G S) none (some w))
    (uniquePort : ∀ t∈S,∀ x y, x∉S → y∉S → G.Adj t x → G.Adj t y → x=y) :
    Nonempty (DumbPorts P) := by
  let i : Fin P.first.n := ⟨0,by have := P.longFirst; omega⟩
  let j : Fin P.first.n := ⟨P.first.n-1,by have := P.longFirst; omega⟩
  obtain ⟨l,ls,lh⟩ := (liftRelay_triangle (G:=G) (S:=S) (w:=w) P.first i).mpr (Or.inl ⟨rfl,rfl⟩)
  obtain ⟨r,rs,rh⟩ := (liftRelay_triangle (G:=G) (S:=S) (w:=w) P.first j).mpr (Or.inr ⟨by
    have := P.longFirst
    change P.first.n-1+1=P.first.n
    omega,rfl⟩)
  obtain ⟨k,ks,kh⟩ : ∃ k∈S,G.Adj k (dumbStartVertex P).val := by
    by_cases p : 0<P.mid.n
    · simpa only [dumbStartVertex,dif_pos p] using
        (liftRelay_triangle (G:=G) (S:=S) (w:=w) P.mid ⟨0,p⟩).mpr (Or.inl ⟨rfl,rfl⟩)
    · have e := P.direct.mpr (by omega : P.mid.n=0)
      simpa only [dumbStartVertex,dif_neg p] using
        (show ∃ k∈S,G.Adj k w.val from e)
  have edge_ne_start (a : Fin P.first.n) : (liftRelay (G:=G) (S:=S) (w:=w) P.first a).val≠(dumbStartVertex P).val := by
    by_cases p : 0<P.mid.n
    · simpa only [dumbStartVertex,dif_pos p] using (liftRelay_sep (G:=G) (S:=S) (w:=w) P.f_m a ⟨0,p⟩).1
    · simpa only [dumbStartVertex,dif_neg p] using liftRelay_off_hub (G:=G) (S:=S) (w:=w) P.first a
  refine ⟨⟨l,r,k,ls,rs,ks,lh,rh,kh,?_,?_,?_⟩⟩
  · intro eq
    have conn := uniquePort l ls _ _ (liftRelay (G:=G) (S:=S) (w:=w) P.first i).property (liftRelay (G:=G) (S:=S) (w:=w) P.first j).property
      lh (eq.symm ▸ rh)
    have h := congrArg Fin.val (liftRelay_inj (G:=G) (S:=S) (w:=w) P.first conn)
    change 0=P.first.n-1 at h
    have := P.longFirst
    omega
  · intro eq
    exact edge_ne_start i (uniquePort l ls _ _ (liftRelay (G:=G) (S:=S) (w:=w) P.first i).property
      (dumbStartVertex P).property lh (eq.symm ▸ kh))
  · intro eq
    exact edge_ne_start j (uniquePort r rs _ _ (liftRelay (G:=G) (S:=S) (w:=w) P.first j).property
      (dumbStartVertex P).property rh (eq.symm ▸ kh))

#print axioms choose_dumb_ports
end Graffiti133ExpandedTriangle


namespace Graffiti133ExpandedTriangle
open SimpleGraph Graffiti133 Graffiti133Camby Graffiti133Bicycle Graffiti133TriangleCritical
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {S : Finset V} {w : {x : V // x∉S}}

theorem dumb_expanded_long_path
    (P : DumbRelays (TriangleContraction G S) none (some w))
    (T : DumbPorts P)
    (clique : ∀ x∈S,∀ y∈S,x≠y → G.Adj x y)
    (unique : ∀ t∈S,∀ x y, x∉S → y∉S → G.Adj t x → G.Adj t y → x=y) :
    ∃ f : Fin (P.first.n+P.mid.n+P.last.n+2)→V, InducedPath G f := by
  classical
  let a := P.first.n
  let b := P.mid.n
  let c := P.last.n-1
  have apos : 0<a := by have := P.longFirst; omega
  have aone : 1<a := P.longFirst
  have cpos : 2≤P.last.n := P.longLast
  have csize : c+1=P.last.n := by dsimp [c]; omega
  let ai : Fin a := ⟨0,apos⟩
  let liftA (i : Fin a) := (liftRelay (G:=G) (S:=S) (w:=w) P.first i).val
  let liftB (i : Fin b) := (liftRelay (G:=G) (S:=S) (w:=w) P.mid i).val
  let castC : Fin c → Fin P.last.n := Fin.castLE (by omega)
  let Al : Fin (a+1)→V := Fin.lastCases T.left (liftA ∘ Fin.rev)
  let L : Fin (a+2)→V := Fin.lastCases T.join Al
  let M : Fin (b+1)→V := Fin.lastCases w.val liftB
  let R (i : Fin c) := (liftRelay (G:=G) (S:=S) (w:=w) P.last (castC i)).val
  have startA (i : Fin a) : G.Adj T.left (liftA i) ↔ i.val=0 := by
    constructor
    · intro e
      have eq := unique T.left T.leftMem _ _ (liftRelay (G:=G) (S:=S) (w:=w) P.first i).property
        (liftRelay (G:=G) (S:=S) (w:=w) P.first ai).property e T.leftHit
      simpa using congrArg Fin.val (liftRelay_inj (G:=G) (S:=S) (w:=w) P.first eq)
    · intro e
      have ei : i=ai := Fin.ext e
      subst i
      exact T.leftHit
  have notJoinA (i : Fin a) : ¬G.Adj T.join (liftA i) := by
    intro edge
    have eq := unique T.join T.joinMem _ _ (liftRelay (G:=G) (S:=S) (w:=w) P.first i).property
      (dumbStartVertex P).property edge T.joinHit
    by_cases bp : 0<b
    · have hd := (liftRelay_sep (G:=G) (S:=S) (w:=w) P.f_m i ⟨0,bp⟩).1
      exact hd (by simpa only [dumbStartVertex,dif_pos (show 0<P.mid.n from bp)] using eq)
    · exact liftRelay_off_hub (G:=G) (S:=S) (w:=w) P.first i (by simpa only [dumbStartVertex,dif_neg (show ¬0<P.mid.n from bp)] using eq)
  have fresh (x : V) (hx : x∈S) (i : Fin a) : x≠liftA i := by
    intro e
    exact (liftRelay (G:=G) (S:=S) (w:=w) P.first i).property (Eq.mp (congrArg (fun v=>v∈S) e) hx)
  have ar : InducedPath G (liftA ∘ Fin.rev) := reverse_path (liftRelay_path (G:=G) (S:=S) (w:=w) P.first)
  have rev (i : Fin a) : (Fin.rev i).val=a-(i.val+1) := Fin.val_rev i
  have nAl : InducedPath G Al := by
    apply append_induced apos ar T.left (fun i=>fresh T.left T.leftMem i.rev)
    · apply (startA _).mpr
      rw [rev]
      change a-(a-1+1)=0
      omega
    · intro i hi e
      have x := (startA i.rev).mp e
      rw [rev] at x
      omega
  have nL : InducedPath G L := by
    have two : 0<a+1 := by omega
    apply append_induced two nAl T.join
    · intro i
      refine Fin.lastCases ?_ (fun j=>?_) i
      · simpa [Al] using T.lj.symm
      · simpa [Al,Function.comp_def] using fresh T.join T.joinMem j.rev
    · have eq : (⟨a+1-1,by omega⟩:Fin (a+1))=Fin.last a := Fin.ext (by simp)
      rw [eq]
      change G.Adj T.join (Fin.lastCases T.left (liftA ∘ Fin.rev) (Fin.last a))
      rw [Fin.lastCases_last]
      exact clique T.join T.joinMem T.left T.leftMem T.lj.symm
    · intro i hi
      have il : i≠Fin.last a := by intro e; subst i; simp at hi
      obtain ⟨j,hj⟩ := Fin.eq_castSucc_of_ne_last il
      rw [←hj]
      simpa [Al,Function.comp_def] using notJoinA j.rev
  have nM : InducedPath G M := by
    by_cases bz : b=0
    · refine ⟨fun i j _=>Fin.ext (by have := i.isLt; have := j.isLt; omega),?_⟩
      intro i j lt
      have := j.isLt
      have e : i.val<j.val := lt
      omega
    · have bp : 0<b := by omega
      apply append_induced bp (liftRelay_path (G:=G) (S:=S) (w:=w) P.mid) w.val
      · intro i
        exact (liftRelay_off_hub (G:=G) (S:=S) (w:=w) P.mid i).symm
      · apply (liftRelay_ext_hub (G:=G) (S:=S) (w:=w) P.mid _).mpr
        exact Or.inr ⟨by change b-1+1=b; omega,rfl⟩
      · intro i hi edge
        rcases (liftRelay_ext_hub (G:=G) (S:=S) (w:=w) P.mid _).mp edge with e|e
        · cases e.2
        · have ex := e.1
          change i.val+1=b at ex
          omega
  have nR : InducedPath G R := by
    refine ⟨(liftRelay_inj (G:=G) (S:=S) (w:=w) P.last).comp (Fin.castLE_injective _),?_⟩
    intro i j lt
    exact (liftRelay_path (G:=G) (S:=S) (w:=w) P.last).2 (castC i) (castC j) lt
  have rwfirst (i : Fin c) : G.Adj w.val (R i) ↔ i.val=0 := by
    rw [show R i=(liftRelay (G:=G) (S:=S) (w:=w) P.last (castC i)).val from rfl,liftRelay_ext_hub]
    simp only [and_true]
    change i.val=0 ∨ i.val+1=P.last.n ↔ i.val=0
    have := i.isLt
    omega
  have shownA (i : Fin (a+2)) :
      (i.val=a+1 ∧ L i=T.join) ∨ (i.val=a ∧ L i=T.left) ∨
      ∃ k : Fin a,i.val<a ∧ L i=liftA k := by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · exact Or.inl ⟨rfl,Fin.lastCases_last⟩
    · refine Fin.lastCases ?_ (fun k=>?_) j
      · exact Or.inr (Or.inl ⟨rfl,by simp [L,Al]⟩)
      · exact Or.inr (Or.inr ⟨k.rev,k.isLt,by simp [L,Al,Function.comp_def]⟩)
  have shownB (i : Fin (b+1)) :
      (i.val=b ∧ M i=w.val) ∨ ∃ k : Fin b,i.val=k.val ∧ M i=liftB k := by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · exact Or.inl ⟨rfl,Fin.lastCases_last⟩
    · exact Or.inr ⟨j,rfl,Fin.lastCases_castSucc _⟩
  have uniqueLeft (x : V) (xo : x∉S) : G.Adj T.left x → x=liftA ai :=
    fun h=>unique T.left T.leftMem _ _ xo (liftRelay (G:=G) (S:=S) (w:=w) P.first ai).property h T.leftHit
  have uniqueJoin (x : V) (xo : x∉S) : G.Adj T.join x → x=(dumbStartVertex P).val :=
    fun h=>unique T.join T.joinMem _ _ xo (dumbStartVertex P).property h T.joinHit
  have meetMid (i : Fin b) : G.Adj T.join (liftB i) ↔ i.val=0 := by
    have bp : 0<b := by have := i.isLt; omega
    constructor
    · intro edge
      have eq := uniqueJoin _ (liftRelay (G:=G) (S:=S) (w:=w) P.mid i).property edge
      rw [dumbStartVertex,dif_pos (show 0<P.mid.n from bp)] at eq
      exact congrArg Fin.val (liftRelay_inj (G:=G) (S:=S) (w:=w) P.mid eq)
    · intro e
      have eq : i=⟨0,bp⟩ := Fin.ext e
      subst i
      simpa only [dumbStartVertex,dif_pos (show 0<P.mid.n from bp)] using T.joinHit
  have meetHub : G.Adj T.join w.val ↔ b=0 := by
    constructor
    · intro edge
      by_cases pos : 0<P.mid.n
      · have eq := uniqueJoin _ w.property edge
        rw [dumbStartVertex,dif_pos pos] at eq
        exact (liftRelay_off_hub (G:=G) (S:=S) (w:=w) P.mid ⟨0,pos⟩ eq.symm).elim
      · dsimp [b]; omega
    · intro e
      simpa only [dumbStartVertex,dif_neg (by change ¬0<b; omega : ¬0<P.mid.n)] using T.joinHit
  have finL (i : Fin (a+2)) (j : Fin (b+1)) :
      L i≠M j ∧ (G.Adj (L i) (M j) ↔ i.val+1=a+2 ∧ j.val=0) := by
    rcases shownA i with ⟨iy,iy'⟩|⟨iy,iy'⟩|⟨k,ki,ke⟩ <;>
      rcases shownB j with ⟨jy,jy'⟩|⟨h,hj,he⟩
    · rw [iy',jy',iy,jy,meetHub]
      refine ⟨?_,by simp⟩
      intro e
      exact w.property (Eq.mp (congrArg (fun v=>v∈S) e) T.joinMem)
    · rw [iy',he,iy,hj,meetMid]
      refine ⟨?_,by simp⟩
      intro e
      exact (liftRelay (G:=G) (S:=S) (w:=w) P.mid h).property (Eq.mp (congrArg (fun v=>v∈S) e) T.joinMem)
    · rw [iy',jy',iy,jy]
      refine ⟨?_,⟨?_,fun e=>by omega⟩⟩
      · intro e
        exact w.property (Eq.mp (congrArg (fun v=>v∈S) e) T.leftMem)
      · intro e
        exact (liftRelay_off_hub (G:=G) (S:=S) (w:=w) P.first ai (uniqueLeft _ w.property e).symm).elim
    · rw [iy',he,iy,hj]
      refine ⟨?_,⟨?_,fun e=>by omega⟩⟩
      · intro e
        exact (liftRelay (G:=G) (S:=S) (w:=w) P.mid h).property (Eq.mp (congrArg (fun v=>v∈S) e) T.leftMem)
      · intro e
        exact ((liftRelay_sep (G:=G) (S:=S) (w:=w) P.f_m ai h).1 (uniqueLeft _ (liftRelay (G:=G) (S:=S) (w:=w) P.mid h).property e).symm).elim
    · rw [ke,jy']
      refine ⟨liftRelay_off_hub (G:=G) (S:=S) (w:=w) P.first k,⟨?_,fun e=>by omega⟩⟩
      intro e
      simpa using (liftRelay_ext_hub (G:=G) (S:=S) (w:=w) P.first k).mp e.symm
    · rw [ke,he]
      exact ⟨(liftRelay_sep (G:=G) (S:=S) (w:=w) P.f_m k h).1,
        ⟨fun e=>((liftRelay_sep (G:=G) (S:=S) (w:=w) P.f_m k h).2 e).elim,fun e=>by omega⟩⟩
  let LM : Fin ((a+2)+(b+1))→V := Fin.addCases L M
  have nLM : InducedPath G LM := concat_induced_paths nL nM (fun i j=>(finL i j).1) (fun i j=>(finL i j).2)
  have finR (i : Fin ((a+2)+(b+1))) (j : Fin c) :
      LM i≠R j ∧ (G.Adj (LM i) (R j) ↔ i.val+1=(a+2)+(b+1) ∧ j.val=0) := by
    refine Fin.addCases ?_ ?_ i
    · intro x
      simp only [LM,Fin.addCases_left]
      have xl := x.isLt
      change L x≠R j ∧ (G.Adj (L x) (R j) ↔ x.val+1=(a+2)+(b+1) ∧ j.val=0)
      rcases shownA x with ⟨_,eq⟩|⟨_,eq⟩|⟨k,_,eq⟩
      · rw [eq]
        refine ⟨?_,⟨?_,fun q=>by omega⟩⟩
        · intro e
          exact (liftRelay (G:=G) (S:=S) (w:=w) P.last (castC j)).property (Eq.mp (congrArg (fun v=>v∈S) e) T.joinMem)
        · intro e
          have h := (liftRelay_triangle (G:=G) (S:=S) (w:=w) P.last (castC j)).mp ⟨T.join,T.joinMem,e⟩
          simp at h
      · rw [eq]
        refine ⟨?_,⟨?_,fun q=>by omega⟩⟩
        · intro e
          exact (liftRelay (G:=G) (S:=S) (w:=w) P.last (castC j)).property (Eq.mp (congrArg (fun v=>v∈S) e) T.leftMem)
        · intro e
          have h := (liftRelay_triangle (G:=G) (S:=S) (w:=w) P.last (castC j)).mp ⟨T.left,T.leftMem,e⟩
          simp at h
      · rw [eq]
        exact ⟨(liftRelay_sep (G:=G) (S:=S) (w:=w) P.f_l k (castC j)).1,
          ⟨fun e=>((liftRelay_sep (G:=G) (S:=S) (w:=w) P.f_l k (castC j)).2 e).elim,fun q=>by omega⟩⟩
    · intro x
      simp only [LM,Fin.addCases_right]
      change M x≠R j ∧ (G.Adj (M x) (R j) ↔ (a+2)+x.val+1=(a+2)+(b+1) ∧ j.val=0)
      rcases shownB x with ⟨v,eq⟩|⟨k,v,eq⟩
      · rw [eq,v,rwfirst]
        exact ⟨(liftRelay_off_hub (G:=G) (S:=S) (w:=w) P.last (castC j)).symm,by simp [Nat.add_assoc]⟩
      · rw [eq,v]
        have := k.isLt
        exact ⟨(liftRelay_sep (G:=G) (S:=S) (w:=w) P.m_l k (castC j)).1,
          ⟨fun e=>((liftRelay_sep (G:=G) (S:=S) (w:=w) P.m_l k (castC j)).2 e).elim,fun q=>by omega⟩⟩
  have final := concat_induced_paths nLM nR (fun i j=>(finR i j).1) (fun i j=>(finR i j).2)
  have eq : P.first.n+P.mid.n+P.last.n+2 = ((a+2)+(b+1))+c := by dsimp [a,b]; omega
  rw [eq]
  exact ⟨_,final⟩

#print axioms dumb_expanded_long_path
end Graffiti133ExpandedTriangle


namespace Graffiti133ExpandedTriangle
open SimpleGraph Finset Graffiti133 Graffiti133Bicycle Graffiti133TriangleCritical
open scoped Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {S : Finset V} {w : {x : V // x∉S}}

theorem expanded_dumb_excluded
    (P : DumbRelays (TriangleContraction G S) none (some w))
    (clique : ∀ x∈S,∀ y∈S,x≠y → G.Adj x y)
    (unique : ∀ t∈S,∀ x y, x∉S → y∉S → G.Adj t x → G.Adj t y → x=y)
    (noExtTri : ∀ x y z, x∉S → y∉S → z∉S → G.Adj x y → G.Adj y z → G.Adj z x → False)
    (four : FourCycleFree G) (nine : ¬∃ p : Fin 9→V,InducedPath G p) : False := by
  obtain ⟨T⟩ := choose_dumb_ports P unique
  have left : 3≤P.first.n := by
    by_contra! bad
    have eq : P.first.n=2 := by have := P.longFirst; omega
    let i : Fin P.first.n := ⟨0,by omega⟩
    let j : Fin P.first.n := ⟨1,by omega⟩
    have f := liftRelay_path (G:=G) (S:=S) (w:=w) P.first
    have e := (f.2 i j (by change (0:Nat)<1; decide)).mpr rfl
    have er : G.Adj T.right (liftRelay (G:=G) (S:=S) (w:=w) P.first j).val := by
      have jlast : j=(⟨P.first.n-1,by omega⟩:Fin P.first.n) := Fin.ext (by change 1=P.first.n-1; omega)
      rw [jlast]
      exact T.rightHit
    have lr := clique T.left T.leftMem T.right T.rightMem T.lr
    have ne : T.left≠(liftRelay (G:=G) (S:=S) (w:=w) P.first j).val := by
      intro e
      exact (liftRelay (G:=G) (S:=S) (w:=w) P.first j).property
        (Eq.mp (congrArg (fun x=>x∈S) e) T.leftMem)
    have same := four _ _ _ _ ne T.leftHit e.symm lr er.symm
    exact (liftRelay (G:=G) (S:=S) (w:=w) P.first i).property (same.symm ▸ T.rightMem)
  have right : 4≤P.last.n := by
    rcases (show P.last.n=2 ∨ P.last.n=3 ∨ 4≤P.last.n by have := P.longLast; omega) with eq|eq|eq
    · let i : Fin P.last.n := ⟨0,by omega⟩
      let j : Fin P.last.n := ⟨1,by omega⟩
      have f := liftRelay_path (G:=G) (S:=S) (w:=w) P.last
      have e := (f.2 i j (by change (0:Nat)<1; decide)).mpr rfl
      have p := (liftRelay_ext_hub (G:=G) (S:=S) (w:=w) P.last i).mpr (Or.inl ⟨rfl,rfl⟩)
      have q := (liftRelay_ext_hub (G:=G) (S:=S) (w:=w) P.last j).mpr (Or.inr ⟨by change 1+1=P.last.n; omega,rfl⟩)
      exact (noExtTri _ _ _ w.property
        (liftRelay (G:=G) (S:=S) (w:=w) P.last i).property
        (liftRelay (G:=G) (S:=S) (w:=w) P.last j).property p e q.symm).elim
    · let i : Fin P.last.n := ⟨0,by omega⟩
      let j : Fin P.last.n := ⟨1,by omega⟩
      let k : Fin P.last.n := ⟨2,by omega⟩
      have f := liftRelay_path (G:=G) (S:=S) (w:=w) P.last
      have e := (f.2 i j (by change (0:Nat)<1; decide)).mpr rfl
      have ee := (f.2 j k (by change (1:Nat)<2; decide)).mpr rfl
      have p := (liftRelay_ext_hub (G:=G) (S:=S) (w:=w) P.last i).mpr (Or.inl ⟨rfl,rfl⟩)
      have q := (liftRelay_ext_hub (G:=G) (S:=S) (w:=w) P.last k).mpr (Or.inr ⟨by change 2+1=P.last.n; omega,rfl⟩)
      have ne := (liftRelay_off_hub (G:=G) (S:=S) (w:=w) P.last j).symm
      have eq := f.1 (four _ _ _ _ ne p e.symm q ee)
      have h := congrArg Fin.val eq
      change 0=2 at h
      omega
    · exact eq
  obtain ⟨f,p⟩ := dumb_expanded_long_path P T clique unique
  exact nine (Graffiti133Revisit.trim_path (by omega) p)

#print axioms expanded_dumb_excluded
end Graffiti133ExpandedTriangle


namespace Graffiti133ExpandedTriangle
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Bicycle Graffiti133TriangleCritical
open scoped Classical
set_option linter.unusedSectionVars false
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {A : SimpleGraph W}

theorem three_three_three_plus_three_excluded
    (a b c w : V) (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a)
    (da : G.degree a=3) (db : G.degree b=3) (dc : G.degree c=3) (dw : G.degree w=3)
    (wo : w∉({a,b,c}:Finset V))
    (rest : ∀ x, x∉({a,b,c}:Finset V) → x≠w → G.degree x=2)
    (hc : G.Connected)
    (noExtTri : ∀ x y z, x∉({a,b,c}:Finset V) → y∉({a,b,c}:Finset V) →
      z∉({a,b,c}:Finset V) → G.Adj x y → G.Adj y z → G.Adj z x → False)
    (emb : V→W) (ei : Function.Injective emb)
    (ind : ∀ x y,A.Adj (emb x) (emb y) ↔ G.Adj x y)
    (H : Hole A 7) (four : FourCycleFree A) (nine : ¬∃ p : Fin 9→W,InducedPath A p)
    (out : ∀ x,Outside H.c (emb x))
    (single : ∀ x,∃ k,∀ j,A.Adj (emb x) (H.c j) ↔ k=j) : False := by
  let S : Finset V := {a,b,c}
  let J := TriangleContraction G S
  let wx : {x : V // x∉S} := ⟨w,wo⟩
  have fourG : FourCycleFree G := by
    intro u v x y ne ux vx uy vy
    exact ei (four _ _ _ _ (ei.ne ne) ((ind _ _).mpr ux) ((ind _ _).mpr vx) ((ind _ _).mpr uy) ((ind _ _).mpr vy))
  have nineG : ¬∃ p : Fin 9→V,InducedPath G p := by
    rintro ⟨p,h⟩
    exact nine ⟨emb ∘ p,ei.comp h.1,fun i j lt=>(ind _ _).trans (h.2 i j lt)⟩
  have conn : J.Connected := triangle_contraction_connected G S ⟨a,by simp [S]⟩ hc
  have hubDeg : J.degree none=3 := by
    have e := triangle_hub_degree G fourG a b c ab bc ca
    change J.degree none+6=_ at e
    omega
  have outsideDeg (x : {x : V // x∉S}) : J.degree (some x)=G.degree x.val :=
    external_degree_in_contraction G S x (triangle_single_external_neighbor G fourG a b c ab bc ca _ x.property)
  have outD : J.degree (some wx)=3 := (outsideDeg wx).trans dw
  have low (x : Option {x : V // x∉S}) (na : x≠none) (nb : x≠some wx) : J.degree x=2 := by
    cases x with
    | none => exact (na rfl).elim
    | some x =>
      exact (outsideDeg x).trans (rest _ x.property (fun he=>nb (congrArg some (Subtype.ext he))))
  rcases two_degree_three_has_relay_networks conn (by simp : none≠some wx) hubDeg outD low with th|du
  · obtain ⟨P⟩ := th
    exact expanded_theta_excluded a b c ab bc ca da db dc P emb ei ind H four nine out single
  · obtain ⟨P⟩ := du
    have clique (x : V) (xs : x∈S) (y : V) (ys : y∈S) (ne : x≠y) : G.Adj x y := by
      simp only [S,Finset.mem_insert,Finset.mem_singleton] at xs ys
      rcases xs with e|e|e <;> subst x <;> rcases ys with e|e|e <;> subst y
      all_goals first | contradiction | exact ab | exact ab.symm | exact bc | exact bc.symm | exact ca | exact ca.symm
    exact expanded_dumb_excluded P clique
      (fun t tm x y xo yo tx ty=>degree_three_triangle_has_unique_port a b c ab bc ca da db dc t x y tm xo yo tx ty)
      noExtTri fourG nineG

#print axioms three_three_three_plus_three_excluded
end Graffiti133ExpandedTriangle
