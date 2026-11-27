import BicycleExpandedFourProfile133
import BicycleTriangleDeletion133

namespace Graffiti133ExpandedTriangle
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Bicycle Graffiti133TriangleDeletion
open scoped Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def inducedImageIso (S : Finset V) (T : Finset ((S : Set V))) :
    ((G.induce (S : Set V)).induce (T : Set ((S : Set V)))) ≃g
      G.induce (T.image (fun x : (S : Set V) => x.val) : Set V) where
  toEquiv :=
    { toFun := fun z=>⟨z.val.val,Finset.mem_image.mpr ⟨z.val,z.property,rfl⟩⟩
      invFun := fun z=>by
        classical
        exact ⟨Classical.choose (Finset.mem_image.mp z.property),
          (Classical.choose_spec (Finset.mem_image.mp z.property)).1⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        exact (Classical.choose_spec (Finset.mem_image.mp
          (Finset.mem_image.mpr ⟨z.val,z.property,rfl⟩))).2
      right_inv := by
        intro z
        apply Subtype.ext
        exact (Classical.choose_spec (Finset.mem_image.mp z.property)).2 }
  map_rel_iff' := Iff.rfl

theorem induced_subset_sparsity (H : Hole G 7) (four : FourCycleFree G)
    (nine : ¬∃ p : Fin 9→V,InducedPath G p)
    (site : ∀ x, Outside H.c x → ∃ i, ∀j, G.Adj x (H.c j) ↔ j=i)
    (S : Finset V) (out : ∀ z∈S,Outside H.c z)
    (T : Finset ((S : Set V)))
    (tri : ∀ a b c, a∈T → b∈T → c∈T →
      G.Adj a.val b.val→G.Adj b.val c.val→G.Adj c.val a.val→False) :
    ((G.induce (S : Set V)).induce (T : Set ((S : Set V)))).edgeFinset.card≤T.card := by
  classical
  let v (x : (S : Set V)) := x.val
  have bound := local_exterior_edges H four nine site (T.image v)
    (fun x hx=> by obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hx; exact out _ w.property)
    (fun a b c ha hb hc ab bc ca=>by
      obtain ⟨x,xm,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y,ym,rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨z,zm,rfl⟩ := Finset.mem_image.mp hc
      exact tri _ _ _ xm ym zm ab bc ca)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at bound
  rw [(inducedImageIso (G:=G) S T).card_edgeFinset_eq]
  convert bound using 1
  apply congrArg Finset.card
  ext e
  simp only [SimpleGraph.mem_edgeFinset]
  rfl

theorem choose_exterior_excess_two (O : Finset V)
    (big : O.card+2≤(G.induce (O : Set V)).edgeFinset.card) :
    ∃ S⊆O, S.card+2≤(G.induce (S : Set V)).edgeFinset.card ∧
      ∀ T⊆O,T.card<S.card → (G.induce (T : Set V)).edgeFinset.card≤T.card+1 := by
  classical
  let P (S : Finset V) := S.card+2≤(G.induce (S : Set V)).edgeFinset.card
  let C := O.powerset.filter P
  have mem (S : Finset V) : S∈C ↔ S⊆O ∧ P S := by simp [C]
  obtain ⟨S,sm,min⟩ := Finset.exists_min_image C Finset.card ⟨O,(mem O).mpr ⟨Subset.rfl,big⟩⟩
  refine ⟨S,((mem S).mp sm).1,((mem S).mp sm).2,?_⟩
  intro T TO small
  by_cases over : P T
  · exact ((Nat.not_le_of_gt small) (min T ((mem T).mpr ⟨TO,over⟩))).elim
  · change ¬ T.card+2≤(G.induce (T : Set V)).edgeFinset.card at over
    omega

theorem critical_induced_deletion_budgets (O S : Finset V) (so : S⊆O)
    (min : ∀ T⊆O,T.card<S.card → (G.induce (T : Set V)).edgeFinset.card≤T.card+1)
    (T : Finset ((S : Set V))) (small : T.card<S.card) :
    ((G.induce (S : Set V)).induce (T : Set ((S : Set V)))).edgeFinset.card≤T.card+1 := by
  classical
  rw [(inducedImageIso (G:=G) S T).card_edgeFinset_eq]
  let v (x : (S : Set V)) := x.val
  have count : (T.image v).card=T.card := Finset.card_image_of_injective _ Subtype.val_injective
  have sub : T.image v⊆O := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact so y.property
  simpa only [count] using min _ sub (by rwa [count])

def asErasedIso (J : SimpleGraph V) (x : V) :
    J.induce {y : V | y≠x} ≃g J.induce ((Finset.univ.erase x : Finset V) : Set V) where
  toEquiv :=
    { toFun := fun v=>⟨v.val,Finset.mem_erase.mpr ⟨v.property,Finset.mem_univ _⟩⟩
      invFun := fun v=>⟨v.val,(Finset.mem_erase.mp v.property).1⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  map_rel_iff' := Iff.rfl

#print axioms inducedImageIso
#print axioms induced_subset_sparsity
#print axioms choose_exterior_excess_two
end Graffiti133ExpandedTriangle


namespace Graffiti133TriangleCritical
open SimpleGraph Finset Graffiti133 Graffiti133Bicycle
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem erased_card (x : V) : Fintype.card {y : V // y≠x} + 1 = Fintype.card V := by
  rw [Fintype.card_subtype,Finset.filter_ne']
  exact (Finset.card_erase_add_one (Finset.mem_univ x)).trans Finset.card_univ

private theorem neighbor_exterior_bound (a b c : V) (ab : G.Adj a b) (ca : G.Adj c a)
    (deg : 4≤G.degree a) :
    2≤((G.neighborFinset a) \ ({b,c}:Finset V)).card := by
  have sub : ({b,c}:Finset V)⊆G.neighborFinset a := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl|e
    · exact (G.mem_neighborFinset a _).mpr ab
    · rcases Finset.mem_singleton.mp e with rfl
      exact (G.mem_neighborFinset a _).mpr ca.symm
  have sz := Finset.card_sdiff_add_card_eq_card sub
  rw [G.card_neighborFinset_eq_degree] at sz
  have u : ({b,c}:Finset V).card≤2 := by
    exact (Finset.card_insert_le _ _).trans (by simp)
  omega

private theorem enough_vertices (h4 : FourCycleFree G)
    (a b c : V) (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a)
    (da : 4≤G.degree a) (db : 4≤G.degree b) : 7≤Fintype.card V := by
  let A := G.neighborFinset a \ ({b,c}:Finset V)
  let B := G.neighborFinset b \ ({a,c}:Finset V)
  let C : Finset V := {a,b,c}
  have sa : 2≤A.card := neighbor_exterior_bound G a b c ab ca da
  have sb : 2≤B.card := neighbor_exterior_bound G b a c ab.symm bc.symm db
  have sc : C.card=3 := by simp [C,ab.ne,bc.ne,ca.ne.symm]
  have ac : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro x hx hc
    rcases Finset.mem_insert.mp hc with e|q
    · subst x
      exact (G.loopless _) ((G.mem_neighborFinset a a).mp (Finset.mem_sdiff.mp hx).1)
    · exact (Finset.mem_sdiff.mp hx).2 q
  have bc' : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro x hx hc
    have cEq : C = ({b,a,c}:Finset V) := by ext y; simp [C,or_comm,or_left_comm]
    rw [cEq] at hc
    rcases Finset.mem_insert.mp hc with e|q
    · subst x
      exact (G.loopless _) ((G.mem_neighborFinset b b).mp (Finset.mem_sdiff.mp hx).1)
    · exact (Finset.mem_sdiff.mp hx).2 q
  have ab' : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x xa xb
    have aa := (G.mem_neighborFinset a x).mp (Finset.mem_sdiff.mp xa).1
    have bb := (G.mem_neighborFinset b x).mp (Finset.mem_sdiff.mp xb).1
    have same := h4 a b x c ab.ne aa bb ca.symm bc
    exact (Finset.mem_sdiff.mp xa).2 (by simp [same])
  have whole := Finset.card_le_univ (A∪B∪C)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨ac,bc'⟩),
    Finset.card_union_of_disjoint ab'] at whole
  omega

private theorem degree_surplus (min : ∀ v, 2≤G.degree v) :
    (∑ v : V,(G.degree v-2)) + 2*Fintype.card V=2*G.edgeFinset.card := by
  calc
    _ = ∑ v : V, ((G.degree v-2)+2) := by
      rw [Finset.sum_add_distrib]
      simp [Nat.mul_comm]
    _ = ∑ v : V,G.degree v := Finset.sum_congr rfl (fun v _=>Nat.sub_add_cancel (min v))
    _ = _ := G.sum_degrees_eq_twice_card_edges

theorem one_triangle_excess_two_profile (h4 : FourCycleFree G)
    (a b c : V) (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a)
    (over : Fintype.card V+2≤G.edgeFinset.card)
    (minimal : ∀ x : V, (G.induce {y : V | y≠x}).edgeFinset.card ≤ Fintype.card {y : V // y≠x}+1)
    (cut : ∀ x∈({a,b,c}:Finset V), (G.induce {y : V | y≠x}).edgeFinset.card ≤ Fintype.card {y : V // y≠x}) :
    G.edgeFinset.card=Fintype.card V+2 ∧ (∀ x,2≤G.degree x) ∧
    (∀ x∈({a,b,c}:Finset V),3≤G.degree x) ∧
      (∑ v : V,(G.degree v-2))=4 := by
  let k := G.edgeFinset.card-Fintype.card V
  have k2 : 2≤k := by dsimp [k]; omega
  have eq : G.edgeFinset.card=Fintype.card V+k := by dsimp [k]; omega
  have mn (x : V) : k≤G.degree x := by
    have p := card_delete_add_degree G x
    have q := erased_card x
    have r := minimal x
    omega
  have sp (x : V) (hx : x∈({a,b,c}:Finset V)) : k+1≤G.degree x := by
    have p := card_delete_add_degree G x
    have q := erased_card x
    have r := cut x hx
    omega
  have small : k≤2 := by
    by_contra! bad
    have da := sp a (by simp)
    have db := sp b (by simp)
    have nn := enough_vertices G h4 a b c ab bc ca (by omega) (by omega)
    have low : Fintype.card V*(k-2) ≤ ∑ x : V,(G.degree x-2) := by
      simpa using (Finset.sum_le_sum (s:=Finset.univ) (fun x _ =>
        Nat.sub_le_sub_right (mn x) 2) :
        (∑ _ : V,(k-2)) ≤ ∑ x : V,(G.degree x-2))
    have low' : 7*(k-2)≤Fintype.card V*(k-2) := Nat.mul_le_mul_right _ nn
    have final := degree_surplus G (fun x=>k2.trans (mn x))
    omega
  have dn := degree_surplus G (fun x=>k2.trans (mn x))
  exact ⟨by omega,fun x=>k2.trans (mn x),fun x hx=>by have := sp x hx; omega,by omega⟩

#print axioms one_triangle_excess_two_profile
end Graffiti133TriangleCritical


namespace Graffiti133ExpandedTriangle
open SimpleGraph Finset Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem degree_surplus_split_triangle (a b c : V) (ab : a≠b) (bc : b≠c) (ca : c≠a)
    (low : ∀ x,2≤G.degree x)
    (triangleHigh : ∀ x∈({a,b,c}:Finset V),3≤G.degree x)
    (surplus : (∑ x : V,(G.degree x-2))=4) :
    (G.degree a=4 ∧ G.degree b=3 ∧ G.degree c=3 ∧
      ∀ x∉({a,b,c}:Finset V),G.degree x=2) ∨
    (G.degree a=3 ∧ G.degree b=4 ∧ G.degree c=3 ∧
      ∀ x∉({a,b,c}:Finset V),G.degree x=2) ∨
    (G.degree a=3 ∧ G.degree b=3 ∧ G.degree c=4 ∧
      ∀ x∉({a,b,c}:Finset V),G.degree x=2) ∨
    (G.degree a=3 ∧ G.degree b=3 ∧ G.degree c=3 ∧
       ∃ w∉({a,b,c}:Finset V),G.degree w=3 ∧
         ∀ x∉({a,b,c}:Finset V),x≠w → G.degree x=2) := by
  classical
  let T : Finset V := {a,b,c}
  let U := Finset.univ \ T
  let e (x : V) := G.degree x-2
  have hiA := triangleHigh a (by simp)
  have hiB := triangleHigh b (by simp)
  have hiC := triangleHigh c (by simp)
  have pieces : (∑ x∈U,e x) + (e a+e b+e c)=4 := by
    have p := Finset.sum_sdiff (f:=e) (Finset.subset_univ T)
    have s : (∑ x∈T,e x)=e a+e b+e c := by simp [T,ab,bc,ca.symm,Nat.add_assoc]
    rw [s] at p
    exact p.trans surplus
  have um (x : V) : x∈U ↔ x∉T := by simp [U]
  have each (x : V) (xo : x∉T) : e x≤∑ y∈U,e y :=
    Finset.single_le_sum (fun y _=>Nat.zero_le (e y)) ((um x).mpr xo)
  change (∑ x∈U,e x) + ((G.degree a-2)+(G.degree b-2)+(G.degree c-2))=4 at pieces
  have none : (∑ x∈U,e x)=0 → ∀ x∉T,G.degree x=2 := by
    intro q x xo
    have p := each x xo
    have h := low x
    change G.degree x-2≤_ at p
    omega
  by_cases hA : G.degree a≤3
  · by_cases hB : G.degree b≤3
    · by_cases hC : G.degree c≤3
      · refine Or.inr (Or.inr (Or.inr ⟨by omega,by omega,by omega,?_⟩))
        have one : (∑ x∈U,e x)=1 := by omega
        obtain ⟨w,wm,wp⟩ : ∃ w∈U,0<e w := by
          by_contra! no
          have z : (∑ x∈U,e x)=0 := Finset.sum_eq_zero (fun x hi => by have := no x hi; omega)
          omega
        have wb : e w≤1 := by have := each w ((um w).mp wm); omega
        have dw : G.degree w=3 := by dsimp [e] at wb wp; omega
        refine ⟨w,(um w).mp wm,dw,?_⟩
        intro x xo xw
        have sumPair : (∑ y∈({x,w}:Finset V),e y)≤∑ y∈U,e y :=
          Finset.sum_le_sum_of_subset_of_nonneg (by
            intro y hy
            simp only [Finset.mem_insert,Finset.mem_singleton] at hy
            rcases hy with eq|eq <;> subst y
            · exact (um x).mpr xo
            · exact wm) (by simp)
        rw [show (∑ y∈({x,w}:Finset V),e y)=e x+e w by simp [xw]] at sumPair
        have := low x
        change G.degree x-2+e w≤_ at sumPair
        omega
      · exact Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega,none (by omega)⟩))
    · exact Or.inr (Or.inl ⟨by omega,by omega,by omega,none (by omega)⟩)
  · exact Or.inl ⟨by omega,by omega,by omega,none (by omega)⟩

#print axioms degree_surplus_split_triangle
end Graffiti133ExpandedTriangle


namespace Graffiti133ExpandedTriangle
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Bicycle
  Graffiti133TriangleCritical Graffiti133TriangleDeletion
open scoped Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem one_exterior_triangle_edge_bound (H : Hole G 7)
    (four : FourCycleFree G) (nine : ¬∃ p : Fin 9→V,InducedPath G p)
    (site : ∀ x, Outside H.c x → ∃ i, ∀ j,G.Adj x (H.c j) ↔ j=i)
    (O T₀ : Finset V) (out : ∀ x∈O,Outside H.c x)
    (three : T₀.card≤3)
    (only : ∀ x y z, x∈O → y∈O → z∈O →
      G.Adj x y → G.Adj y z → G.Adj z x → z∈T₀) :
    (G.induce (O : Set V)).edgeFinset.card ≤ O.card+1 := by
  classical
  by_contra! over
  obtain ⟨S,SO,excess,minimum⟩ := choose_exterior_excess_two (G:=G) O
    (by exact Nat.succ_le_of_lt over)
  let U := (S : Set V)
  let J := G.induce U
  have outS (x : V) (xs : x∈S) : Outside H.c x := out x (SO xs)
  obtain ⟨a,b,c,ab,bc,ca⟩ : ∃ a b c : U,J.Adj a b ∧ J.Adj b c ∧ J.Adj c a := by
    by_contra! no
    have e := local_exterior_edges H four nine site S outS
      (fun x y z xs ys zs xy yz zx=>no ⟨x,xs⟩ ⟨y,ys⟩ ⟨z,zs⟩ xy yz zx)
    change S.card+2≤J.edgeFinset.card at excess
    change J.edgeFinset.card≤S.card at e
    omega
  let T : Finset U := {a,b,c}
  let val (x : U) := x.val
  have sizeT : T.card=3 := by simp [T,ab.ne,bc.ne,ca.ne.symm]
  have color (x y z : U) (xy : J.Adj x y) (yz : J.Adj y z) (zx : J.Adj z x) :
      z.val∈T₀ := only _ _ _ (SO x.property) (SO y.property) (SO z.property) xy yz zx
  have setEq : T.image val=T₀ := by
    apply Finset.eq_of_subset_of_card_le
    · intro v vm
      obtain ⟨x,xm,rfl⟩ := Finset.mem_image.mp vm
      simp only [T,Finset.mem_insert,Finset.mem_singleton] at xm
      rcases xm with e|e|e <;> subst x
      · exact color b c a bc ca ab
      · exact color c a b ca ab bc
      · exact color a b c ab bc ca
    · rw [Finset.card_image_of_injective _ Subtype.val_injective,sizeT]
      exact three
  have onlyJ (x y z : U) (xy : J.Adj x y) (yz : J.Adj y z) (zx : J.Adj z x) :
      z∈T := by
    have c := color x y z xy yz zx
    rw [←setEq] at c
    obtain ⟨p,pm,pe⟩ := Finset.mem_image.mp c
    have h : p=z := Subtype.ext pe
    exact h ▸ pm
  have cc : Fintype.card U=S.card := Fintype.card_coe S
  have eJ : Fintype.card U+2≤J.edgeFinset.card := by rwa [cc]
  have small (R : Finset U) (r : R.card<Fintype.card U) :
      (J.induce (R : Set U)).edgeFinset.card≤R.card+1 :=
    critical_induced_deletion_budgets O S SO minimum R (by rwa [cc] at r)
  have sep (R : Finset U) (tri : ∀ x y z, x∈R → y∈R → z∈R →
      J.Adj x y → J.Adj y z → J.Adj z x → False) :
      (J.induce (R : Set U)).edgeFinset.card≤R.card :=
    induced_subset_sparsity H four nine site S outS R tri
  have conn : J.Connected := by
    apply (J.connected_iff_exists_forall_reachable).mpr
    refine ⟨a,?_⟩
    intro x
    apply Classical.byContradiction
    intro no
    let R := Finset.univ.filter fun y => J.Reachable a y
    let Q := Finset.univ \ R
    have rMem (y : U) : y∈R ↔ J.Reachable a y := by simp [R]
    have aR : a∈R := (rMem _).mpr SimpleGraph.Reachable.rfl
    have bR : b∈R := (rMem _).mpr ab.reachable
    have cR : c∈R := (rMem _).mpr ca.symm.reachable
    have contain : T⊆R := by
      intro y ym
      simp only [T,Finset.mem_insert,Finset.mem_singleton] at ym
      rcases ym with e|e|e <;> subst y <;> assumption
    have closed (y z : U) (yz : J.Adj y z) : y∈R ↔ z∈R := by
      rw [rMem,rMem]
      exact ⟨fun h=>h.trans yz.reachable,fun h=>h.trans yz.symm.reachable⟩
    have rlt : R.card<Fintype.card U := by
      rw [←Finset.card_univ]
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,
        fun h=>no ((rMem _).mp (h.symm ▸ Finset.mem_univ x))⟩)
    have er := small R rlt
    have eq := sep Q (fun y z w _ _ wm yz zw wy =>
      (Finset.mem_sdiff.mp wm).2 (contain (onlyJ _ _ _ yz zw wy)))
    have total := edge_count_no_cross J R closed
    have ns := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ R)
    change (J.induce (R : Set U)).edgeFinset.card+(J.induce (Q : Set U)).edgeFinset.card=J.edgeFinset.card at total
    change Q.card+R.card=(Finset.univ : Finset U).card at ns
    rw [Finset.card_univ] at ns
    omega
  have eraseCard (x : U) :
      Fintype.card {y : U // y≠x} = (Finset.univ.erase x : Finset U).card :=
    (Fintype.card_congr (asErasedIso J x).toEquiv).trans (Fintype.card_coe _)
  have allDel (x : U) : (J.induce {y : U | y≠x}).edgeFinset.card≤Fintype.card {y : U // y≠x}+1 := by
    rw [(asErasedIso J x).card_edgeFinset_eq,eraseCard]
    apply small
    exact Finset.card_erase_lt_of_mem (Finset.mem_univ x)
  have triDel (x : U) (xt : x∈T) :
      (J.induce {y : U | y≠x}).edgeFinset.card≤Fintype.card {y : U // y≠x} := by
    rw [(asErasedIso J x).card_edgeFinset_eq,eraseCard]
    apply sep
    intro r s t rm sm tm rs st tr
    have rt : r∈T := onlyJ s t r st tr rs
    have st' : s∈T := onlyJ t r s tr rs st
    have tt : t∈T := onlyJ r s t rs st tr
    have pic : ({r,s,t}:Finset U)=T := by
      apply Finset.eq_of_subset_of_card_le
      · intro u um
        simp only [Finset.mem_insert,Finset.mem_singleton] at um
        rcases um with e|e|e <;> subst u <;> assumption
      · simp [sizeT,rs.ne,st.ne,tr.ne.symm]
    rw [←pic] at xt
    simp only [Finset.mem_insert,Finset.mem_singleton] at xt
    rcases xt with e|e|e
    · exact (Finset.mem_erase.mp rm).1 e.symm
    · exact (Finset.mem_erase.mp sm).1 e.symm
    · exact (Finset.mem_erase.mp tm).1 e.symm
  have fourJ : FourCycleFree J := by
    intro u v x y ne ux vx uy vy
    exact Subtype.ext (four _ _ _ _ (fun e=>ne (Subtype.ext e)) ux vx uy vy)
  obtain ⟨_,low,high,surplus⟩ := one_triangle_excess_two_profile J fourJ a b c ab bc ca eJ allDel triDel
  have single (x : U) : ∃ i,∀ j,G.Adj x.val (H.c j) ↔ i=j := by
    obtain ⟨i,p⟩ := site _ (outS _ x.property)
    exact ⟨i,fun j=>(p j).trans eq_comm⟩
  have O' (x : U) : Outside H.c (val x) := outS _ x.property
  have noOther (x y z : U) (xo : x∉T) (yo : y∉T) (zo : z∉T)
      (xy : J.Adj x y) (yz : J.Adj y z) (zx : J.Adj z x) : False :=
    zo (onlyJ _ _ _ xy yz zx)
  rcases degree_surplus_split_triangle J a b c ab.ne bc.ne ca.ne low high surplus with
    ⟨da,db,dc,rest⟩|⟨da,db,dc,rest⟩|⟨da,db,dc,rest⟩|⟨da,db,dc,w,wo,dw,rest⟩
  · exact four_three_three_excluded (G:=J) (A:=G) a b c ab bc ca da db dc rest onlyJ
      val Subtype.val_injective (fun _ _=>Iff.rfl) H four nine O' single
  · have eq : ({b,c,a}:Finset U)=T := by ext x; simp [T,or_comm,or_left_comm]
    exact four_three_three_excluded (G:=J) (A:=G) b c a bc ca ab db dc da
      (by simpa only [eq] using rest) (by simpa only [eq] using onlyJ)
      val Subtype.val_injective (fun _ _=>Iff.rfl) H four nine O' single
  · have eq : ({c,a,b}:Finset U)=T := by ext x; simp [T,or_comm,or_left_comm]
    exact four_three_three_excluded (G:=J) (A:=G) c a b ca ab bc dc da db
      (by simpa only [eq] using rest) (by simpa only [eq] using onlyJ)
      val Subtype.val_injective (fun _ _=>Iff.rfl) H four nine O' single
  · exact three_three_three_plus_three_excluded (G:=J) (A:=G) a b c w ab bc ca da db dc dw wo rest conn noOther
      val Subtype.val_injective (fun _ _=>Iff.rfl) H four nine O' single

#print axioms one_exterior_triangle_edge_bound
end Graffiti133ExpandedTriangle



namespace Graffiti133OneTriangle
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

open Graffiti133BicycleCharge Graffiti133Bicycle

private lemma row_card (v : V) (S : Finset V) :
    row G v S = (S.filter fun w => G.Adj v w).card := by
  classical
  exact (Finset.card_filter _ _).symm

private lemma local_bound (v : V) : localIndependence G v ≤ row G v Finset.univ := by
  classical
  obtain ⟨A,hA,eA⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
  rw [←eA,row_card]
  exact Finset.card_le_card (fun x hx => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,(Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1 x hx⟩)

private lemma row_symm (A B : Finset V) :
    (∑ x ∈ A, row G x B) = ∑ y ∈ B, row G y A := by
  classical
  unfold row
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [G.adj_comm y x]

private lemma cycle_row (H : Hole G 7) (i : Fin 7) :
    row G (H.c i) (Finset.univ.image H.c) = 2 := by
  classical
  change (∑ w ∈ Finset.univ.image H.c, (if G.Adj (H.c i) w then 1 else 0 : ℕ))=2
  rw [Finset.sum_image (fun _ _ _ _ eq => H.inj eq)]
  have aux : ∀ i : Fin 7, (Finset.univ.filter fun j => Cyclic i j).card = 2 := by decide
  rw [←aux i,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  exact if_congr (H.adj i j) rfl rfl


private theorem singleton_row (H : Hole G 7) (x : V) (i : Fin 7)
    (hit : ∀ j, G.Adj x (H.c j) ↔ j=i) :
    row G x (Finset.univ.image H.c) = 1 := by
  classical
  change (∑ w ∈ Finset.univ.image H.c, (if G.Adj x w then 1 else 0 : ℕ))=_
  rw [Finset.sum_image (fun _ _ _ _ eq => H.inj eq)]
  have h : (∑ j : Fin 7, (if j=i then 1 else 0 : ℕ)) = 1 := by simp
  have same : (∑ j : Fin 7, (if G.Adj x (H.c j) then 1 else 0 : ℕ)) =
      (∑ j : Fin 7, (if j=i then 1 else 0 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro j _
    exact if_congr (hit j) rfl rfl
  exact same.trans h


private theorem degree_induced_row (O : Finset V) (x : (O : Set V)) :
    (G.induce (O : Set V)).degree x = row G x.val O := by
  classical
  rw [SimpleGraph.degree,show row G x.val O=(O.filter fun y=>G.Adj x.val y).card
    from (Finset.card_filter _ _).symm]
  apply Finset.card_bij (fun y _=>y.val)
  · intro y hy
    exact Finset.mem_filter.mpr ⟨y.property,((G.induce (O : Set V)).mem_neighborFinset x y).mp hy⟩
  · exact fun y _ z _ e=>Subtype.ext e
  · intro y hy
    obtain ⟨mem,adj⟩ := Finset.mem_filter.mp hy
    exact ⟨⟨y,mem⟩,((G.induce (O : Set V)).mem_neighborFinset x ⟨y,mem⟩).mpr adj,rfl⟩


private theorem local_extra (v a b : V) (va : G.Adj v a) (vb : G.Adj v b)
    (ab : G.Adj a b) : localIndependence G v + 1 ≤ row G v Finset.univ := by
  classical
  obtain ⟨A,hA,eA⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
  have facts := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  obtain ⟨x,xn,xv⟩ : ∃ x, x∉A ∧ G.Adj v x := by
    by_cases aa : a∈A
    · exact ⟨b,fun bb=>facts.2 a aa b bb ab,vb⟩
    · exact ⟨a,aa,va⟩
  rw [←eA,row_card,←Finset.card_insert_of_not_mem xn]
  apply Finset.card_le_card
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl|ya
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,xv⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,facts.1 y ya⟩


theorem singleton_seven_at_most_one_exterior_triangle_mean_four (H : Hole G 7)
    (h4 : FourCycleFree G) (h9 : ¬∃ p : Fin 9→V,InducedPath G p)
    (site : ∀ x, Outside H.c x → ∃ i, ∀j,G.Adj x (H.c j) ↔ j=i)
    (T₀ : Finset V) (three : T₀.card≤3)
    (only : ∀ a b c,Outside H.c a → Outside H.c b → Outside H.c c →
      G.Adj a b → G.Adj b c → G.Adj c a → c∈T₀) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  by_cases tr : ∃ a b c, Outside H.c a ∧ Outside H.c b ∧ Outside H.c c ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c a
  · obtain ⟨a,b,c,ao,bo,co,ab,bc,ca⟩ := tr
    let C : Finset V := Finset.univ.image H.c
    let O : Finset V := Finset.univ \ C
    let T : Finset V := {a,b}
    have old : C.card=7 := by rw [Finset.card_image_of_injective _ H.inj]; simp
    have size : O.card+7=Fintype.card V := by
      have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
      rw [old,Finset.card_univ] at h
      exact h
    have out (x : V) (hx : x∈O) : Outside H.c x := by
      intro i e
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
    have edges := Graffiti133ExpandedTriangle.one_exterior_triangle_edge_bound H h4 h9 site O T₀ out three
      (fun x y z hx hy hz xy yz zx=>only x y z (out x hx) (out y hy) (out z hz) xy yz zx)
    let J := G.induce (O : Set V)
    change J.edgeFinset.card≤O.card+1 at edges
    have arcsO : (∑ x∈O,row G x O)≤2*O.card+2 := by
      calc
        _ = ∑ x : (O : Set V),row G x.val O := (Finset.sum_attach O _).symm
        _ = ∑ x : (O : Set V),J.degree x := Finset.sum_congr rfl (fun x _=>(degree_induced_row O x).symm)
        _ = 2*J.edgeFinset.card := J.sum_degrees_eq_twice_card_edges
        _ ≤ _ := by omega
    have cSum : (∑ v∈C, row G v C)=14 := by
      change (∑ v ∈ Finset.univ.image H.c, row G v C)=14
      rw [Finset.sum_image (fun _ _ _ _ e => H.inj e)]
      have cRow (i : Fin 7) : row G (H.c i) C=2 := cycle_row H i
      simp_rw [cRow]
      simp
    have weight : (∑ v∈O, row G v C)=O.card := by
      have eq (v : V) (hv : v∈O) : row G v C=1 := by
        obtain ⟨i,hi⟩ := site v (out v hv)
        exact singleton_row H v i hi
      rw [Finset.sum_congr rfl eq]
      simp
    have split (f : V → ℕ) : (∑ v : V, f v) = (∑ v∈C,f v)+(∑ v∈O,f v) := by
      simpa [O,Nat.add_comm] using (Finset.sum_sdiff (f:=f) (Finset.subset_univ C)).symm
    have rows (v : V) : row G v Finset.univ = row G v C + row G v O :=
      split (fun w => @ite ℕ (G.Adj v w) (Classical.propDecidable _) 1 0)
    have budget : (∑ v : V,row G v Finset.univ)≤4*Fintype.card V+2 := by
      rw [split (fun v=>row G v Finset.univ)]
      simp_rw [rows,Finset.sum_add_distrib]
      rw [cSum,row_symm (G:=G) C O,weight]
      omega
    have triangle (v : V) (vin : v∈T) : ∃ r s,G.Adj v r ∧ G.Adj v s ∧ G.Adj r s := by
      simp only [T,Finset.mem_insert,Finset.mem_singleton] at vin
      rcases vin with q|q <;> subst v
      · exact ⟨b,c,ab,ca.symm,bc⟩
      · exact ⟨c,a,bc,ab.symm,ca⟩
    have point (v : V) : localIndependence G v+(if v∈T then 1 else 0)≤row G v Finset.univ := by
      by_cases inT : v∈T
      · obtain ⟨r,s,vr,vs,rs⟩ := triangle v inT
        simpa [inT] using local_extra v r s vr vs rs
      · simpa [inT] using local_bound (G:=G) v
    have sb := Finset.sum_le_sum (s:=Finset.univ) (fun v _=>point v)
    rw [Finset.sum_add_distrib] at sb
    have cardT : (∑ v : V,(if v∈T then (1:Nat) else 0))=2 := by
      rw [←Finset.card_filter]
      have eq : (Finset.univ.filter fun v => v∈T)=T := by ext; simp
      rw [eq]
      change ({a,b}:Finset V).card=2
      simp [ab.ne]
    rw [cardT] at sb
    omega
  · exact singleton_triangle_free_seven_mean_four H h4 h9 site
      (fun a b c ao bo co ab bc ca=>tr ⟨a,b,c,ao,bo,co,ab,bc,ca⟩)

#print axioms singleton_seven_at_most_one_exterior_triangle_mean_four
end Graffiti133OneTriangle
