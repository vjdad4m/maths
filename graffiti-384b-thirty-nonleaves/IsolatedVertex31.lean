import LeafFinish
import NoLeafAttachment
import Mathlib.Data.Finset.Sum

namespace Graffiti384b.Isolate31
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The second summand consists of one isolated vertex. -/
def extend : SimpleGraph (V⊕Unit) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> first | exact G.adj_symm | exact id
  loopless := by intro u; cases u <;> first | exact G.loopless _ | exact id

instance : DecidableRel (extend G).Adj := fun u v => by
  cases u <;> cases v <;> first | exact inferInstanceAs (Decidable (G.Adj _ _)) | exact isFalse (fun h => h)

omit [DecidableEq V] in
private theorem neighbors (v : V) :
    (extend G).neighborFinset (.inl v)=(G.neighborFinset v).map .inl := by
  ext x; cases x <;> simp [extend]

omit [DecidableEq V] in
private theorem isolated : (extend G).neighborFinset (.inr ())=∅ := by
  ext x; cases x <;> simp [extend]

private theorem score (v : V) : trianglesAt (extend G) (.inl v)=trianglesAt G v := by
  classical
  unfold trianglesAt
  rw [neighbors,powersetCard_map,filter_map,card_map]
  congr 1
  apply filter_congr
  intro p _
  change (∀ x∈p.map (.inl : V ↪ V⊕Unit),∀ y∈p.map .inl,x≠y → (extend G).Adj x y) ↔ _
  constructor
  · intro h x xm y ym ne
    exact h (.inl x) (mem_map.mpr ⟨_,xm,rfl⟩) (.inl y) (mem_map.mpr ⟨_,ym,rfl⟩)
      (fun eq => ne (Sum.inl_injective eq))
  · intro h x xm y ym ne
    obtain ⟨u,um,rfl⟩ := mem_map.mp xm
    obtain ⟨v,vm,rfl⟩ := mem_map.mp ym
    exact h u um v vm (fun eq => ne (congrArg _ eq))

theorem palette : types (extend G)=insert 0 (types G) := by
  classical
  have zero : trianglesAt (extend G) (.inr ())=0 := by
    have h : (∅ : Finset (V⊕Unit)).powersetCard 2=∅ := powersetCard_eq_empty.mpr (by simp)
    simp [trianglesAt,isolated,h]
  ext k
  constructor
  · intro h
    obtain ⟨v,_,rfl⟩ := mem_image.mp h
    cases v with
    | inl v => rw [score]; exact mem_insert_of_mem (mem_image_of_mem _ (mem_univ v))
    | inr v => cases v; rw [zero]; exact mem_insert_self ..
  · intro h
    rcases mem_insert.mp h with rfl|old
    · exact mem_image.mpr ⟨.inr (),mem_univ _,zero⟩
    · obtain ⟨v,_,rfl⟩ := mem_image.mp old
      exact mem_image.mpr ⟨.inl v,mem_univ _,score G v⟩

omit [DecidableEq V] in
theorem nonleaf_count : (nonleaves (extend G)).card=(nonleaves G).card := by
  have eq : nonleaves (extend G)=(nonleaves G).map .inl := by
    ext x
    cases x with
    | inl v =>
      simp [nonleaves,←card_neighborFinset_eq_degree,neighbors]
    | inr v =>
      cases v; simp [nonleaves,←card_neighborFinset_eq_degree,isolated]
  rw [eq,card_map]

omit [Fintype V] [DecidableEq V] in
private theorem neighbors_in_set (D : Finset (V⊕Unit)) (v : V) :
    nbr (extend G) (.inl v) D=nbr G v D.toLeft := by
  have eq : D.filter ((extend G).Adj (.inl v))=(D.toLeft.filter (G.Adj v)).map .inl := by
    ext x; cases x <;> simp [extend]
  exact (congrArg card eq).trans (card_map ..)

omit [DecidableEq V] in
private theorem minimum (J : SimpleGraph V) [DecidableRel J.Adj] :
    ∃ D,TwoDominates J D ∧ D.card=gamma J :=
  Nat.sInf_mem (show {k : ℕ | ∃ D,TwoDominates J D ∧ D.card=k}.Nonempty from
    ⟨_,univ,by simp [TwoDominates],rfl⟩)

omit [DecidableEq V] in
theorem domination : gamma (extend G)=gamma G+1 := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨D,good,size⟩ := minimum G
    let A := D.disjSum (univ:Finset Unit)
    have dom : TwoDominates (extend G) A := by
      intro x out; cases x with
      | inl v => rw [neighbors_in_set]; simpa [A] using good v (by simpa [A] using out)
      | inr v => simp [A] at out
    have upper : gamma (extend G)≤A.card := Nat.sInf_le ⟨_,dom,rfl⟩
    simpa [A,size] using upper
  · obtain ⟨D,good,size⟩ := minimum (extend G)
    have mandatory : (Sum.inr () : V⊕Unit)∈D := by
      by_contra out
      have z := good _ out
      have eq : D.filter ((extend G).Adj (.inr ()))=∅ := by ext y; cases y <;> simp [extend]
      simp [nbr,eq] at z
    have dom : TwoDominates G D.toLeft := by
      intro v out
      rw [←neighbors_in_set]
      exact good _ (fun h => out (mem_toLeft.mpr h))
    have ub : gamma G≤D.toLeft.card := Nat.sInf_le ⟨_,dom,rfl⟩
    have c := card_toLeft_add_card_toRight (u:=D)
    have p : 0<D.toRight.card := card_pos.mpr ⟨(),mem_toRight.mpr mandatory⟩
    omega

theorem bound_step (zero : 0∈types G) : bound (extend G)=bound G+1 := by
  have up : (types G).card≤Fintype.card V := by
    simpa [types] using (card_image_le (s:=(univ:Finset V)) (f:=trianglesAt G))
  unfold bound
  rw [palette,insert_eq_of_mem zero,Fintype.card_sum,Fintype.card_unit]
  omega

/-- The two independent proofs of the order-33 case also apply to disconnected graphs. -/
theorem order33 (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31) :
    gamma G≤bound G := by
  by_contra! bad
  obtain ⟨e,l,de,dl,el⟩ := Shared.leaf_necessary G n q t bad
  have ind (u v : V) (du : G.degree u=2) (dv : G.degree v=2) (uv : G.Adj u v) : False :=
    (not_lt_of_ge (AdjacentFull.exact G n q t uv du dv)) bad
  exact (not_lt_of_ge (LeafPath.exact_leaf G n q t ind de dl el)) bad

theorem order32 (n : Fintype.card V=32) (q : (nonleaves G).card=32) (t : (types G).card=31)
    (zero : 0∈types G) : gamma G≤bound G := by
  have upper := order33 (extend G) (by simp [n]) ((nonleaf_count G).trans q)
    (by rw [palette,insert_eq_of_mem zero,t])
  rw [domination,bound_step G zero] at upper
  omega

/-- At order 32, failure itself supplies the old zero score. -/
theorem exact32 (n : Fintype.card V=32) (q : (nonleaves G).card=32) (t : (types G).card=31) :
    gamma G≤bound G := by
  by_contra! bad
  obtain ⟨h,_⟩ := Cover31.residual G t q bad
  obtain ⟨_,_,zero,_⟩ := Repair.maximal_diversity G (by omega)
  exact (not_lt_of_ge (order32 G n q t zero)) bad

end Graffiti384b.Isolate31
#print axioms Graffiti384b.Isolate31.palette
#print axioms Graffiti384b.Isolate31.nonleaf_count
#print axioms Graffiti384b.Isolate31.domination
#print axioms Graffiti384b.Isolate31.bound_step
#print axioms Graffiti384b.Isolate31.order33
#print axioms Graffiti384b.Isolate31.order32
#print axioms Graffiti384b.Isolate31.exact32
