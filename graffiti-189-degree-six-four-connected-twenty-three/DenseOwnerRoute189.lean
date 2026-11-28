import WideWing189
import SixCoreMarkedPath189

open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath
open private Graffiti189LongestPath.WideWing.CompleteOn from WideWing189
namespace Graffiti189LongestPath.DenseOwnerRoute
variable {U : Type*} [Fintype U] [DecidableEq U] {D : SimpleGraph U} [DecidableRel D.Adj]

private theorem degree_bound (A B : Finset U) (u : U)
    (outside : ∀ v, D.Adj u v → v∉A → v∈B) :
    D.degree u ≤ (A.filter (D.Adj u)).card + B.card := by
  have s : D.neighborFinset u⊆A.filter (D.Adj u) ∪ B := by
    intro v e
    have edge := (D.mem_neighborFinset _ _).mp e
    by_cases h : v∈A
    · exact mem_union_left _ (mem_filter.mpr ⟨h,edge⟩)
    · exact mem_union_right _ (outside v edge h)
  have b := (card_le_card s).trans (card_union_le _ _)
  rwa [D.card_neighborFinset_eq_degree] at b

private theorem contacts (x y z : U) (xy : x≠y) (A : Finset U)
    (out : ∀ v∉A,v=x ∨ v=y ∨ v=z)
    (lo : ∀ u,2≤D.degree u) (hi : ∀ u,u≠z → 4≤D.degree u) :
    ∃ a∈A, ∃ b∈A, a≠b ∧ D.Adj x a ∧ D.Adj y b := by
  classical
  let X := A.filter (D.Adj x)
  let Y := A.filter (D.Adj y)
  have dx : D.degree x≤X.card+2 := by
    have q := degree_bound (D:=D) A ({y,z}:Finset U) x (fun v e vo => by
      obtain h|h|h := out v vo
      · exact (e.ne h.symm).elim
      · exact mem_insert.mpr (Or.inl h)
      · exact mem_insert.mpr (Or.inr (mem_singleton.mpr h)))
    have c := card_insert_le y ({z}:Finset U)
    rw [card_singleton] at c
    change D.degree x≤X.card+({y,z}:Finset U).card at q
    omega
  have dy : D.degree y≤Y.card+2 := by
    have q := degree_bound (D:=D) A ({x,z}:Finset U) y (fun v e vo => by
      obtain h|h|h := out v vo
      · exact mem_insert.mpr (Or.inl h)
      · exact (e.ne h.symm).elim
      · exact mem_insert.mpr (Or.inr (mem_singleton.mpr h)))
    have c := card_insert_le x ({z}:Finset U)
    rw [card_singleton] at c
    change D.degree y≤Y.card+({x,z}:Finset U).card at q
    omega
  have xbig (xz : x≠z) : 2≤X.card := by have e := hi x xz; omega
  have ybig (yz : y≠z) : 2≤Y.card := by have e := hi y yz; omega
  have xpos : X.Nonempty := by
    apply card_pos.mp
    by_cases zx : x=z
    · have q := degree_bound (D:=D) A ({y}:Finset U) x (fun v e vo => by
        rcases out v vo with h|h|h
        · exact (e.ne h.symm).elim
        · exact mem_singleton.mpr h
        · exact (e.ne (h.trans zx.symm).symm).elim)
      rw [card_singleton] at q
      change D.degree x≤X.card+1 at q
      have le := lo x
      omega
    · have e := xbig zx
      omega
  have ypos : Y.Nonempty := by
    apply card_pos.mp
    by_cases zy : y=z
    · have q := degree_bound (D:=D) A ({x}:Finset U) y (fun v e vo => by
        rcases out v vo with h|h|h
        · exact mem_singleton.mpr h
        · exact (e.ne h.symm).elim
        · exact (e.ne (h.trans zy.symm).symm).elim)
      rw [card_singleton] at q
      change D.degree y≤Y.card+1 at q
      have le := lo y
      omega
    · have e := ybig zy
      omega
  have use : 1<X.card ∨ 1<Y.card := by
    by_cases h : x=z
    · exact Or.inr (ybig (fun h' => xy (h.trans h'.symm)))
    · exact Or.inl (xbig h)
  rcases use with xx|yy
  · obtain ⟨b,hb⟩ := ypos
    obtain ⟨a,ha,a',ha',ne⟩ := one_lt_card.mp xx
    have finish (w : U) (hw : w∈X) (wb : w≠b) :
        ∃ a∈A, ∃ b∈A, a≠b ∧ D.Adj x a ∧ D.Adj y b :=
      ⟨w,(mem_filter.mp hw).1,b,(mem_filter.mp hb).1,wb,(mem_filter.mp hw).2,(mem_filter.mp hb).2⟩
    by_cases e : a=b
    · exact finish a' ha' (fun t => ne (e.trans t.symm))
    · exact finish a ha e
  · obtain ⟨a,ha⟩ := xpos
    obtain ⟨b,hb,b',hb',ne⟩ := one_lt_card.mp yy
    have finish (w : U) (hw : w∈Y) (aw : a≠w) :
        ∃ a∈A, ∃ b∈A, a≠b ∧ D.Adj x a ∧ D.Adj y b :=
      ⟨a,(mem_filter.mp ha).1,w,(mem_filter.mp hw).1,aw,(mem_filter.mp ha).2,(mem_filter.mp hw).2⟩
    by_cases e : a=b
    · exact finish b' hb' (fun t => ne (e.symm.trans t))
    · exact finish b hb e

private theorem bracket {x y a b : U} (xy : x≠y) (xa : D.Adj x a) (byy : D.Adj b y)
    (q : D.Walk a b) (qp : q.IsPath) (xo : x∉q.support) (yo : y∉q.support) :
    ∃ p : D.Walk x y,p.IsPath ∧ p.length=q.length+2 := by
  refine ⟨.cons xa (q.concat byy),?_,by simp⟩
  apply (cons_isPath_iff _ _).mpr
  refine ⟨Graffiti189LongestPath.CrossSaturation.path_concat_new q qp byy yo,?_⟩
  rw [support_concat,List.concat_eq_append]
  simp [xo,xy]

/-- In a seven-vertex component, two exclusive porters have a spanning
route if every other high vertex has internal degree at least six. -/
theorem route_seven (hc : Fintype.card U=7)
    (x y z : U) (xy : x≠y) (lo : ∀ v,2≤D.degree v) (hi : ∀ v,v≠z → 4≤D.degree v)
    (dense : ∀ v,v≠x → v≠y → v≠z → 6≤D.degree v) :
    ∃ q : D.Walk x y,q.IsPath ∧ 6≤q.length := by
  classical
  let A := ((univ:Finset U).erase x).erase y
  have ca : A.card=5 := by
    dsimp [A]
    rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm xy,mem_univ y⟩),
      card_erase_of_mem (mem_univ x),card_univ,hc]
  have excl (v : U) (va : v∈A) : v≠x ∧ v≠y :=
    ⟨(mem_erase.mp (mem_erase.mp va).2).1,(mem_erase.mp va).1⟩
  have ab (u v : U) (ne : u≠v) (ud : 6≤D.degree u) : D.Adj u v := by
    have sub : D.neighborFinset u⊆univ.erase u :=
      fun w ww => mem_erase.mpr ⟨((D.mem_neighborFinset _ _).mp ww).ne.symm,mem_univ w⟩
    have e := eq_of_subset_of_card_le sub (by
      rw [card_erase_of_mem (mem_univ u),card_univ,hc,D.card_neighborFinset_eq_degree]; omega)
    exact (D.mem_neighborFinset _ _).mp (e.symm ▸ mem_erase.mpr ⟨Ne.symm ne,mem_univ v⟩)
  have cl : Graffiti189LongestPath.WideWing.CompleteOn D A := by
    intro u uu v vv ne
    by_cases uz : u=z
    · exact (ab v u (Ne.symm ne) (dense v (excl v vv).1 (excl v vv).2
        (fun e => ne (uz.trans e.symm)))).symm
    · exact ab u v ne (dense u (excl u uu).1 (excl u uu).2 uz)
  have out (w : U) (wo : w∉A) : w=x ∨ w=y ∨ w=z := by
    by_cases wx : w=x
    · exact Or.inl wx
    · by_cases wy : w=y
      · exact Or.inr (Or.inl wy)
      · exact (wo (mem_erase.mpr ⟨wy, mem_erase.mpr ⟨wx,mem_univ _⟩⟩)).elim
  obtain ⟨a,aa,b,bb,aB,xa,byy⟩ := contacts x y z xy A out lo hi
  obtain ⟨p,pp,ps⟩ := WideWing.path_between_in_clique A cl aa bb aB
  have se : p.support.toFinset=A := by ext v; exact List.mem_toFinset.trans (ps v)
  have pl := congrArg card se
  rw [List.toFinset_card_of_nodup pp.support_nodup,length_support,ca] at pl
  obtain ⟨q,qp,ql⟩ := bracket xy xa byy.symm p pp
    (fun h => (excl x ((ps x).mp h)).1 rfl) (fun h => (excl y ((ps y).mp h)).2 rfl)
  exact ⟨q,qp,by omega⟩

/-- In an eight-vertex component with the same two-porter geometry, six
vertices suffice. Pick five high nonporters containing the two contacts. -/
theorem route_eight (hc : Fintype.card U=8)
    (x y z : U) (xy : x≠y) (lo : ∀ v,2≤D.degree v) (hi : ∀ v,v≠z → 4≤D.degree v)
    (dense : ∀ v,v≠x → v≠y → v≠z → 6≤D.degree v) :
    ∃ q : D.Walk x y,q.IsPath ∧ 5≤q.length := by
  classical
  let R := (((univ:Finset U).erase x).erase y).erase z
  have R5 : 5≤R.card := by
    have a := Finset.card_erase_le (s:=((univ:Finset U).erase x).erase y) (a:=z)
    by_cases h : z∈((univ:Finset U).erase x).erase y
    · have ez := card_erase_add_one h
      rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm xy,mem_univ y⟩),
        card_erase_of_mem (mem_univ x),card_univ,hc] at ez
      exact Nat.le_of_eq (by change R.card+1=6 at ez; omega)
    · rw [show R=((univ:Finset U).erase x).erase y from erase_eq_of_not_mem h,
        card_erase_of_mem (mem_erase.mpr ⟨Ne.symm xy,mem_univ y⟩),
        card_erase_of_mem (mem_univ x),card_univ,hc]
      decide
  have out (w : U) (wo : w∉R) : w=x ∨ w=y ∨ w=z := by
    by_cases wx : w=x
    · exact Or.inl wx
    · by_cases wy : w=y
      · exact Or.inr (Or.inl wy)
      · by_cases wz : w=z
        · exact Or.inr (Or.inr wz)
        · exact (wo (mem_erase.mpr ⟨wz,mem_erase.mpr ⟨wy,mem_erase.mpr ⟨wx,mem_univ _⟩⟩⟩)).elim
  obtain ⟨a,aa,b,bb,ab,xa,byy⟩ := contacts x y z xy R out lo hi
  have abR : ({a,b}:Finset U)⊆R := fun w ww =>
    (mem_insert.mp ww).elim (fun e => e.symm ▸ aa) (fun e => (mem_singleton.mp e).symm ▸ bb)
  let K := R\({a,b}:Finset U)
  have k3 : 3≤K.card := by
    have cs := card_sdiff_add_card_eq_card abR
    rw [show ({a,b}:Finset U).card=2 by simp [ab]] at cs
    change K.card+2=R.card at cs
    omega
  obtain ⟨T,tK,tc⟩ := exists_subset_card_eq k3
  let A := ({a,b}:Finset U)∪T
  have ac : A.card=5 := by
    have d : Disjoint ({a,b}:Finset U) T := disjoint_left.mpr (fun _ e et =>
      (mem_sdiff.mp (tK et)).2 e)
    rw [card_union_of_disjoint d,show ({a,b}:Finset U).card=2 by simp [ab],tc]
  have ar : A⊆R := union_subset abR (tK.trans sdiff_subset)
  let J := D.induce (A:Set U)
  let s : ↥(A:Set U) := ⟨a,by simp [A]⟩
  let t : ↥(A:Set U) := ⟨b,by simp [A]⟩
  have minD (v : ↥(A:Set U)) : 3≤J.degree v := by
    have q := ar v.property
    have vd := dense v.val (mem_erase.mp (mem_erase.mp (mem_erase.mp q).2).2).1
      (mem_erase.mp (mem_erase.mp q).2).1 (mem_erase.mp q).1
    have re := degree_bound (D:=D) A (univ\A) v.val (fun w _ wo => mem_sdiff.mpr ⟨mem_univ _,wo⟩)
    have cs := card_sdiff_add_card_eq_card (subset_univ A)
    rw [ac,card_univ,hc] at cs
    have e : (A.filter (D.Adj v.val)).card=J.degree v := by
      rw [←J.card_neighborFinset_eq_degree]
      refine card_bij' (s:=A.filter (D.Adj v.val)) (t:=J.neighborFinset v)
        (fun w ww => (⟨w,(mem_filter.mp ww).1⟩ : ↥(A:Set U)))
        (fun (w : ↥(A:Set U)) _ => w.val) ?_ ?_ ?_ ?_
      · intro w ww; exact (J.mem_neighborFinset _ _).mpr (mem_filter.mp ww).2
      · intro w ww; exact mem_filter.mpr ⟨w.property,(J.mem_neighborFinset _ _).mp ww⟩
      · intro w hw; rfl
      · intro w hw; exact Subtype.ext rfl
    rw [e] at re
    omega
  obtain ⟨p,pp,pl⟩ := Graffiti189SixCore.five_core_marked_path J
    ((Fintype.card_coe A).trans ac) minD (show s≠t from fun e => ab (congrArg Subtype.val e))
  let f : J→g D := ⟨Subtype.val,fun e => e⟩
  have supported (u : U) (up : u∈(p.map f).support) : u∈R := by
    rw [support_map] at up
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp up
    exact ar v.property
  have xo : x∉(p.map f).support := fun e =>
    (mem_erase.mp (mem_erase.mp (mem_erase.mp (supported x e)).2).2).1 rfl
  have yo : y∉(p.map f).support := fun e =>
    (mem_erase.mp (mem_erase.mp (supported y e)).2).1 rfl
  obtain ⟨ppp,pP,lp⟩ := bracket xy xa byy.symm (p.map f)
    (map_isPath_of_injective Subtype.val_injective pp) xo yo
  have ll : 3≤(p.map f).length := by simpa using pl
  exact ⟨ppp,pP,by omega⟩

#print axioms route_seven
#print axioms route_eight
end Graffiti189LongestPath.DenseOwnerRoute
