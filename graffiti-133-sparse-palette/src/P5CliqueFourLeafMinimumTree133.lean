import P5CliqueSparseTreeMetric133
import P5CliqueFourCleanP6Budget133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem minimum_dominating_core_leaf_has_outer_client
    (D : Finset V) (dm : MinimalSize G D) (x : (D : Set V))
    (someOther : ∃ y : (D : Set V),y≠x)
    (leaf : SparseLeaf (G.induce (D : Set V)) x) :
    ∃ q∉D,G.Adj q x.val := by
  classical
  by_contra! none
  let J := G.induce (D : Set V)
  let T := D.erase x.val
  have mT (u : (D : Set V)) (ne : u≠x) : u.val∈T :=
    Finset.mem_erase.mpr ⟨fun h=>ne (Subtype.ext h),u.property⟩
  obtain ⟨y,yx⟩ := someOther
  have yn : y.val∈T := mT y yx
  have conn : (G.induce (T : Set V)).Connected := by
    rw [connected_iff_exists_forall_reachable]
    refine ⟨⟨y.val,yn⟩,fun z=>?_⟩
    let zz : (D : Set V) := ⟨z.val,(Finset.mem_erase.mp z.property).2⟩
    have zn : zz≠x := fun e=>(Finset.mem_erase.mp z.property).1 (congrArg Subtype.val e)
    obtain ⟨w,wmin⟩ := dm.1.1.exists_walk_length_eq_dist y zz
    have no : x∉w.support := by
      intro xs
      obtain ⟨j,jx,jl⟩ := Walk.mem_support_iff_exists_getVert.mp xs
      have jp : 0<j := by
        by_cases j0 : j=0
        · rw [j0,Walk.getVert_zero] at jx
          exact (yx jx).elim
        omega
      have js : j<w.length := by
        by_cases je : j=w.length
        · rw [je,Walk.getVert_length] at jx
          exact (zn jx).elim
        omega
      have e := w.adj_getVert_succ js
      rw [jx] at e
      have pre := w.adj_getVert_succ (i:=j-1) (by omega)
      have pred : j-1+1=j := by omega
      rw [pred,jx] at pre
      have eq := leaf _ _ pre.symm e
      let F (i : Fin (w.length+1)) := w.getVert i.val
      have p := (sparse_core_geodesic_prefix dm.1.1 w wmin (w.length+1) le_rfl).1
      have fin : (⟨j-1,by omega⟩ : Fin (w.length+1))=⟨j+1,by omega⟩ := p eq
      have val := congrArg Fin.val fin
      change j-1=j+1 at val
      omega
    let S : Set (D : Set V) := {v | v∈w.support}
    let inc : J.induce S →g G.induce (T : Set V) :=
      ⟨fun v=>⟨v.val.val,mT v.val (fun e=>no (e ▸ v.property))⟩,fun e=>e⟩
    have reach : (J.induce S).Reachable ⟨y,w.start_mem_support⟩ ⟨zz,w.end_mem_support⟩ :=
      w.connected_induce_support _ _
    exact reach.map inc
  have xd : ∃ z∈T,G.Adj x.val z := by
    refine (dm.1.1.preconnected x y).elim ?_
    intro w
    have e := w.adj_snd (w.not_nil_of_ne yx.symm)
    have ne : w.snd≠x := by
      intro h
      rw [h] at e
      exact J.loopless x e
    exact ⟨w.snd.val,mT _ ne,e⟩
  have cd : CD G T := by
    refine ⟨conn,?_⟩
    intro a
    by_cases ad : a∈D
    · by_cases ax : a=x.val
      · obtain ⟨z,zm,ez⟩ := xd
        exact Or.inr ⟨z,zm,ax.symm ▸ ez⟩
      · exact Or.inl (Finset.mem_erase.mpr ⟨ax,ad⟩)
    obtain hd | ⟨z,zd,az⟩ := dm.1.2 a
    · exact (ad hd).elim
    have zx : z≠x.val := fun e=>none a ad (e ▸ az)
    exact Or.inr ⟨z,Finset.mem_erase.mpr ⟨zx,zd⟩,az⟩
  have min := dm.2 T cd
  have er := Finset.card_erase_add_one x.property
  change T.card+1=D.card at er
  omega

theorem four_leaf_minimum_tree_core_ambient_radius_four_mean_four
    (h4 : FourCycleFree G) (h9 : NoPath G 9) (conn : G.Connected) (rad : 4≤radius G)
    (D : Finset V) (dm : MinimalSize G D)
    (tr : (G.induce (D : Set V)).IsTree) (h7 : NoPath (G.induce (D : Set V)) 7)
    (p : Fin 4→V) (pm : ∀ i,p i∈D) (pi : Function.Injective p)
    (leaf : ∀ i,SparseLeaf (G.induce (D : Set V)) ⟨p i,pm i⟩)
    (attach : ∀ q∉D,∃ i,G.Adj q (p i))
    (palette : ∀ q∉D,∀ x∈D,G.Adj q x→∃ i,x=p i)
    (single : ∀ q∉D,∀ i,G.Adj q (p i)→∀ x∈D,G.Adj q x↔x=p i) :
    (∑ v : V,localIndependence G v)≤4*Fintype.card V := by
  classical
  obtain ⟨F,Fp,lf,rf⟩ := sparse_tree_diameter_five_arm_from_ambient_radius conn rad D
    (fun q qo=>by obtain ⟨i,qi⟩ := attach q qo; exact ⟨p i,pm i,qi⟩) tr h7
  let f (j : Fin 6) := (F j).val
  have fp : InducedPath G f := ⟨fun i j e=>Fp.1 (Subtype.ext e),Fp.2⟩
  have fd (j : Fin 6) : f j∈D := (F j).property
  have differ : F 0≠F 5 := fun e=>(by decide : (0:Fin 6)≠5) (Fp.1 e)
  obtain ⟨x,xo,ex⟩ := minimum_dominating_core_leaf_has_outer_client D dm (F 0) ⟨F 5,differ.symm⟩ lf
  obtain ⟨y,yo,ey⟩ := minimum_dominating_core_leaf_has_outer_client D dm (F 5) ⟨F 0,differ⟩ rf
  obtain ⟨i,ei⟩ := palette x xo _ (fd 0) ex
  obtain ⟨j,ej⟩ := palette y yo _ (fd 5) ey
  have ji : j≠i := fun e=>differ (Subtype.ext (ei.trans ((congrArg p e).symm.trans ej.symm)))
  let e0 := Equiv.swap 0 i
  have e0i : e0 0=i := by simp [e0]
  let j' := e0.symm j
  have j0 : j'≠0 := fun h=>ji (by simpa [j',e0i] using congrArg e0 h)
  let e1 := Equiv.swap 1 j'
  have e1z : e1 0=0 := Equiv.swap_apply_of_ne_of_ne (by decide) (fun h=>j0 h.symm)
  have e1j : e1 1=j' := Equiv.swap_apply_left _ _
  let e := e1.trans e0
  have ez : e 0=i := by simp [e,e1z,e0i]
  have en : e 1=j := by simp [e,e1j,j']
  let p' (k : Fin 4) := p (e k)
  have att' (q : V) (qo : q∉D) : ∃ a,G.Adj q (p' a) := by
    obtain ⟨a,h⟩ := attach q qo
    exact ⟨e.symm a,by simpa [p'] using h⟩
  have pal' (q : V) (qo : q∉D) (w : V) (wm : w∈D) (qw : G.Adj q w) : ∃ a,w=p' a := by
    obtain ⟨a,h⟩ := palette q qo w wm qw
    exact ⟨e.symm a,by simpa [p'] using h⟩
  have lft : f 0=p' 0 := by simpa [p',ez] using ei
  have rgt : f 5=p' 1 := by simpa [p',en] using ej
  have off (k : Fin 4) (k2 : 2≤k.val) (m : Fin 6) : p' k≠f m := by
    intro eq
    have ki : k≠0 := fun h=>by have a := congrArg Fin.val h; change k.val=0 at a; omega
    have kj : k≠1 := fun h=>by have a := congrArg Fin.val h; change k.val=1 at a; omega
    have m0 : m≠0 := fun h=>ki (e.injective (pi (eq.trans (h.symm ▸ lft))))
    have m5 : m≠5 := fun h=>kj (e.injective (pi (eq.trans (h.symm ▸ rgt))))
    have lo : 0<m.val := Fin.pos_iff_ne_zero.mpr m0
    have hi : m.val < 5 := by
      by_contra! bad
      exact m5 (Fin.ext (by change m.val=5; omega))
    let a : Fin 6 := ⟨m.val-1,by omega⟩
    let b : Fin 6 := ⟨m.val+1,by omega⟩
    have ea : (G.induce (D : Set V)).Adj (F a) (F m) :=
      (Fp.2 a m (show a.val<m.val by change m.val-1 < m.val; omega)).mpr (by change m.val-1+1=m.val; omega)
    have eb : (G.induce (D : Set V)).Adj (F m) (F b) :=
      (Fp.2 m b (show m.val < b.val by change m.val < m.val+1; omega)).mpr rfl
    have tEq : (⟨p (e k),pm (e k)⟩ : (D : Set V))=F m := Subtype.ext eq
    have same := (tEq ▸ leaf (e k)) _ _ ea.symm eb
    have bad := congrArg Fin.val (Fp.1 same)
    change m.val-1=m.val+1 at bad
    omega
  exact clean_P6_four_port_ambient_mean_four h4 h9 D p' (fun k=>pm (e k)) (pi.comp e.injective)
    att' pal' (fun q qo k=>single q qo (e k)) f fp fd lft rgt off dm.1.1 h7

#print axioms minimum_dominating_core_leaf_has_outer_client
#print axioms four_leaf_minimum_tree_core_ambient_radius_four_mean_four
end Graffiti133P5CliqueArms
