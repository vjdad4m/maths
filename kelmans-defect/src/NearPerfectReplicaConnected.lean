import NearPerfectReplicaCubic

open Finset SimpleGraph
namespace KelmansCactus.NearPerfectReplica.Layout
noncomputable section

variable {U J : Type*} [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]
variable {A : SimpleGraph U} {B : SimpleGraph J} {r : U}
variable (L : Layout A B r)

private abbrev remains {X : Type*} [DecidableEq X] (D : Finset X) : Set X := {x | x∉D}

def localD (D : Finset (Host J r)) (i : J) : Finset U :=
  (D.filter (fun v=>v.1=i)).image (fun v=>v.2.val)

omit [Fintype U] [Fintype J] in
theorem localD_iff {D : Finset (Host J r)} {i : J} {u : Cell r} :
    u.val ∈ localD D i ↔ (i,u)∈D := by
  constructor
  · intro h
    obtain ⟨x,xm,xv⟩ := mem_image.mp h
    obtain ⟨xd,xi⟩ := mem_filter.mp xm
    have e : x=(i,u) := Prod.ext xi (Subtype.ext xv)
    exact e ▸ xd
  · intro h
    exact mem_image.mpr ⟨(i,u),mem_filter.mpr ⟨h,rfl⟩,rfl⟩

omit [Fintype U] [Fintype J] in
theorem root_not_local (D : Finset (Host J r)) (i : J) : r∉localD D i := by
  intro h
  obtain ⟨x,_,xr⟩ := mem_image.mp h
  exact x.2.property xr

omit [Fintype U] [Fintype J] in
theorem localD_bound (D : Finset (Host J r)) (i : J) :
    (localD D i).card≤(D.filter (fun v=>v.1=i)).card := card_image_le

def affected (D : Finset (Host J r)) : Finset J := D.image Prod.fst

omit [Fintype U] [DecidableEq U] [Fintype J] in
theorem affected_bound (D : Finset (Host J r)) : (affected D).card≤D.card :=
  card_image_le

omit [Fintype U] [DecidableEq U] [Fintype J] in
theorem unaffected_survives {D : Finset (Host J r)} {i : J}
    (h : i∉affected D) (u : Cell r) : (i,u)∉D := by
  intro hd
  exact h (mem_image.mpr ⟨(i,u),hd,rfl⟩)

def liftCell {D : Finset (Host J r)} {i : J}
    (u : remains (insert r (localD D i))) : remains D :=
  let active : u.val≠r ∧ u.val∉localD D i := by
    have h := u.property
    change u.val∉insert r (localD D i) at h
    simpa only [mem_insert,not_or] using h
  ⟨(i,⟨u.val,active.1⟩),fun bad=>active.2 (localD_iff.mpr bad)⟩

def enter {D : Finset (Host J r)} (x : remains D) :
    remains (insert r (localD D x.val.1)) :=
  ⟨x.val.2.val,by
    simp only [Set.mem_setOf_eq,mem_insert,not_or,localD_iff]
    exact ⟨x.val.2.property, x.property⟩⟩

def liftHom {D : Finset (Host J r)} {i : J} :
    (A.induce (remains (insert r (localD D i)))) →g
      (L.graph.induce (remains D)) :=
  ⟨liftCell,fun {x y} h=>(L.internal_adj (x:=(liftCell x).val) (y:=(liftCell y).val) rfl).mpr h⟩

omit [Fintype U] [Fintype J] in
theorem inside_reach {D : Finset (Host J r)} {x y : remains D}
    (same : x.val.1=y.val.1)
    (con : (A.induce (remains (insert r (localD D x.val.1)))).Connected) :
    (L.graph.induce (remains D)).Reachable x y := by
  let yy : remains (insert r (localD D x.val.1)) :=
    ⟨y.val.2.val,by
      change y.val.2.val∉insert r (localD D x.val.1)
      rw [same]
      exact (enter y).property⟩
  have reach := con (enter x) yy
  apply reach.elim
  intro w
  have rr := (w.map L.liftHom).reachable
  change (L.graph.induce (remains D)).Reachable (liftCell (enter x)) (liftCell yy) at rr
  have ex : liftCell (enter x)=x := by rfl
  have ey : liftCell yy=y := Subtype.ext (Prod.ext same (Subtype.ext rfl))
  rwa [ex,ey] at rr

private def removeRoot (r : U) {T : Finset U} (x : remains T) (xr : x.val≠r) :
    remains (insert r T) :=
  ⟨x.val,by
    change x.val∉insert r T
    exact fun f=>(mem_insert.mp f).elim xr x.property⟩

omit [Fintype U] [Fintype J] in
/-- In a rooted graph, a surviving vertex that reaches the root after
some nonroot deletions already reaches a surviving root neighbor
before entering the root. -/
private theorem root_entry_walk (r : U) {T : Finset U} {x y : remains T}
    (w : (A.induce (remains T)).Walk x y) (dest : y.val=r) :
    ∀ xr : x.val≠r, ∃ u : remains (insert r T), A.Adj r u.val ∧
      (A.induce (remains (insert r T))).Reachable (removeRoot r x xr) u := by
  induction w with
  | nil => exact fun no=>(no dest).elim
  | @cons x v y ed w ih =>
    intro xr
    by_cases vr : v.val=r
    · refine ⟨removeRoot r x xr,?_,Reachable.refl _⟩
      have e : A.Adj x.val v.val := ed
      exact vr ▸ e.symm
    · obtain ⟨u,e,walk⟩ := ih dest vr
      have a : (A.induce (remains (insert r T))).Adj (removeRoot r x xr) (removeRoot r v vr) := ed
      exact ⟨u,e,a.reachable.trans walk⟩

omit [Fintype J] in
private theorem local_connected_of_few {D : Finset (Host J r)} {i : J}
    (con : KelmansStarter.ThreeConnected A)
    (small : (localD D i).card≤1) :
    (A.induce (remains (insert r (localD D i)))).Connected := by
  apply con.2
  rw [card_insert_of_not_mem (root_not_local D i)]
  omega

omit [Fintype U] [Fintype J] in
private theorem local_empty_of_healthy {D : Finset (Host J r)} {i : J}
    (well : i∉affected D) : localD D i=∅ := by
  ext v
  constructor
  · intro h
    obtain ⟨x,xm,_⟩ := mem_image.mp h
    have e := mem_filter.mp xm
    exact (well (mem_image.mpr ⟨x,e.1,e.2⟩)).elim
  · simp

omit [Fintype J] in
private theorem local_connected_of_healthy {D : Finset (Host J r)} {i : J}
    (con : KelmansStarter.ThreeConnected A) (healthy : i∉affected D) :
    (A.induce (remains (insert r (localD D i)))).Connected := by
  apply local_connected_of_few con
  rw [local_empty_of_healthy healthy]
  simp

private def representative {D : Finset (Host J r)} (i : remains (affected D)) :
    remains D :=
  ⟨(i.val,L.port 0),unaffected_survives i.property (L.port 0)⟩

omit [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J] in
private theorem target_of_baseEdge {i k : J} (h : B.Adj i k) :
    ∃ j, L.target (i,j)=k := by
  obtain ⟨j,hj⟩ := (L.baseSlots i).surjective ⟨k,h⟩
  exact ⟨j,congrArg (fun x : B.neighborSet i=>x.val) hj⟩

omit [Fintype J] in
private theorem reach_baseEdge {D : Finset (Host J r)} {i k : remains (affected D)}
    (conA : KelmansStarter.ThreeConnected A)
    (ed : (B.induce (remains (affected D))).Adj i k) :
    (L.graph.induce (remains D)).Reachable (L.representative i) (L.representative k) := by
  obtain ⟨j,ej⟩ := L.target_of_baseEdge (show B.Adj i.val k.val from ed)
  let s : J×Fin 3 := (i.val,j)
  let x : remains D := ⟨L.p s,unaffected_survives i.property (L.port j)⟩
  have qi : (L.q s).1=k.val := ej
  let y : remains D := ⟨L.q s,by
    have notD := unaffected_survives k.property (L.q s).2
    intro bad
    have e : L.q s = (k.val,(L.q s).2) := Prod.ext qi rfl
    exact notD (e ▸ bad)⟩
  have left : (L.graph.induce (remains D)).Reachable (L.representative i) x :=
    L.inside_reach rfl (local_connected_of_healthy conA i.property)
  have across : (L.graph.induce (remains D)).Adj x y := L.edge_at_slot s
  have right : (L.graph.induce (remains D)).Reachable (L.representative k) y :=
    L.inside_reach qi.symm (local_connected_of_healthy conA k.property)
  exact left.trans (across.reachable.trans right.symm)

omit [Fintype J] in
private theorem along_base {D : Finset (Host J r)} {i k : remains (affected D)}
    (conA : KelmansStarter.ThreeConnected A)
    (w : (B.induce (remains (affected D))).Walk i k) :
    (L.graph.induce (remains D)).Reachable (L.representative i) (L.representative k) := by
  induction w with
  | nil => exact Reachable.refl _
  | cons e w iw => exact (L.reach_baseEdge conA e).trans iw

omit [Fintype U] [Fintype J] in
private theorem low_damage_escape {D : Finset (Host J r)} {i : J}
    (sd : D.card≤2) (hit : i∈affected D)
    (loc : (D.filter (fun v=>v.1=i)).card≤1) :
    ∃ j : Fin 3, L.p (i,j)∉D ∧ L.target (i,j)∉affected D := by
  classical
  let F : Finset (Fin 3) := univ.filter (fun j=>L.p (i,j)∈D)
  let T : Finset (Fin 3) := univ.filter (fun j=>L.target (i,j)∈affected D)
  have nF : F.card≤1 := by
    have sub : F.image (fun j=>L.p (i,j)) ⊆ D.filter (fun v=>v.1=i) := by
      intro x h
      obtain ⟨j,jF,rfl⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨(mem_filter.mp jF).2,rfl⟩
    have b := card_le_card sub
    rw [card_image_of_injective _ (fun _ _ e=>congrArg Prod.snd (L.p_inj e))] at b
    exact b.trans loc
  have nT : T.card≤1 := by
    have sub : T.image (fun j=>L.target (i,j)) ⊆ (affected D).erase i := by
      intro x h
      obtain ⟨j,jT,rfl⟩ := mem_image.mp h
      exact mem_erase.mpr ⟨L.target_ne (i,j),(mem_filter.mp jT).2⟩
    have inj : Function.Injective (fun j=>L.target (i,j)) := by
      intro j k e
      have same := L.slot_eq_of_target (s:=(i,j)) (t:=(i,k)) rfl e
      exact congrArg (fun b : J×Fin 3=>b.2) same
    have b := card_le_card sub
    rw [card_image_of_injective _ inj,card_erase_of_mem hit] at b
    have n := (affected_bound D).trans sd
    omega
  have lt : (F∪T).card < (univ : Finset (Fin 3)).card := by
    have n := card_union_le F T
    simp only [card_univ,Fintype.card_fin]
    omega
  obtain ⟨j,_,no⟩ := exists_mem_not_mem_of_card_lt_card lt
  exact ⟨j,fun h=>no (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)),
     fun h=>no (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩))⟩

omit [Fintype U] [DecidableEq U] [Fintype J] in
private theorem damage_stays_here {D : Finset (Host J r)} {i : J}
    (small : D.card≤2) (notSmall : ¬(D.filter (fun v=>v.1=i)).card≤1)
    {k : J} (ne : k≠i) : k∉affected D := by
  have eq : D.filter (fun v=>v.1=i)=D :=
    eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  intro h
  obtain ⟨v,vd,vk⟩ := mem_image.mp h
  have vv : v∈D.filter (fun w=>w.1=i) := eq.symm ▸ vd
  exact ne (vk.symm.trans ((mem_filter.mp vv).2))

omit [Fintype J] in
private theorem exit_high_damage {D : Finset (Host J r)}
    (x : remains D) (conA : KelmansStarter.ThreeConnected A)
    (small : D.card≤2) (notSmall : ¬(D.filter (fun v=>v.1=x.val.1)).card≤1) :
    ∃ k : remains (affected D),
      (L.graph.induce (remains D)).Reachable x (L.representative k) := by
  let i := x.val.1
  let S := localD D i
  have atMost : S.card≤2 := (localD_bound D i).trans ((card_filter_le _ _).trans small)
  have conS := conA.2 S atMost
  let u : remains S := ⟨x.val.2.val,fun h=>x.property (localD_iff.mp h)⟩
  let v : remains S := ⟨r,root_not_local D i⟩
  exact (conS u v).elim (fun walk => by
    obtain ⟨q,edge,reach⟩ := root_entry_walk r walk rfl x.val.2.property
    have qp := q.property
    change q.val∉insert r S at qp
    have nq : q.val≠r := fun eq=>qp (mem_insert.mpr (Or.inl eq))
    obtain ⟨j,jp⟩ := L.port_of_edge (u:=⟨q.val,nq⟩) edge
    let s : J×Fin 3 := (i,j)
    have eqPort : (liftCell q : remains D).val=L.p s := Prod.ext rfl jp.symm
    have surviving : L.p s∉D := by
      rw [←eqPort]
      exact (liftCell q : remains D).property
    have lq : liftCell q=(⟨L.p s,surviving⟩ : remains D) := Subtype.ext eqPort
    have healthy : L.target s∉affected D := damage_stays_here small notSmall (L.target_ne s)
    let k : remains (affected D) := ⟨L.target s,healthy⟩
    let t : remains D := ⟨L.q s,unaffected_survives healthy (L.q s).2⟩
    have first : (L.graph.induce (remains D)).Reachable x (liftCell q) :=
      reach.elim fun w => (w.map L.liftHom).reachable
    have mid : (L.graph.induce (remains D)).Adj (liftCell q) t := by
      rw [lq]
      exact L.edge_at_slot s
    have last : (L.graph.induce (remains D)).Reachable (L.representative k) t :=
      L.inside_reach rfl (local_connected_of_healthy conA healthy)
    exact ⟨k,first.trans (mid.reachable.trans last.symm)⟩)

omit [Fintype J] in
private theorem reaches_healthy {D : Finset (Host J r)} (x : remains D)
    (conA : KelmansStarter.ThreeConnected A) (small : D.card≤2) :
    ∃ k : remains (affected D),
      (L.graph.induce (remains D)).Reachable x (L.representative k) := by
  let i := x.val.1
  by_cases hi : i∈affected D
  · by_cases loc : (D.filter (fun v=>v.1=i)).card≤1
    · obtain ⟨j,pSurv,qHealthy⟩ := L.low_damage_escape small hi loc
      let s : J×Fin 3 := (i,j)
      let p : remains D := ⟨L.p s,pSurv⟩
      let q : remains D := ⟨L.q s,unaffected_survives qHealthy (L.q s).2⟩
      let k : remains (affected D) := ⟨L.target s,qHealthy⟩
      have left := L.inside_reach (x:=x) (y:=p) rfl
        (local_connected_of_few conA ((localD_bound D i).trans loc))
      have e : (L.graph.induce (remains D)).Adj p q := L.edge_at_slot s
      have right := L.inside_reach (x:=L.representative k) (y:=q) rfl
        (local_connected_of_healthy conA qHealthy)
      exact ⟨k,left.trans (e.reachable.trans right.symm)⟩
    · exact L.exit_high_damage x conA small loc
  · exact ⟨⟨i,hi⟩,L.inside_reach rfl
      (local_connected_of_healthy conA hi)⟩

/-- Replacing every vertex of a 3-connected cubic base by a common
rooted 3-connected brick preserves 3-connectivity. For a deletion
of at most two vertices, intact cells connect through the corresponding
induced base, and every surviving vertex can reach an intact cell. -/
theorem three_connected (conA : KelmansStarter.ThreeConnected A)
    (conB : KelmansStarter.ThreeConnected B) :
    KelmansStarter.ThreeConnected L.graph := by
  refine ⟨?_,?_⟩
  · rw [host_card]
    have n : 1≤Fintype.card U-1 := by have h:=conA.1; omega
    calc
      4 ≤ Fintype.card J := conB.1
      _ = Fintype.card J*1 := (Nat.mul_one _).symm
      _ ≤ Fintype.card J*(Fintype.card U-1) := Nat.mul_le_mul_left _ n
  · intro D small
    have baseCon := conB.2 (affected D) ((affected_bound D).trans small)
    haveI : Nonempty (remains D) := by
      obtain ⟨i⟩ := baseCon.nonempty
      exact ⟨L.representative i⟩
    constructor
    intro x y
    obtain ⟨i,Rx⟩ := L.reaches_healthy x conA small
    obtain ⟨k,Ry⟩ := L.reaches_healthy y conA small
    have mid := (baseCon i k).elim (fun w=>L.along_base conA w)
    exact Rx.trans (mid.trans Ry.symm)

#print axioms three_connected
end
end KelmansCactus.NearPerfectReplica.Layout
