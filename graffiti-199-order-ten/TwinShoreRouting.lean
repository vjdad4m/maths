import PathRepair

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]
variable {B : Set V}

/-- Insert a spanning shore route between two disjoint path pieces which
together cover exactly the rest of the graph. -/
theorem traceable_of_route_between_lists {p q : V} {L R : List V}
    (route : ShoreRoute G B p q)
    (left : L.Chain' G.Adj) (right : R.Chain' G.Adj)
    (entry : L.getLast? = some p) (exit : R.head? = some q)
    (nd : (L ++ R).Nodup) (coverage : ∀ v, v ∈ L ++ R ↔ v ∉ B) : Traceable G := by
  obtain ⟨a,b,pa,bq,P,pf,pl⟩ := route
  have pFirst : P.vertices.head? = some a := (List.head_eq_iff_head?_eq_some P.nonempty).mp pf
  have pLast : P.vertices.getLast? = some b := by rw [List.getLast?_eq_getLast P.nonempty]; exact congrArg some pl
  have chain₁ := left.append P.chain (by
    intro x hx y hy
    have xp : p = x := by simpa [entry] using hx
    have ya : a = y := by simpa [pFirst] using hy
    exact xp ▸ ya ▸ pa)
  have nChain := chain₁.append right (by
    intro x hx y hy
    have suffix : (L ++ P.vertices).getLast? = some b := by
      rw [List.getLast?_append_of_ne_nil _ P.nonempty,pLast]
    have xb : b = x := by simpa [suffix] using hx
    have yq : q = y := by simpa [exit] using hy
    exact xb ▸ yq ▸ bq)
  obtain ⟨ln,rn,lr⟩ := List.nodup_append.mp nd
  have separate (v : V) (hv : v ∈ L ++ R) (vp : v ∈ P.vertices) : False :=
    (coverage v).mp hv ((P.covers v).mp vp)
  have distinct : (L ++ P.vertices ++ R).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨List.nodup_append.mpr ⟨ln,P.nodup,?_⟩,rn,?_⟩
    · exact fun v vL vp => separate v (List.mem_append_left _ vL) vp
    · intro v hv vr
      rcases List.mem_append.mp hv with hL|hp
      · exact lr hL vr
      · exact separate v (List.mem_append_right _ vr) hp
  have full (v : V) : v ∈ L ++ P.vertices ++ R := by
    by_cases hv : v ∈ B
    · exact List.mem_append_left _ (List.mem_append_right _ ((P.covers v).mpr hv))
    · rcases List.mem_append.mp ((coverage v).mpr hv) with hL|hR
      · exact List.mem_append_left _ (List.mem_append_left _ hL)
      · exact List.mem_append_right _ hR
  have nonempty : L ++ P.vertices ++ R ≠ [] := fun h =>
    P.nonempty (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).2
  exact traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp
    ⟨⟨_,nonempty,nChain,distinct,fun v => iff_of_true (full v) trivial⟩⟩)

variable {A : Set V}

private theorem reverse_or_permuted_pair {p q s a b : V}
    (aD : a ∈ ({p,q,s} : Finset V)) (bD : b ∈ ({p,q,s} : Finset V))
    (ab : a ≠ b) (route : ShoreRoute G B a b) :
    ShoreRoute G B p q ∨ ShoreRoute G B s p ∨ ShoreRoute G B s q := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at aD bD
  rcases aD with e|e|e <;> subst a <;> rcases bD with e|e|e <;> subst b
  · exact (ab rfl).elim
  · exact Or.inl route
  · exact Or.inr (Or.inl route.reverse)
  · exact Or.inl route.reverse
  · exact (ab rfl).elim
  · exact Or.inr (Or.inr route.reverse)
  · exact Or.inr (Or.inl route)
  · exact Or.inr (Or.inr route)
  · exact (ab rfl).elim

/-- A three-vertex path whose endpoints share two ports can absorb any
single spanning route on the other component. The pair using those two
shared ports is handled by visiting the path component in two pieces. -/
theorem traceable_of_twin_path_shore_and_route
    (S : ThreeVertexShore G A) {p q s a b : V}
    (pq : p ≠ q) (ps : p ≠ s) (qs : q ≠ s)
    (offA : ∀ v ∈ ({p,q,s} : Finset V), v ∉ A)
    (offB : ∀ v ∈ ({p,q,s} : Finset V), v ∉ B)
    (apart : Disjoint A B) (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ ({p,q,s} : Finset V))
    (pu : G.Adj p S.left) (qu : G.Adj q S.left)
    (pz : G.Adj p S.right) (qz : G.Adj q S.right)
    (sy : G.Adj s S.middle)
    (aD : a ∈ ({p,q,s} : Finset V)) (bD : b ∈ ({p,q,s} : Finset V))
    (ab : a ≠ b) (route : ShoreRoute G B a b) : Traceable G := by
  have middleMem : S.middle ∈ A :=
    Eq.mpr (congrArg (fun U : Set V => S.middle ∈ U) S.shape) (by simp)
  have offport (v u : V) (vD : v ∈ ({p,q,s} : Finset V)) (uA : u ∈ A) : v ≠ u :=
    fun e => offA v vD (e.symm ▸ uA)
  have npL := offport p S.left (by simp) S.left_mem
  have npM := offport p S.middle (by simp) middleMem
  have npR := offport p S.right (by simp) S.right_mem
  have nqL := offport q S.left (by simp) S.left_mem
  have nqM := offport q S.middle (by simp) middleMem
  have nqR := offport q S.right (by simp) S.right_mem
  have nsL := offport s S.left (by simp) S.left_mem
  have nsM := offport s S.middle (by simp) middleMem
  have nsR := offport s S.right (by simp) S.right_mem
  have outside (v : V) : v ∉ B ↔ v ∈ A ∨ v ∈ ({p,q,s} : Finset V) := by
    constructor
    · intro h
      rcases cover v with va|vb|vd
      · exact Or.inl va
      · exact (h vb).elim
      · exact Or.inr vd
    · rintro (va|vd)
      · exact Set.disjoint_left.mp apart va
      · exact offB _ vd
  have certify (L R : List V) (perm : (L ++ R).Perm [s,S.middle,S.left,p,q,S.right]) :
      (L ++ R).Nodup ∧ (∀ v, v ∈ L ++ R ↔ v ∉ B) := by
    constructor
    · apply (List.Perm.nodup_iff perm).mpr
      simp [pq,ps.symm,qs.symm,npL.symm,npM.symm,npR,nqL.symm,nqM.symm,nqR,
        nsL,nsM,nsR,S.lm.ne.symm,S.mr.ne,S.lr]
    · intro v
      rw [perm.mem_iff,outside]
      have eq : v ∈ A ↔ v = S.left ∨ v = S.middle ∨ v = S.right := by
        conv_lhs => rw [S.shape]
        simp
      simp only [eq,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,List.not_mem_nil,or_false]
      constructor
      · rintro (hs|hy|hu|hp|hq|hz)
        · exact Or.inr (Or.inr (Or.inr hs))
        · exact Or.inl (Or.inr (Or.inl hy))
        · exact Or.inl (Or.inl hu)
        · exact Or.inr (Or.inl hp)
        · exact Or.inr (Or.inr (Or.inl hq))
        · exact Or.inl (Or.inr (Or.inr hz))
      · rintro ((hu|hy|hz)|(hp|hq|hs))
        · exact Or.inr (Or.inr (Or.inl hu))
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hz))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq))))
        · exact Or.inl hs
  let readVertex : Fin 6 → V := ![s,S.middle,S.left,p,q,S.right]
  have permute (indices : List (Fin 6)) (h : indices.Perm [0,1,2,3,4,5]) :
      (indices.map readVertex).Perm [s,S.middle,S.left,p,q,S.right] := h.map readVertex
  rcases reverse_or_permuted_pair aD bD ab route with pqRoute|spRoute|sqRoute
  · have proof := certify [s,S.middle,S.left,p] [q,S.right] (by simp)
    exact traceable_of_route_between_lists (L := [s,S.middle,S.left,p]) (R := [q,S.right])
      pqRoute (by simp [List.chain'_cons,sy,S.lm.symm,pu.symm])
      (List.chain'_pair.mpr qz) (by simp) (by simp) proof.1 proof.2
  · have proof := certify [S.left,q,S.right,S.middle,s] [p]
      (permute [2,4,5,1,0,3] (by decide))
    exact traceable_of_route_between_lists (L := [S.left,q,S.right,S.middle,s]) (R := [p])
      spRoute (by simp [List.chain'_cons,qu.symm,qz,S.mr.symm,sy.symm])
      (List.chain'_singleton _) (by simp) (by simp) proof.1 proof.2
  · have proof := certify [S.left,p,S.right,S.middle,s] [q]
      (permute [2,3,5,1,0,4] (by decide))
    exact traceable_of_route_between_lists (L := [S.left,p,S.right,S.middle,s]) (R := [q])
      sqRoute (by simp [List.chain'_cons,pu.symm,pz,S.mr.symm,sy.symm])
      (List.chain'_singleton _) (by simp) (by simp) proof.1 proof.2

variable [Fintype V] [DecidableRel G.Adj]
variable {D : Finset V}

/-- A cubic endpoint on a three-vertex path component forces traceability
if the other component has any single spanning route between two ports. -/
theorem traceable_of_cubic_path_shore_and_route (S : ThreeVertexShore G A)
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundary : ShoreBoundary G D A) (apart : Disjoint A B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D)
    (degree : G.degree S.left = 3) (P : PathOn G {x | x ≠ S.left})
    {a b : V} (aD : a ∈ D) (bD : b ∈ D) (ab : a ≠ b) (route : ShoreRoute G B a b) :
    Traceable G := by
  classical
  by_contra no
  obtain ⟨s,sD,sy,eqU,eqZ⟩ := cubic_three_vertex_shore_profile S conn size offA boundary degree P no
  have count : (D.erase s).card = 2 := by rw [Finset.card_erase_of_mem sD,size]
  obtain ⟨p,q,pq,ports⟩ := Finset.card_eq_two.mp count
  have pE : p ∈ D.erase s := ports.symm ▸ (by simp : p ∈ ({p,q} : Finset V))
  have qE : q ∈ D.erase s := ports.symm ▸ (by simp : q ∈ ({p,q} : Finset V))
  have ps := (Finset.mem_erase.mp pE).1
  have qs := (Finset.mem_erase.mp qE).1
  have frame : D = {p,q,s} := by
    rw [← Finset.insert_erase sD,ports]
    ext v
    simp only [Finset.mem_insert,Finset.mem_singleton]
    tauto
  have adjU (v : V) (vE : v ∈ D.erase s) : G.Adj v S.left :=
    ((G.mem_neighborFinset _ _).mp (eqU.symm ▸ Finset.mem_insert_of_mem vE)).symm
  have adjZ (v : V) (vE : v ∈ D.erase s) : G.Adj v S.right :=
    ((G.mem_neighborFinset _ _).mp (eqZ.symm ▸ Finset.mem_insert_of_mem vE)).symm
  exact no (traceable_of_twin_path_shore_and_route S pq ps qs (frame ▸ offA) (frame ▸ offB)
    apart (frame ▸ cover) (adjU p pE) (adjU q qE) (adjZ p pE) (adjZ q qE) sy
    (frame ▸ aD) (frame ▸ bD) ab route)

universe w
/-- Supply the deletion path from the minimum-order independent-cubic
reduction rather than assuming a separate path hypothesis. -/
theorem traceable_of_minimum_cubic_path_shore_and_route
    {W : Type w} {H : SimpleGraph W} [DecidableEq W] [Fintype W] [DecidableRel H.Adj]
    {A B : Set W} {D : Finset W} (S : ThreeVertexShore H A)
    (smaller : SmallerAtThree.{w} (Fintype.card W))
    (conn : ConnectivityAtLeast H 3) (budget : treeNumber H ≤ 5)
    (order : 5 ≤ Fintype.card W)
    (ind : ∀ x y, H.degree x = 3 → H.degree y = 3 → ¬ H.Adj x y)
    (size : D.card = 3) (offA : ∀ v ∈ D, v ∉ A) (offB : ∀ v ∈ D, v ∉ B)
    (boundary : ShoreBoundary H D A) (apart : Disjoint A B)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D) (degree : H.degree S.left = 3)
    {a b : W} (aD : a ∈ D) (bD : b ∈ D) (ab : a ≠ b) (route : ShoreRoute H B a b) :
    Traceable H := by
  by_contra no
  obtain ⟨P⟩ := pathOn_of_traceable_delete
    (traceable_after_cubic_delete smaller conn budget order no ind degree)
  exact no (traceable_of_cubic_path_shore_and_route S conn size offA offB boundary apart cover
    degree P aD bD ab route)

#print axioms traceable_of_route_between_lists
#print axioms traceable_of_twin_path_shore_and_route
#print axioms traceable_of_cubic_path_shore_and_route
#print axioms traceable_of_minimum_cubic_path_shore_and_route

end Graffiti199Depleted.Catalogue
