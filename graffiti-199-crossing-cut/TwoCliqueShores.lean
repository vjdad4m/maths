import CubicPortProfiles

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private theorem two_distinct_contacts [Fintype V] [DecidableEq V] {A : Set V} {p q r : V}
    (conn : ConnectivityAtLeast G 3) (pr : p ≠ r)
    (outside : ∀ d ∈ ({p,q,r} : Finset V), d ∉ A)
    (boundary : ShoreBoundary G {p,q,r} A)
    (nontrivial : ∃ a ∈ A, ∃ b ∈ A, a ≠ b) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ G.Adj p a ∧ G.Adj q b := by
  classical
  let D : Finset V := {p,q,r}
  have size : D.card ≤ 3 := by
    change (insert p ({q,r} : Finset V)).card ≤ 3
    have a := Finset.card_insert_le p ({q,r} : Finset V)
    have b := Finset.card_insert_le q ({r} : Finset V)
    have c : ({r} : Finset V).card = 1 := Finset.card_singleton _
    omega
  obtain ⟨a,ha,b,hb,ab⟩ := nontrivial
  obtain ⟨x,xA,px⟩ := contact_of_shore conn size outside boundary ⟨a,ha⟩
    (show p ∈ D from by simp [D])
  obtain ⟨y,yA,qy⟩ := contact_of_shore conn size outside boundary ⟨a,ha⟩
    (show q ∈ D from by simp [D])
  by_cases xy : x = y
  · subst y
    apply Classical.byContradiction
    intro bad
    have soleP (u : V) (uA : u ∈ A) (pu : G.Adj p u) : u = x :=
      Classical.byContradiction (fun ne => bad ⟨u,uA,x,xA,ne,pu,qy⟩)
    have soleQ (u : V) (uA : u ∈ A) (qu : G.Adj q u) : u = x :=
      Classical.byContradiction (fun ne => bad ⟨x,xA,u,uA,Ne.symm ne,px,qu⟩)
    let U : Finset V := {x,r}
    have small : U.card < 3 := by
      have b := Finset.card_insert_le x ({r} : Finset V)
      rw [Finset.card_singleton] at b
      exact lt_of_le_of_lt b (by decide)
    let M : Set V := {v | v ∉ U}
    have rA : r ∉ A := outside r (by simp)
    have pA : p ∉ A := outside p (by simp)
    have pKeep : p ∈ M := by
      change p ∉ U
      simp [U,pr,show p ≠ x from fun e => pA (e.symm ▸ xA)]
    have witness : ∃ v ∈ A, v ∈ M := by
      by_cases ax : a = x
      · exact ⟨b,hb,by
          change b ∉ U
          simp [U,show b ≠ x from fun e => ab (ax.trans e.symm),
            show b ≠ r from fun e => rA (e ▸ hb)]⟩
      · exact ⟨a,ha,by
          change a ∉ U
          simp [U,ax,show a ≠ r from fun e => rA (e ▸ ha)]⟩
    obtain ⟨v,vA,vKeep⟩ := witness
    obtain ⟨w⟩ := (conn.2 U small).preconnected ⟨v,vKeep⟩ ⟨p,pKeep⟩
    obtain ⟨u,uA,s,sA,us⟩ := crossingOnWalk (U := {t : M | t.val ∈ A}) w vA pA
    have inD : s.val ∈ D := boundary u.val uA s.val sA us
    have offX : u.val ≠ x := fun e => u.property (by simp [U,e])
    have offR : s.val ≠ r := fun e => s.property (by simp [U,e])
    rcases (show s.val = p ∨ s.val = q ∨ s.val = r by simpa [D] using inD) with ep|eq|er
    · exact offX (soleP _ uA (ep ▸ (show G.Adj s.val u.val from us.symm)))
    · exact offX (soleQ _ uA (eq ▸ (show G.Adj s.val u.val from us.symm)))
    · exact offR er
  · exact ⟨x,xA,y,yA,xy,px,qy⟩

private theorem clique_path_between [Fintype V] {A : Set V} {a b : V}
    (clique : A.Pairwise G.Adj) (aA : a ∈ A) (bA : b ∈ A) (ab : a ≠ b) :
    ∃ p : PathOn G A, p.first = a ∧ p.last = b := by
  classical
  let R := ((Finset.univ : Finset V).filter fun v => v ∈ A ∧ v ≠ a ∧ v ≠ b).toList
  let L := a :: R ++ [b]
  have rmem (v : V) : v ∈ R ↔ v ∈ A ∧ v ≠ a ∧ v ≠ b := by simp [R]
  have lr (v : V) : v ∈ L ↔ v ∈ A := by
    constructor
    · intro h
      rcases (show v = a ∨ (v ∈ A ∧ v ≠ a ∧ v ≠ b) ∨ v = b by simpa [L,rmem] using h) with rfl|hc|rfl
      · exact aA
      · exact hc.1
      · exact bA
    · intro h
      by_cases ha : v = a
      · simp [L,ha]
      · by_cases hb : v = b
        · simp [L,hb]
        · simp [L,rmem,h,ha,hb]
  have rn : R.Nodup := Finset.nodup_toList _
  have nd : L.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_,List.nodup_append.mpr ⟨rn,by simp,?_⟩⟩
    · simp [rmem,ab]
    · intro x mx xb
      have e : x = b := by simpa using xb
      exact ((rmem x).mp mx).2.2 e
  have edges : L.Chain' G.Adj := by
    apply List.Pairwise.chain'
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt
    apply clique (lr _ |>.mp (List.getElem_mem hi)) (lr _ |>.mp (List.getElem_mem hj))
    intro eq
    have same : L.get ⟨i,hi⟩ = L.get ⟨j,hj⟩ := eq
    have e := (List.nodup_iff_injective_get.mp nd) same
    have indices := congrArg Fin.val e
    change i = j at indices
    omega
  let p : PathOn G A := ⟨L,by simp [L],edges,nd,lr⟩
  have last : p.last = b := by
    change (a :: R ++ [b]).getLast _ = b
    exact List.getLast_append_of_right_ne_nil (a :: R) [b] (by simp)
  exact ⟨p,rfl,last⟩

private def singletonPath (G : SimpleGraph V) (x : V) : PathOn G ({x} : Set V) :=
  ⟨[x],by simp,List.chain'_singleton _,by simp,fun _ => by simp⟩

private theorem join_last {A B : Set V} (p : PathOn G A) (q : PathOn G B)
    (apart : Disjoint A B) (e : G.Adj p.last q.first) : (p.join q apart e).last = q.last :=
  List.getLast_append_of_right_ne_nil _ _ q.nonempty

/-- When a three-cut separates two nontrivial clique shores, two distinct
contacts on each shore permit a Hamiltonian path across all three ports. -/
theorem traceable_of_two_clique_shores [Fintype V] {D : Finset V} {A B : Set V}
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (apart : Disjoint A B)
    (outsideA : ∀ d ∈ D, d ∉ A) (outsideB : ∀ d ∈ D, d ∉ B)
    (boundaryA : ShoreBoundary G D A) (boundaryB : ShoreBoundary G D B)
    (cliqueA : A.Pairwise G.Adj) (cliqueB : B.Pairwise G.Adj)
    (nontrivialA : ∃ a ∈ A, ∃ b ∈ A, a ≠ b) (nontrivialB : ∃ a ∈ B, ∃ b ∈ B, a ≠ b)
    (cover : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ D) : Traceable G := by
  classical
  obtain ⟨p,q,r,pq,pr,qr,rfl⟩ := Finset.card_eq_three.mp size
  have outsideB' : ∀ d ∈ ({q,r,p} : Finset V), d ∉ B := by
    intro d hd
    apply outsideB d
    simpa only [Finset.mem_insert,Finset.mem_singleton,or_left_comm,or_comm] using hd
  have boundaryB' : ShoreBoundary G {q,r,p} B := by
    intro x xB y yB xy
    have h := boundaryB x xB y yB xy
    simpa only [Finset.mem_insert,Finset.mem_singleton,or_left_comm,or_comm] using h
  obtain ⟨a,aA,a',aA',aa',pa,qa'⟩ := two_distinct_contacts conn pr outsideA boundaryA nontrivialA
  obtain ⟨b,bB,b',bB',bb',qb,rb'⟩ := two_distinct_contacts conn pq.symm outsideB' boundaryB' nontrivialB
  obtain ⟨P,Pfirst,Plast⟩ := clique_path_between cliqueA aA aA' aa'
  obtain ⟨Q,Qfirst,Qlast⟩ := clique_path_between cliqueB bB bB' bb'
  have away1 : Disjoint ({p} : Set V) A := by
    apply Set.disjoint_left.mpr
    intro v hv vA
    have eq : v = p := hv
    exact outsideA p (by simp) (eq ▸ vA)
  let P1 := (singletonPath G p).join P away1 (Pfirst.symm ▸ pa)
  have end1 : P1.last = a' := (join_last ..).trans Plast
  have away2 : Disjoint (({p} : Set V) ∪ A) {q} := by
    apply Set.disjoint_left.mpr
    rintro v (mem|mem) vq
    · exact pq ((show v = p from mem).symm.trans (show v = q from vq))
    · exact outsideA q (by simp) ((show v = q from vq) ▸ mem)
  let P2 := P1.join (singletonPath G q) away2 (end1.symm ▸ qa'.symm)
  have end2 : P2.last = q := join_last ..
  have away3 : Disjoint ((({p} : Set V) ∪ A) ∪ {q}) B := by
    apply Set.disjoint_left.mpr
    rintro v ((vp|vA)|vq) vB
    · exact outsideB p (by simp) ((show v = p from vp) ▸ vB)
    · exact Set.disjoint_left.mp apart vA vB
    · exact outsideB q (by simp) ((show v = q from vq) ▸ vB)
  let P3 := P2.join Q away3 (end2.symm ▸ Qfirst.symm ▸ qb)
  have end3 : P3.last = b' := (join_last ..).trans Qlast
  have away4 : Disjoint (((({p} : Set V) ∪ A) ∪ {q}) ∪ B) {r} := by
    apply Set.disjoint_left.mpr
    rintro v (((hp|ha)|hq)|hb) hr
    · exact pr ((show v = p from hp).symm.trans (show v = r from hr))
    · exact outsideA r (by simp) ((show v = r from hr) ▸ ha)
    · exact qr ((show v = q from hq).symm.trans (show v = r from hr))
    · exact outsideB r (by simp) ((show v = r from hr) ▸ hb)
  let P4 := P3.join (singletonPath G r) away4 (end3.symm ▸ rb'.symm)
  have full : ((((({p} : Set V) ∪ A) ∪ {q}) ∪ B) ∪ {r}) = Set.univ := by
    ext v
    have h := cover v
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_univ,iff_true]
    tauto
  exact traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp ⟨full ▸ P4⟩)

#print axioms traceable_of_two_clique_shores

end Graffiti199Depleted.Catalogue
