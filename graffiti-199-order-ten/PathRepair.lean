import TwoShortShores

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Reverse an actual spanning path of an induced vertex set. -/
private def reversePath {A : Set V} (p : PathOn G A) : PathOn G A :=
  ⟨p.vertices.reverse,by simpa using p.nonempty,
    List.chain'_reverse.mpr (p.chain.imp (fun _ _ e => e.symm)),
    (List.nodup_reverse.mpr p.nodup),fun v => by simpa using p.covers v⟩

/-- Read a consecutive triple from indices on a list. -/
private theorem list_triple {L : List V} {i j k : Fin L.length}
    (ij : i.val + 1 = j.val) (jk : j.val + 1 = k.val) :
    ∃ frontPart tail : List V, L = frontPart ++ L.get i :: L.get j :: L.get k :: tail := by
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  have eq := List.take_append_drop i.val L
  rw [List.drop_eq_getElem_cons hi,ij,List.drop_eq_getElem_cons hj,jk,
    List.drop_eq_getElem_cons hk] at eq
  exact ⟨L.take i.val,L.drop (k.val+1),eq.symm⟩

variable [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

/-- Replace the three vertices s,y,z by s,z,y,r. The suffix need only
start at a neighbor of r if the suffix is nonempty. -/
theorem traceable_of_three_vertex_insertion {r s y z : V}
    (p : PathOn G {x | x ≠ r}) {frontPart tail : List V}
    (form : p.vertices = frontPart ++ s :: y :: z :: tail)
    (sz : G.Adj s z) (ry : G.Adj r y)
    (entry : ∀ w, tail.head? = some w → G.Adj r w) : Traceable G := by
  let fill : FilledPath G (G.neighborFinset r) r :=
    ⟨p.vertices,p.nonempty,p.nodup,p.covers,p.chain.imp (fun _ _ edge => Or.inl edge)⟩
  have path := p.chain
  rw [form] at path
  obtain ⟨left,_,middle⟩ := List.chain'_append_cons_cons.mp path
  have endChain : (r :: tail).Chain' G.Adj := middle.tail.tail.cons' (fun w h => entry w h)
  have suffix : (z :: y :: r :: tail).Chain' G.Adj :=
    List.chain'_cons.mpr ⟨middle.rel_head.symm,List.chain'_cons.mpr ⟨ry.symm,endChain⟩⟩
  have newPath : ((frontPart ++ [s]) ++ z :: y :: r :: tail).Chain' G.Adj := by
    apply left.append suffix
    intro x hx w hw
    have ex : s = x := by simpa using hx
    have ew : z = w := by simpa using hw
    exact ex ▸ ew ▸ sz
  let front := frontPart ++ [s]
  have swap : (front ++ z :: y :: tail).Perm (front ++ y :: z :: tail) :=
    (List.Perm.swap y z tail).append_left front
  have insertR : (front ++ z :: y :: r :: tail).Perm (r :: (front ++ z :: y :: tail)) := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using
      (List.perm_middle (a := r) (l₁ := front ++ [z,y]) (l₂ := tail))
  have perm : ((frontPart ++ [s]) ++ z :: y :: r :: tail).Perm (r :: p.vertices) := by
    rw [form]
    simpa only [front,List.append_assoc,List.cons_append,List.nil_append] using
      insertR.trans (swap.cons r)
  exact traceable_from_augmented_fill fill perm newPath

variable {A : Set V} {D : Finset V}

private theorem shore_path_triple (S : ThreeVertexShore G A)
    (size : D.card = 3) (off : ∀ v ∈ D, v ∉ A)
    (boundary : ShoreBoundary G D A) (degree : G.degree S.left = 3)
    (p : PathOn G {x | x ≠ S.left}) (no : ¬ Traceable G) :
    ∃ s ∈ D, ¬ G.Adj S.left s ∧
      ∃ P : PathOn G {x | x ≠ S.left}, ∃ frontPart tail : List V,
        P.vertices = frontPart ++ s :: S.middle :: S.right :: tail := by
  classical
  have middleMem : S.middle ∈ A :=
    Eq.mpr (congrArg (fun U : Set V => S.middle ∈ U) S.shape) (by simp)
  have split (v : V) (vA : v ∈ A) : v = S.left ∨ v = S.middle ∨ v = S.right := by
    have h : v ∈ ({S.left,S.middle,S.right} : Set V) := S.shape ▸ vA
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
  obtain ⟨i,j,ij,iA,ri,jA,rj⟩ := cubic_shore_has_internal_flank size off boundary
    S.left_mem degree ⟨S.middle,middleMem,S.lm⟩ p no
  have mid : p.vertices.get i = S.middle := by
    rcases split _ iA with e|e|e
    · exact (G.loopless _ (e ▸ ri)).elim
    · exact e
    · exact (S.noLR (e ▸ ri)).elim
  have right : p.vertices.get j = S.right := by
    rcases split _ jA with e|e|e
    · exact ((p.covers _).mp (List.get_mem _ _) e).elim
    · exact (rj (e.symm ▸ S.lm)).elim
    · exact e
  have port (k : Fin p.vertices.length) (ki : G.Adj (p.vertices.get i) (p.vertices.get k))
      (rk : ¬ G.Adj S.left (p.vertices.get k)) (ne : k ≠ j) :
      p.vertices.get k ∈ D := by
    apply boundary _ iA _ _ ki
    intro kA
    rcases split _ kA with e|e|e
    · exact (p.covers _).mp (List.get_mem _ _) e
    · exact rk (e.symm ▸ S.lm)
    · exact ne ((List.nodup_iff_injective_get.mp p.nodup) (e.trans right.symm))
  obtain ⟨⟨before,hbefore,ib,rb⟩,⟨after,hafter,ia,ra⟩⟩ := path_flanks_of_nontraceable p no i ri
  rcases ij with ij|ji
  · have ne : before ≠ j := by intro e; rw [e] at hbefore; omega
    obtain ⟨frontPart,tail,shape⟩ := list_triple hbefore ij
    refine ⟨p.vertices.get before,port before ib rb ne,rb,p,frontPart,tail,?_⟩
    simpa only [mid,right] using shape
  · have ne : after ≠ j := by intro e; rw [e] at hafter; omega
    obtain ⟨frontPart,tail,shape⟩ := list_triple ji hafter
    refine ⟨p.vertices.get after,port after ia ra ne,ra,reversePath p,tail.reverse,frontPart.reverse,?_⟩
    rw [mid,right] at shape
    have rev := congrArg List.reverse shape
    simpa only [reversePath,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.append_assoc,List.cons_append,List.nil_append] using rev

/-- In a nontraceable graph with a spanning path after cubic deletion, a
three-vertex path component with a cubic endpoint has two cubic vertices
with the same neighborhood. The third port touches the middle. -/
theorem cubic_three_vertex_shore_profile (S : ThreeVertexShore G A)
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (off : ∀ v ∈ D, v ∉ A) (boundary : ShoreBoundary G D A)
    (degree : G.degree S.left = 3) (p : PathOn G {x | x ≠ S.left}) (no : ¬ Traceable G) :
    ∃ s ∈ D, G.Adj s S.middle ∧
      G.neighborFinset S.left = insert S.middle (D.erase s) ∧
      G.neighborFinset S.right = insert S.middle (D.erase s) := by
  classical
  obtain ⟨s,sD,rs,P,frontPart,tail,shape⟩ := shore_path_triple S size off boundary degree p no
  have split (v : V) (vA : v ∈ A) : v = S.left ∨ v = S.middle ∨ v = S.right := by
    have h : v ∈ ({S.left,S.middle,S.right} : Set V) := S.shape ▸ vA
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
  have middleMem : S.middle ∈ A :=
    Eq.mpr (congrArg (fun U : Set V => S.middle ∈ U) S.shape) (by simp)
  let N := insert S.middle (D.erase s)
  have cardN : N.card = 3 := by
    change (insert S.middle (D.erase s)).card = 3
    rw [Finset.card_insert_of_not_mem (fun h => off _ (Finset.mem_of_mem_erase h) middleMem),
      Finset.card_erase_of_mem sD,size]
  have common (v : V) (vA : v ∈ A) (center : ∀ w ∈ A, G.Adj v w → w = S.middle)
      (ns : ¬ G.Adj v s) : G.neighborFinset v ⊆ N := by
    intro x hx
    have vx := (G.mem_neighborFinset _ _).mp hx
    by_cases xA : x ∈ A
    · rw [center _ xA vx]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
        ⟨fun e => ns (e ▸ vx),boundary _ vA _ xA vx⟩)
  have eqR : G.neighborFinset S.left = N := by
    apply Finset.eq_of_subset_of_card_le (common _ S.left_mem _ rs)
    · rw [cardN,G.card_neighborFinset_eq_degree,degree]
    · intro w wA edge
      rcases split _ wA with e|e|e
      · exact (G.loopless _ (e ▸ edge)).elim
      · exact e
      · exact (S.noLR (e ▸ edge)).elim
  have noSZ : ¬ G.Adj s S.right := by
    intro sz
    apply no (traceable_of_three_vertex_insertion P shape sz S.lm _)
    intro w hw
    have wMem := List.mem_of_mem_head? (show w ∈ tail.head? from hw)
    have hChain := P.chain
    rw [shape] at hChain
    have zw := (List.chain'_append_cons_cons.mp hChain).2.2.tail.rel_head? (show w ∈ tail.head? from hw)
    have noEarlier (v : V) (hv : v ∈ [s,S.middle,S.right]) : v ∉ tail := by
      have nd := P.nodup
      rw [shape] at nd
      have nd' : ([s,S.middle,S.right] ++ tail).Nodup := (List.nodup_append.mp nd).2.1
      exact fun h => (List.nodup_append.mp nd').2.2 hv h
    have offA : w ∉ A := by
      intro wA
      rcases split _ wA with e|e|e
      · have wg : w ∈ P.vertices := by rw [shape]; simp [wMem]
        exact (P.covers w).mp wg e
      · exact noEarlier w (by simp [e]) wMem
      · exact noEarlier w (by simp [e]) wMem
    have wD := boundary _ S.right_mem _ offA zw
    have ws : w ≠ s := fun e => noEarlier w (by simp [e]) wMem
    apply (G.mem_neighborFinset _ _).mp
    rw [eqR]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨ws,wD⟩)
  have low := degree_of_small_deletion_preconnected (G := G)
    (by have n := conn.1; omega : 4 ≤ Fintype.card V)
    (fun K hK => (conn.2 K hK).preconnected) S.right
  have eqZ : G.neighborFinset S.right = N := by
    apply Finset.eq_of_subset_of_card_le (common _ S.right_mem _ (fun h => noSZ h.symm))
    · rw [cardN,G.card_neighborFinset_eq_degree]
      exact low
    · intro w wA edge
      rcases split _ wA with e|e|e
      · exact (S.noLR (e ▸ edge).symm).elim
      · exact e
      · exact (G.loopless _ (e ▸ edge)).elim
  have sy := P.chain
  rw [shape] at sy
  exact ⟨s,sD,(List.chain'_append_cons_cons.mp sy).2.1,eqR,eqZ⟩

theorem neighborFinset_eq_of_cubic_three_vertex_shore (S : ThreeVertexShore G A)
    (conn : ConnectivityAtLeast G 3) (size : D.card = 3)
    (off : ∀ v ∈ D, v ∉ A) (boundary : ShoreBoundary G D A)
    (degree : G.degree S.left = 3) (p : PathOn G {x | x ≠ S.left}) (no : ¬ Traceable G) :
    G.neighborFinset S.left = G.neighborFinset S.right := by
  obtain ⟨_,_,_,eqL,eqR⟩ := cubic_three_vertex_shore_profile S conn size off boundary degree p no
  exact eqL.trans eqR.symm

#print axioms cubic_three_vertex_shore_profile
#print axioms traceable_of_three_vertex_insertion
#print axioms neighborFinset_eq_of_cubic_three_vertex_shore

end Graffiti199Depleted.Catalogue
