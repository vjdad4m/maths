import ThreeSide189
import Mathlib.Data.List.Chain
namespace Graffiti189LongestPath.TwoCut
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

private theorem walk_of_chain (x : V) (l : List V) (h : List.Chain' G.Adj (x :: l)) :
    ∃ y, ∃ p : G.Walk x y, p.support = x :: l := by
  induction l generalizing x with
  | nil => exact ⟨x,.nil,rfl⟩
  | cons a l ih =>
    obtain ⟨y,p,hp⟩ := ih a h.tail
    exact ⟨y,.cons h.rel_head p,by simp [hp]⟩

private theorem clique_path (P : Finset V) (pos : 0<P.card)
    (complete : ∀ x∈P, ∀ y∈P, x≠y → G.Adj x y) :
    ∃ x∈P, ∃ y∈P, ∃ w : G.Walk x y, w.IsPath ∧ ∀ z, z∈w.support ↔ z∈P := by
  let l := P.toList
  have mem (x : V) : x∈l ↔ x∈P := by simp [l]
  have nd : l.Nodup := P.nodup_toList
  have llen : l.length=P.card := length_toList _
  have chain : List.Chain' G.Adj l := by
    apply List.Pairwise.chain'
    exact (List.pairwise_iff_getElem).mpr (fun i j hi hj lt =>
      complete l[i] ((mem _).mp (List.getElem_mem hi)) l[j] ((mem _).mp (List.getElem_mem hj))
        (fun e => (Nat.ne_of_lt lt) (List.Nodup.getElem_inj_iff nd |>.mp e)))
  cases e : l with
  | nil => simp [e] at llen; omega
  | cons x tail =>
    obtain ⟨y,w,ws⟩ := walk_of_chain x tail (e ▸ chain)
    have eq : w.support=l := ws.trans e.symm
    exact ⟨x,(mem x).mp (eq ▸ w.start_mem_support),y,(mem y).mp (eq ▸ w.end_mem_support),
      w,Walk.IsPath.mk' (eq.symm ▸ nd),fun z => eq ▸ mem z⟩

/-- Universal ports can be alternated with arbitrary other vertices. The
constructed path starts at a port and also ends at one if there are strictly
more ports than other vertices. -/
theorem path_from_universal_ports (P I : Finset V) (dis : Disjoint P I)
    (pos : 0<P.card) (cnt : I.card≤P.card)
    (cover : ∀ x∈P, ∀ y∈P∪I, x≠y → G.Adj x y) :
    ∃ x∈P, ∃ y, ∃ w : G.Walk x y,
      w.IsPath ∧ (∀ z, z∈w.support ↔ z∈P∪I) ∧ (I.card<P.card → y∈P) := by
  classical
  generalize e : I.card = n
  induction n using Nat.strong_induction_on generalizing P I with
  | h n ih =>
    by_cases empty : I=∅
    · subst I
      obtain ⟨x,xp,y,yp,w,hw,hs⟩ := clique_path P pos
        (fun x hx y hy ne => cover x hx y (mem_union.mpr (Or.inl hy)) ne)
      exact ⟨x,xp,y,w,hw,by simpa using hs,fun _ => yp⟩
    obtain ⟨r,ri⟩ := nonempty_iff_ne_empty.mpr empty
    obtain ⟨p,pp⟩ := card_pos.mp pos
    have rp : r∉P := fun h => disjoint_left.mp dis h ri
    have pr : p≠r := fun e => rp (e ▸ pp)
    have prA := cover p pp r (mem_union.mpr (Or.inr ri)) pr
    let Q := P.erase p
    let J := I.erase r
    have cq : Q.card = P.card-1 := card_erase_of_mem pp
    have cj : J.card = I.card-1 := card_erase_of_mem ri
    by_cases qpos : 0<Q.card
    · have ij : J.card < n := by
        have cp : 0<I.card := card_pos.mpr ⟨r,ri⟩
        omega
      have disJ : Disjoint Q J := dis.mono (erase_subset _ _) (erase_subset _ _)
      have co (x : V) (hx : x∈Q) (y : V) (hy : y∈Q∪J) (ne : x≠y) :
          G.Adj x y := by
        apply cover x (mem_erase.mp hx).2 y ?_ ne
        exact union_subset_union (erase_subset _ _) (erase_subset _ _) hy
      obtain ⟨q,qq,y,w,hw,hs,hy⟩ := ih J.card ij Q J disJ qpos (by omega) co rfl
      have qp := (mem_erase.mp qq).2
      have qr : q≠r := fun e => rp (e ▸ qp)
      have qrA := cover q qp r (mem_union.mpr (Or.inr ri)) qr
      have rn : r∉w.support := by
        intro h
        rcases mem_union.mp ((hs _).mp h) with h|h
        · exact rp (mem_erase.mp h).2
        · exact (mem_erase.mp h).1 rfl
      have pn : p∉(Walk.cons qrA.symm w).support := by
        simp only [support_cons,List.mem_cons]
        rintro (e|h)
        · exact pr e
        rcases mem_union.mp ((hs _).mp h) with h|h
        · exact (mem_erase.mp h).1 rfl
        · exact disjoint_left.mp dis pp (mem_erase.mp h).2
      refine ⟨p,pp,y,.cons prA (.cons qrA.symm w),(hw.cons rn).cons pn,?_,?_⟩
      · intro z
        simp only [support_cons,List.mem_cons,hs,mem_union,Q,J,mem_erase]
        constructor
        · rintro (rfl|rfl|h|h)
          · exact Or.inl pp
          · exact Or.inr ri
          · exact Or.inl h.2
          · exact Or.inr h.2
        · rintro (h|h)
          · by_cases e : z=p
            · exact Or.inl e
            · exact Or.inr (Or.inr (Or.inl ⟨e,h⟩))
          · by_cases e : z=r
            · exact Or.inr (Or.inl e)
            · exact Or.inr (Or.inr (Or.inr ⟨e,h⟩))
      · intro lt
        exact (mem_erase.mp (hy (by omega))).2
    · have Pone : P={p} := card_eq_one.mp (show P.card=1 by omega) |>.choose_spec |> fun h =>
        by
          obtain ⟨q,hq⟩ := card_eq_one.mp (show P.card=1 by omega)
          have pq : p=q := by simpa [hq] using pp
          simpa [pq] using hq
      have Ione : I={r} := by
        have c : 0<I.card := card_pos.mpr ⟨r,ri⟩
        obtain ⟨z,hz⟩ := card_eq_one.mp (show I.card=1 by omega)
        have rz : r=z := by simpa [hz] using ri
        simpa [rz] using hz
      refine ⟨p,pp,r,.cons prA .nil,cons_isPath_iff _ _ |>.mpr ⟨IsPath.nil,by simpa using pr⟩,?_,?_⟩
      · intro z
        simp [Pone,Ione]
      · intro lt
        have ci : I.card=1 := by simp [Ione]
        have cp : P.card=1 := by simp [Pone]
        omega

#print axioms path_from_universal_ports
end Graffiti189LongestPath.TwoCut
