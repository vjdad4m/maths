import P5CliqueFourPortCommonRelayFans133
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem one_edge_triple_path9_of_ordered_adjacency (f : Fin 9→V)
    (h : ∀ i j, i<j → (G.Adj (f i) (f j) ↔ i.val+1=j.val)) : InducedPath G f := by
  refine ⟨?_,h⟩
  have noEq (i j : Fin 9) (lt : i<j) : f i≠f j := by
    have lij : i.val<j.val := lt
    intro e
    by_cases near : i.val+1=j.val
    · exact G.loopless _ (e ▸ (h i j lt).mpr near)
    by_cases gap : i.val+2=j.val
    · by_cases iz : i.val=0
      · let k : Fin 9 := ⟨j.val+1,by omega⟩
        have jk : j < k := by change j.val < j.val+1; omega
        have ik : i < k := lt.trans jk
        have adj : G.Adj (f i) (f k) := e.symm ▸ (h j k jk).mpr rfl
        have eq := (h i k ik).mp adj
        change i.val+1=j.val+1 at eq
        omega
      · let k : Fin 9 := ⟨i.val-1,by omega⟩
        have ki : k < i := by change i.val-1 < i.val; omega
        have kj : k < j := ki.trans lt
        have adj : G.Adj (f k) (f j) := e ▸ (h k i ki).mpr (by change (i.val-1)+1=i.val; omega)
        have eq := (h k j kj).mp adj
        change (i.val-1)+1=j.val at eq
        omega
    · let k : Fin 9 := ⟨i.val+1,by omega⟩
      have ik : i < k := by change i.val < i.val+1; omega
      have kj : k < j := by change i.val+1 < j.val; omega
      have adj : G.Adj (f k) (f j) := e ▸ ((h i k ik).mpr rfl).symm
      have eq := (h k j kj).mp adj
      change i.val+1+1=j.val at eq
      omega
  intro i j e
  rcases lt_trichotomy i j with a|a|a
  · exact (noEq i j a e).elim
  · exact a
  · exact (noEq j i a e.symm).elim

/-- Three pure high fans in the same isolated color cannot coexist around
an adjacent pair of other palette ports in an induced-P9-free graph. -/
theorem one_edge_same_color_at_most_two_fans
    (h4 : FourCycleFree G) {D : Set V} {p : Fin 4→V} {A : Finset V} {f : V→Fin 4→V}
    (H : PortFanFamily G D p A f)
    (edge12 : G.Adj (p 1) (p 2))
    (iso0 : ∀ i,¬G.Adj (p 0) (p i)) (iso3 : ∀ i,¬G.Adj (p 3) (p i))
    (noP9 : NoPath G 9) : A.card≤2 := by
  classical
  have aw (r : V) (rm : r∈A) (i : Fin 4) : G.Adj (f r i) (p i) :=
    (H.onlyPort r rm i _ (H.portsIn i)).mpr rfl
  have leaf (r : V) (rm : r∈A) (i : Fin 4) (i0 : i≠0) : G.Adj (f r 0) (f r i) :=
    (H.star r rm 0 i (Fin.pos_iff_ne_zero.mpr i0)).mpr rfl
  have leavesInject (i : Fin 4) : Set.InjOn (fun r=>f r i) (A:Set V) := by
    intro x xm y ym eq
    by_cases z : i=0
    · subst i
      exact (H.center x xm).symm.trans (eq.trans (H.center y ym))
    have centerNe : p 0≠f x i := fun e=>H.outer x xm i (e ▸ H.portsIn 0)
    change f x i=f y i at eq
    have e := h4 (p 0) (f x i) (f x 0) (f y 0) centerNe (aw x xm 0).symm
      (leaf x xm i z).symm (aw y ym 0).symm (eq.symm ▸ (leaf y ym i z).symm)
    exact (H.center x xm).symm.trans (e.trans (H.center y ym))
  have forbid (x y : V) (xm : x∈A) (ym : y∈A) (xy : x≠y) (i : Fin 4) (i0 : i≠0) :
      ¬G.Adj (f x 0) (f y i) := by
    intro e
    have ne : f x 0≠p i := fun eq=>H.outer x xm 0 (eq.symm ▸ H.portsIn i)
    have eq := h4 (f x 0) (p i) (f x i) (f y i) ne (leaf x xm i i0) (aw x xm i).symm e (aw y ym i).symm
    exact xy (leavesInject i xm ym eq)
  by_cases small : A.card≤2
  · exact small
  exfalso
  obtain ⟨q,qm⟩ := Finset.card_pos.mp (show 0<A.card by omega)
  have aq := Finset.card_erase_add_one qm
  obtain ⟨r,rEm⟩ := Finset.card_pos.mp (show 0<(A.erase q).card by omega)
  obtain ⟨rq,rm⟩ := Finset.mem_erase.mp rEm
  have ar := Finset.card_erase_add_one rEm
  obtain ⟨s,sEm⟩ := Finset.card_pos.mp (show 0<((A.erase q).erase r).card by omega)
  obtain ⟨sr,sQ⟩ := Finset.mem_erase.mp sEm
  obtain ⟨sq,sm⟩ := Finset.mem_erase.mp sQ
  have force (r s : V) (rm : r∈A) (sm : s∈A) (qr : q≠r) (qs : q≠s) (rs : r≠s)
      (j k : Fin 4) (j0 : j≠0) (j3 : j≠3) (k0 : k≠0) (k3 : k≠3) (jk : j≠k)
      (edge : G.Adj (p j) (p k)) (noqr : ¬G.Adj (f q 0) (f r 0)) :
      G.Adj (f q 3) (f r j) ∨ G.Adj (f q 3) (f s k) := by
    by_cases h1 : G.Adj (f q 3) (f r j)
    · exact Or.inl h1
    by_cases h2 : G.Adj (f q 3) (f s k)
    · exact Or.inr h2
    exfalso
    have bcs : ¬G.Adj (f r j) (f s k) := by
      intro h
      have e := h4 (p j) (f s k) (p k) (f r j)
        (fun e=>H.outer s sm k (e ▸ H.portsIn j))
        edge (aw s sm k) (aw r rm j).symm h.symm
      exact H.outer r rm j (e ▸ H.portsIn k)
    have pn (u : V) (um : u∈A) (i j : Fin 4) (ij : i≠j) : ¬G.Adj (f u i) (p j) :=
      fun e=>ij (H.distinctPorts ((H.onlyPort u um i _ (H.portsIn j)).mp e)).symm
    apply noP9
    let path : Fin 9→V := ![p 3,f q 3,f q 0,p 0,f r 0,f r j,p j,p k,f s k]
    refine ⟨path,one_edge_triple_path9_of_ordered_adjacency path ?_⟩
    intro i l
    fin_cases i <;> fin_cases l <;> intro ord <;> try (exfalso; exact (by decide : ¬ _ < _) ord)
    · exact ⟨fun _=>by decide,fun _=>(aw q qm 3).symm⟩
    · exact ⟨fun e=>(fun e=>pn q qm 0 3 (by decide) e.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(2:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(iso3 _ : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(3:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>pn r rm 0 3 (by decide) e.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(4:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>pn r rm j 3 (j3) e.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(5:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(iso3 _ : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(iso3 _ : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>pn s sm k 3 (k3) e.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
    · exact ⟨fun _=>by decide,fun _=>(leaf q qm 3 (by decide)).symm⟩
    · exact ⟨fun e=>(pn q qm 3 0 (by decide) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(3:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>forbid r q rm qm qr.symm 3 (by decide) e.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(4:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(h1 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(5:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(pn q qm 3 j (j3.symm) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(pn q qm 3 k (k3.symm) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(h2 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
    · exact ⟨fun _=>by decide,fun _=>aw q qm 0⟩
    · exact ⟨fun e=>(noqr : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(4:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(forbid q r qm rm qr j (j0) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(5:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(pn q qm 0 j (j0.symm) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(pn q qm 0 k (k0.symm) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(forbid q s qm sm qs k (k0) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
    · exact ⟨fun _=>by decide,fun _=>(aw r rm 0).symm⟩
    · exact ⟨fun e=>(fun e=>pn r rm j 0 (j0) e.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((3:Fin 9).val+1=(5:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(iso0 _ : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((3:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(iso0 _ : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((3:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>pn s sm k 0 (k0) e.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((3:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
    · exact ⟨fun _=>by decide,fun _=>leaf r rm j (j0)⟩
    · exact ⟨fun e=>(pn r rm 0 j (j0.symm) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((4:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(pn r rm 0 k (k0.symm) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((4:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(forbid r s rm sm rs k (k0) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((4:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
    · exact ⟨fun _=>by decide,fun _=>aw r rm j⟩
    · exact ⟨fun e=>(pn r rm j k (jk) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((5:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(bcs : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((5:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
    · exact ⟨fun _=>by decide,fun _=>edge⟩
    · exact ⟨fun e=>(fun e=>pn s sm k j (jk.symm) e.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((6:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
    · exact ⟨fun _=>by decide,fun _=>(aw s sm k).symm⟩
  have atMostOne : ¬(G.Adj (f q 0) (f r 0) ∧ G.Adj (f q 0) (f s 0)) := by
    rintro ⟨qr,qs⟩
    have eq := h4 (f q 0) (p 0) (f r 0) (f s 0)
      (fun e=>H.outer q qm 0 (e.symm ▸ H.portsIn 0)) qr (aw r rm 0).symm qs (aw s sm 0).symm
    exact sr.symm (leavesInject 0 rm sm eq)
  have both : (G.Adj (f q 3) (f r 1) ∨ G.Adj (f q 3) (f s 2)) ∧
      (G.Adj (f q 3) (f r 2) ∨ G.Adj (f q 3) (f s 1)) := by
    by_cases qr : G.Adj (f q 0) (f r 0)
    · have qs : ¬G.Adj (f q 0) (f s 0) := fun e=>atMostOne ⟨qr,e⟩
      exact ⟨(force s r sm rm sq.symm rq.symm sr 2 1 (by decide) (by decide) (by decide)
        (by decide) (by decide) edge12.symm qs).symm,
        (force s r sm rm sq.symm rq.symm sr 1 2 (by decide) (by decide) (by decide)
          (by decide) (by decide) edge12 qs).symm⟩
    exact ⟨force r s rm sm rq.symm sq.symm sr.symm 1 2 (by decide) (by decide) (by decide)
      (by decide) (by decide) edge12 qr,force r s rm sm rq.symm sq.symm sr.symm 2 1
      (by decide) (by decide) (by decide) (by decide) (by decide) edge12.symm qr⟩
  obtain ⟨one,two⟩ := both
  rcases one with a|a <;> rcases two with b|b
  · have ne : f q 3≠f r 0 := fun e=>(by decide : (0:Fin 4)≠3) (H.distinctPorts
      ((H.onlyPort q qm 3 _ (H.portsIn 0)).mp (e.symm ▸ aw r rm 0)))
    have e := h4 (f q 3) (f r 0) (f r 1) (f r 2) ne a (leaf r rm 1 (by decide))
      b (leaf r rm 2 (by decide))
    exact (by decide : (1:Fin 4)≠2) (H.distinctPorts
      ((H.onlyPort r rm 2 _ (H.portsIn 1)).mp (e ▸ aw r rm 1)))
  · have ne : f q 3≠p 1 := fun e=>H.outer q qm 3 (e.symm ▸ H.portsIn 1)
    have e := h4 (f q 3) (p 1) (f r 1) (f s 1) ne a (aw r rm 1).symm b (aw s sm 1).symm
    exact sr.symm (leavesInject 1 rm sm e)
  · have ne : f q 3≠p 2 := fun e=>H.outer q qm 3 (e.symm ▸ H.portsIn 2)
    have e := h4 (f q 3) (p 2) (f s 2) (f r 2) ne a (aw s sm 2).symm b (aw r rm 2).symm
    exact sr (leavesInject 2 sm rm e)
  · have ne : f q 3≠f s 0 := fun e=>(by decide : (0:Fin 4)≠3) (H.distinctPorts
      ((H.onlyPort q qm 3 _ (H.portsIn 0)).mp (e.symm ▸ aw s sm 0)))
    have e := h4 (f q 3) (f s 0) (f s 2) (f s 1) ne a (leaf s sm 2 (by decide))
      b (leaf s sm 1 (by decide))
    exact (by decide : (2:Fin 4)≠1) (H.distinctPorts
      ((H.onlyPort s sm 1 _ (H.portsIn 2)).mp (e ▸ aw s sm 2)))

#print axioms one_edge_same_color_at_most_two_fans
end Graffiti133P5CliqueArms
