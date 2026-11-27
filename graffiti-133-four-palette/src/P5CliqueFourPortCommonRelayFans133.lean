import P5CliqueOnePortAmbientBudget133
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

private theorem path9_of_ordered_adjacency (f : Fin 9→V)
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

structure PortFanFamily (G : SimpleGraph V) (D : Set V) (p : Fin 4→V)
    (A : Finset V) (f : V→Fin 4→V) : Prop where
  portsIn : ∀ i,p i∈D
  distinctPorts : Function.Injective p
  outer : ∀ q∈A,∀ i,f q i∉D
  center : ∀ q∈A,f q 0=q
  onlyPort : ∀ q∈A,∀ i x, x∈D → (G.Adj (f q i) x ↔x=p i)
  star : ∀ q∈A,∀ i j, i<j → (G.Adj (f q i) (f q j) ↔ i=0)

theorem six_same_port_fans_or_induced_P9
    (h4 : FourCycleFree G) {D : Set V} {p : Fin 4→V} {A : Finset V} {f : V→Fin 4→V}
    (H : PortFanFamily G D p A f) (t : V) (td : t∈D) (tn : ∀ i,t≠p i)
    (pt : G.Adj (p 2) t) (tp : G.Adj t (p 3)) (not23 : ¬G.Adj (p 2) (p 3))
    (noP9 : NoPath G 9) : A.card≤6 := by
  classical
  by_cases empty : A=∅
  · simp [empty]
  obtain ⟨q,qM⟩ := Finset.nonempty_iff_ne_empty.mpr empty
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
  have cross (r : V) (rm : r∈A) (qr : q≠r) :
      G.Adj (f q 0) (f r 0) ∨ G.Adj (f q 1) (f r 1) ∨ G.Adj (f q 1) (f r 3) ∨
        G.Adj (f q 2) (f r 1) ∨ G.Adj (f q 2) (f r 3) := by
    by_cases h1 : G.Adj (f q 0) (f r 0)
    · exact Or.inl h1
    by_cases h2 : G.Adj (f q 1) (f r 1)
    · exact Or.inr (Or.inl h2)
    by_cases h3 : G.Adj (f q 1) (f r 3)
    · exact Or.inr (Or.inr (Or.inl h3))
    by_cases h4' : G.Adj (f q 2) (f r 1)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4')))
    by_cases h5 : G.Adj (f q 2) (f r 3)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
    exfalso
    have h := And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4' h5)))
    apply noP9
    let path : Fin 9→V := ![f q 1,f q 0,f q 2,p 2,t,p 3,f r 3,f r 0,f r 1]
    refine ⟨path,path9_of_ordered_adjacency path ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> intro ord <;> try (exfalso; exact (by decide : ¬ _ < _) ord)
    · exact ⟨fun _=>by decide,fun _=>(leaf q qM 1 (by decide)).symm⟩
    · exact ⟨fun e=>(fun e=> (by decide : (1:Fin 4)≠0) ((H.star q qM 1 2 (by decide)).mp e) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(2:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>(by decide : (2:Fin 4)≠1) (H.distinctPorts ((H.onlyPort q qM 1 (p 2) (H.portsIn 2)).mp e)) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(3:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>tn 1 ((H.onlyPort q qM 1 t td).mp e) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(4:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>(by decide : (3:Fin 4)≠1) (H.distinctPorts ((H.onlyPort q qM 1 (p 3) (H.portsIn 3)).mp e)) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(5:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(h.2.2.1 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=> forbid r q rm qM qr.symm 1 (by decide) e.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(h.2.1 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((0:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
    · exact ⟨fun _=>by decide,fun _=>leaf q qM 2 (by decide)⟩
    · exact ⟨fun e=>(fun e=>(by decide : (2:Fin 4)≠0) (H.distinctPorts ((H.onlyPort q qM 0 (p 2) (H.portsIn 2)).mp e)) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(3:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>tn 0 ((H.onlyPort q qM 0 t td).mp e) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(4:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>(by decide : (3:Fin 4)≠0) (H.distinctPorts ((H.onlyPort q qM 0 (p 3) (H.portsIn 3)).mp e)) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(5:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(forbid q r qM rm qr 3 (by decide) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(h.1 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(forbid q r qM rm qr 1 (by decide) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((1:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
    · exact ⟨fun _=>by decide,fun _=>aw q qM 2⟩
    · exact ⟨fun e=>(fun e=>tn 2 ((H.onlyPort q qM 2 t td).mp e) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(4:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>(by decide : (3:Fin 4)≠2) (H.distinctPorts ((H.onlyPort q qM 2 (p 3) (H.portsIn 3)).mp e)) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(5:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(h.2.2.2.2 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=> forbid r q rm qM qr.symm 2 (by decide) e.symm : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(h.2.2.2.1 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((2:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
    · exact ⟨fun _=>by decide,fun _=>pt⟩
    · exact ⟨fun e=>(not23 : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((3:Fin 9).val+1=(5:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>(by decide : (2:Fin 4)≠3) (H.distinctPorts ((H.onlyPort r rm 3 (p 2) (H.portsIn 2)).mp e.symm)) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((3:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>(by decide : (2:Fin 4)≠0) (H.distinctPorts ((H.onlyPort r rm 0 (p 2) (H.portsIn 2)).mp e.symm)) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((3:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>(by decide : (2:Fin 4)≠1) (H.distinctPorts ((H.onlyPort r rm 1 (p 2) (H.portsIn 2)).mp e.symm)) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((3:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
    · exact ⟨fun _=>by decide,fun _=>tp⟩
    · exact ⟨fun e=>(fun e=>tn 3 ((H.onlyPort r rm 3 t td).mp e.symm) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((4:Fin 9).val+1=(6:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>tn 0 ((H.onlyPort r rm 0 t td).mp e.symm) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((4:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>tn 1 ((H.onlyPort r rm 1 t td).mp e.symm) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((4:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
    · exact ⟨fun _=>by decide,fun _=>(aw r rm 3).symm⟩
    · exact ⟨fun e=>(fun e=>(by decide : (3:Fin 4)≠0) (H.distinctPorts ((H.onlyPort r rm 0 (p 3) (H.portsIn 3)).mp e.symm)) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((5:Fin 9).val+1=(7:Fin 9).val)) e).elim⟩
    · exact ⟨fun e=>(fun e=>(by decide : (3:Fin 4)≠1) (H.distinctPorts ((H.onlyPort r rm 1 (p 3) (H.portsIn 3)).mp e.symm)) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((5:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
    · exact ⟨fun _=>by decide,fun _=>(leaf r rm 3 (by decide)).symm⟩
    · exact ⟨fun e=>(fun e=> (by decide : (1:Fin 4)≠0) ((H.star r rm 1 3 (by decide)).mp e.symm) : ¬_ ) e |>.elim,fun e=>((by decide : ¬ ((6:Fin 9).val+1=(8:Fin 9).val)) e).elim⟩
    · exact ⟨fun _=>by decide,fun _=>leaf r rm 1 (by decide)⟩
  let T : Finset (Fin 4×Fin 4) := {(0,0),(1,1),(1,3),(2,1),(2,3)}
  let X (e : Fin 4×Fin 4) := A.filter (fun r=>G.Adj (f q e.1) (f r e.2))
  have one (e : Fin 4×Fin 4) : (X e).card≤1 := by
    apply Finset.card_le_one.mpr
    intro r rm s sm
    obtain ⟨rA,re⟩ := Finset.mem_filter.mp rm
    obtain ⟨sA,se⟩ := Finset.mem_filter.mp sm
    apply leavesInject e.2 rA sA
    exact h4 (f q e.1) (p e.2) (f r e.2) (f s e.2)
      (fun eq=>H.outer q qM e.1 (eq.symm ▸ H.portsIn e.2)) re (aw r rA e.2).symm se (aw s sA e.2).symm
  have cover : A.erase q⊆T.biUnion X := by
    intro r rm
    obtain ⟨qr,rA⟩ := Finset.mem_erase.mp rm
    rcases cross r rA qr.symm with e|e|e|e|e
    · exact Finset.mem_biUnion.mpr ⟨(0,0),by decide,Finset.mem_filter.mpr ⟨rA,e⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨(1,1),by decide,Finset.mem_filter.mpr ⟨rA,e⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨(1,3),by decide,Finset.mem_filter.mpr ⟨rA,e⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨(2,1),by decide,Finset.mem_filter.mpr ⟨rA,e⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨(2,3),by decide,Finset.mem_filter.mpr ⟨rA,e⟩⟩
  have bound : (A.erase q).card≤5 := by
    calc
      _ ≤ (T.biUnion X).card := Finset.card_le_card cover
      _ ≤ ∑ e∈T,(X e).card := Finset.card_biUnion_le
      _ ≤ ∑ _e∈T,1 := Finset.sum_le_sum (fun e _=>one e)
      _ = 5 := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one]; decide
  have eq := Finset.card_erase_add_one qM
  omega

#print axioms six_same_port_fans_or_induced_P9
end Graffiti133P5CliqueArms
