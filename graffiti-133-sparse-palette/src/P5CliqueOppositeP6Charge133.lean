import CambyDomBase133
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4500000
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

private theorem no_induced_P6_with_ends_and_extension
    (h9 : NoPath G 9) (a : Fin 6→V) (p : InducedPath G a) (r s q : V)
    (rn : ∀ i,r≠a i) (sn : ∀ i,s≠a i) (qn : ∀ i,q≠a i)
    (rs : r≠s) (rq : r≠q) (sq : G.Adj s q)
    (ra : ∀ i,G.Adj r (a i)↔i=0)
    (sa : ∀ i,G.Adj s (a i)↔i=5)
    (qa : ∀ i,¬G.Adj q (a i))
    (noRS : ¬G.Adj r s) (noRQ : ¬G.Adj r q) : False := by
  let f : Fin 9→V := ![r,a 0,a 1,a 2,a 3,a 4,a 5,s,q]
  have fi : Function.Injective f := by
    intro i j e
    fin_cases i <;> fin_cases j <;> first | rfl |
      (exfalso
       simp only [f,Matrix.cons_val_zero,Matrix.cons_val_succ] at e
       first | exact rn _ e | exact rn _ e.symm | exact sn _ e | exact sn _ e.symm |
          exact qn _ e | exact qn _ e.symm | exact rs e | exact rs e.symm | exact rq e | exact rq e.symm |
          exact sq.ne e | exact sq.ne e.symm | exact (by decide : ¬ _) (p.1 e))
  have fe (i j : Fin 9) (ij : i<j) : G.Adj (f i) (f j) ↔ i.val+1=j.val := by
    fin_cases i <;> fin_cases j
    · exact False.elim ((by decide : ¬ ((0 : Fin 9) < 0)) ij)
    · simp [f,ra]
    · simp [f,ra]
    · simp [f,ra]
    · simp [f,ra]
    · simp [f,ra]
    · simp [f,ra]
    · simp [f,noRS,noRQ,sq]
    · simp [f,noRS,noRQ,sq]
    · exact False.elim ((by decide : ¬ ((1 : Fin 9) < 0)) ij)
    · exact False.elim ((by decide : ¬ ((1 : Fin 9) < 1)) ij)
    · change G.Adj (a 0) (a 1) ↔ (2 : Nat)=2
      exact (p.2 0 1 (by decide)).trans (by decide : ((0 : Fin 6).val+1=(1 : Fin 6).val)↔(2 : Nat)=2)
    · change G.Adj (a 0) (a 2) ↔ (2 : Nat)=3
      exact (p.2 0 2 (by decide)).trans (by decide : ((0 : Fin 6).val+1=(2 : Fin 6).val)↔(2 : Nat)=3)
    · change G.Adj (a 0) (a 3) ↔ (2 : Nat)=4
      exact (p.2 0 3 (by decide)).trans (by decide : ((0 : Fin 6).val+1=(3 : Fin 6).val)↔(2 : Nat)=4)
    · change G.Adj (a 0) (a 4) ↔ (2 : Nat)=5
      exact (p.2 0 4 (by decide)).trans (by decide : ((0 : Fin 6).val+1=(4 : Fin 6).val)↔(2 : Nat)=5)
    · change G.Adj (a 0) (a 5) ↔ (2 : Nat)=6
      exact (p.2 0 5 (by decide)).trans (by decide : ((0 : Fin 6).val+1=(5 : Fin 6).val)↔(2 : Nat)=6)
    · change G.Adj (a 0) s ↔ (2 : Nat)=7
      exact (SimpleGraph.adj_comm G _ _).trans ((sa 0).trans (by decide))
    · change G.Adj (a 0) q ↔ (2 : Nat)=8
      have e : ¬G.Adj (a 0) q := fun h=>qa 0 h.symm
      simp [e]
    · exact False.elim ((by decide : ¬ ((2 : Fin 9) < 0)) ij)
    · exact False.elim ((by decide : ¬ ((2 : Fin 9) < 1)) ij)
    · exact False.elim ((by decide : ¬ ((2 : Fin 9) < 2)) ij)
    · change G.Adj (a 1) (a 2) ↔ (3 : Nat)=3
      exact (p.2 1 2 (by decide)).trans (by decide : ((1 : Fin 6).val+1=(2 : Fin 6).val)↔(3 : Nat)=3)
    · change G.Adj (a 1) (a 3) ↔ (3 : Nat)=4
      exact (p.2 1 3 (by decide)).trans (by decide : ((1 : Fin 6).val+1=(3 : Fin 6).val)↔(3 : Nat)=4)
    · change G.Adj (a 1) (a 4) ↔ (3 : Nat)=5
      exact (p.2 1 4 (by decide)).trans (by decide : ((1 : Fin 6).val+1=(4 : Fin 6).val)↔(3 : Nat)=5)
    · change G.Adj (a 1) (a 5) ↔ (3 : Nat)=6
      exact (p.2 1 5 (by decide)).trans (by decide : ((1 : Fin 6).val+1=(5 : Fin 6).val)↔(3 : Nat)=6)
    · change G.Adj (a 1) s ↔ (3 : Nat)=7
      exact (SimpleGraph.adj_comm G _ _).trans ((sa 1).trans (by decide))
    · change G.Adj (a 1) q ↔ (3 : Nat)=8
      have e : ¬G.Adj (a 1) q := fun h=>qa 1 h.symm
      simp [e]
    · exact False.elim ((by decide : ¬ ((3 : Fin 9) < 0)) ij)
    · exact False.elim ((by decide : ¬ ((3 : Fin 9) < 1)) ij)
    · exact False.elim ((by decide : ¬ ((3 : Fin 9) < 2)) ij)
    · exact False.elim ((by decide : ¬ ((3 : Fin 9) < 3)) ij)
    · change G.Adj (a 2) (a 3) ↔ (4 : Nat)=4
      exact (p.2 2 3 (by decide)).trans (by decide : ((2 : Fin 6).val+1=(3 : Fin 6).val)↔(4 : Nat)=4)
    · change G.Adj (a 2) (a 4) ↔ (4 : Nat)=5
      exact (p.2 2 4 (by decide)).trans (by decide : ((2 : Fin 6).val+1=(4 : Fin 6).val)↔(4 : Nat)=5)
    · change G.Adj (a 2) (a 5) ↔ (4 : Nat)=6
      exact (p.2 2 5 (by decide)).trans (by decide : ((2 : Fin 6).val+1=(5 : Fin 6).val)↔(4 : Nat)=6)
    · change G.Adj (a 2) s ↔ (4 : Nat)=7
      exact (SimpleGraph.adj_comm G _ _).trans ((sa 2).trans (by decide))
    · change G.Adj (a 2) q ↔ (4 : Nat)=8
      have e : ¬G.Adj (a 2) q := fun h=>qa 2 h.symm
      simp [e]
    · exact False.elim ((by decide : ¬ ((4 : Fin 9) < 0)) ij)
    · exact False.elim ((by decide : ¬ ((4 : Fin 9) < 1)) ij)
    · exact False.elim ((by decide : ¬ ((4 : Fin 9) < 2)) ij)
    · exact False.elim ((by decide : ¬ ((4 : Fin 9) < 3)) ij)
    · exact False.elim ((by decide : ¬ ((4 : Fin 9) < 4)) ij)
    · change G.Adj (a 3) (a 4) ↔ (5 : Nat)=5
      exact (p.2 3 4 (by decide)).trans (by decide : ((3 : Fin 6).val+1=(4 : Fin 6).val)↔(5 : Nat)=5)
    · change G.Adj (a 3) (a 5) ↔ (5 : Nat)=6
      exact (p.2 3 5 (by decide)).trans (by decide : ((3 : Fin 6).val+1=(5 : Fin 6).val)↔(5 : Nat)=6)
    · change G.Adj (a 3) s ↔ (5 : Nat)=7
      exact (SimpleGraph.adj_comm G _ _).trans ((sa 3).trans (by decide))
    · change G.Adj (a 3) q ↔ (5 : Nat)=8
      have e : ¬G.Adj (a 3) q := fun h=>qa 3 h.symm
      simp [e]
    · exact False.elim ((by decide : ¬ ((5 : Fin 9) < 0)) ij)
    · exact False.elim ((by decide : ¬ ((5 : Fin 9) < 1)) ij)
    · exact False.elim ((by decide : ¬ ((5 : Fin 9) < 2)) ij)
    · exact False.elim ((by decide : ¬ ((5 : Fin 9) < 3)) ij)
    · exact False.elim ((by decide : ¬ ((5 : Fin 9) < 4)) ij)
    · exact False.elim ((by decide : ¬ ((5 : Fin 9) < 5)) ij)
    · change G.Adj (a 4) (a 5) ↔ (6 : Nat)=6
      exact (p.2 4 5 (by decide)).trans (by decide : ((4 : Fin 6).val+1=(5 : Fin 6).val)↔(6 : Nat)=6)
    · change G.Adj (a 4) s ↔ (6 : Nat)=7
      exact (SimpleGraph.adj_comm G _ _).trans ((sa 4).trans (by decide))
    · change G.Adj (a 4) q ↔ (6 : Nat)=8
      have e : ¬G.Adj (a 4) q := fun h=>qa 4 h.symm
      simp [e]
    · exact False.elim ((by decide : ¬ ((6 : Fin 9) < 0)) ij)
    · exact False.elim ((by decide : ¬ ((6 : Fin 9) < 1)) ij)
    · exact False.elim ((by decide : ¬ ((6 : Fin 9) < 2)) ij)
    · exact False.elim ((by decide : ¬ ((6 : Fin 9) < 3)) ij)
    · exact False.elim ((by decide : ¬ ((6 : Fin 9) < 4)) ij)
    · exact False.elim ((by decide : ¬ ((6 : Fin 9) < 5)) ij)
    · exact False.elim ((by decide : ¬ ((6 : Fin 9) < 6)) ij)
    · change G.Adj (a 5) s ↔ (7 : Nat)=7
      exact (SimpleGraph.adj_comm G _ _).trans ((sa 5).trans (by decide))
    · change G.Adj (a 5) q ↔ (7 : Nat)=8
      have e : ¬G.Adj (a 5) q := fun h=>qa 5 h.symm
      simp [e]
    · exact False.elim ((by decide : ¬ ((7 : Fin 9) < 0)) ij)
    · exact False.elim ((by decide : ¬ ((7 : Fin 9) < 1)) ij)
    · exact False.elim ((by decide : ¬ ((7 : Fin 9) < 2)) ij)
    · exact False.elim ((by decide : ¬ ((7 : Fin 9) < 3)) ij)
    · exact False.elim ((by decide : ¬ ((7 : Fin 9) < 4)) ij)
    · exact False.elim ((by decide : ¬ ((7 : Fin 9) < 5)) ij)
    · exact False.elim ((by decide : ¬ ((7 : Fin 9) < 6)) ij)
    · exact False.elim ((by decide : ¬ ((7 : Fin 9) < 7)) ij)
    · simp [f,noRS,noRQ,sq]
    · exact False.elim ((by decide : ¬ ((8 : Fin 9) < 0)) ij)
    · exact False.elim ((by decide : ¬ ((8 : Fin 9) < 1)) ij)
    · exact False.elim ((by decide : ¬ ((8 : Fin 9) < 2)) ij)
    · exact False.elim ((by decide : ¬ ((8 : Fin 9) < 3)) ij)
    · exact False.elim ((by decide : ¬ ((8 : Fin 9) < 4)) ij)
    · exact False.elim ((by decide : ¬ ((8 : Fin 9) < 5)) ij)
    · exact False.elim ((by decide : ¬ ((8 : Fin 9) < 6)) ij)
    · exact False.elim ((by decide : ¬ ((8 : Fin 9) < 7)) ij)
    · exact False.elim ((by decide : ¬ ((8 : Fin 9) < 8)) ij)
  exact h9 ⟨f,fi,fe⟩

theorem opposite_P6_port_client_cap_two
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (D R : Finset V) (a : Fin 6→V) (ap : InducedPath G a) (ad : ∀ i,a i∈D)
    (s q : V) (so : s∉D) (qo : q∉D) (sq : G.Adj s q)
    (sa : ∀ v∈D,G.Adj s v↔v=a 5)
    (label : V) (ql : ∀ v∈D,G.Adj q v↔v=label) (la : ∀ i,label≠a i)
    (ra : ∀ r∈R,r∉D ∧ ∀ v∈D,G.Adj r v↔v=a 0) :
    R.card≤2 := by
  classical
  have tags : a 0≠a 5 := fun e=>(by decide : (0:Fin 6)≠5) (ap.1 e)
  have qn : ∀ i,q≠a i := fun i e=>qo (e.symm ▸ ad i)
  have sn : ∀ i,s≠a i := fun i e=>so (e.symm ▸ ad i)
  have qa : ∀ i,¬G.Adj q (a i) := fun i e=>la i (((ql _ (ad i)).mp e).symm)
  have rnor (r : V) (rm : r∈R) : r≠s ∧ r≠q := by
    have e := ((ra r rm).2 _ (ad 0)).mpr rfl
    exact ⟨fun h=>tags ((sa _ (ad 0)).mp (h ▸ e)),fun h=>qa 0 (h ▸ e)⟩
  have cover (r : V) (rm : r∈R) : G.Adj q r ∨ G.Adj s r := by
    by_contra no
    push_neg at no
    obtain ⟨ro,route⟩ := ra r rm
    apply no_induced_P6_with_ends_and_extension h9 a ap r s q
    · exact fun i e=>ro (e.symm ▸ ad i)
    · exact sn
    · exact qn
    · exact (rnor r rm).1
    · exact (rnor r rm).2
    · exact sq
    · intro i
      exact (route _ (ad i)).trans ⟨fun e=>ap.1 e,fun e=>congrArg a e⟩
    · intro i
      exact (sa _ (ad i)).trans ⟨fun e=>ap.1 e,fun e=>congrArg a e⟩
    · exact qa
    · exact fun e=>no.2 e.symm
    · exact fun e=>no.1 e.symm
  have cap (x : V) (xo : x∉D) : (R.filter (G.Adj x)).card≤1 := by
    apply Finset.card_le_one.mpr
    intro r rx t tx
    obtain ⟨rR,xr⟩ := Finset.mem_filter.mp rx
    obtain ⟨tR,xt⟩ := Finset.mem_filter.mp tx
    exact h4 x (a 0) r t (fun e=>xo (e.symm ▸ ad _)) xr
      (((ra r rR).2 _ (ad 0)).mpr rfl).symm xt (((ra t tR).2 _ (ad 0)).mpr rfl).symm
  have sub : R⊆R.filter (G.Adj q)∪R.filter (G.Adj s) := by
    intro r rm
    rcases cover r rm with h|h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨rm,h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨rm,h⟩))
  have first := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have cq := cap q qo
  have cs := cap s so
  omega

#print axioms opposite_P6_port_client_cap_two
end Graffiti133P5CliqueArms
