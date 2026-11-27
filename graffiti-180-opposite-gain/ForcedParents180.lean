import ParentGain180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Transversals HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Keep the entire star of a. Outside the star, impose parent t on
a specified set F. A horizontal neighbor of a may also acquire children
one layer closer to the root. All other parent choices use shortest paths. -/
theorem star_parents (G : SimpleGraph V) (gc : G.Connected) (r a t : V) (ar : a≠r)
    (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A)
    (F : Finset V) (sources : ∀ x∈F,x≠r ∧ ¬G.Adj a x ∧ x≠a ∧ G.Adj x t)
    (levels : ∀ x∈F,G.dist t r≤G.dist x r ∨
      (G.Adj a t ∧ G.dist t r=G.dist a r ∧ G.dist t r≤G.dist x r+1))
    (safe : ∀ x∈F,x∈A∩parity G r p → t∉A∪parity G r p) :
    ∃ (T : SimpleGraph V) (q : V→V) (k : V→ℕ),T≤G ∧ T.IsTree ∧ (∀ x≠r,k (q x)<k x) ∧
      (∀ x≠r,T.Adj x (q x)) ∧ T.degree a=G.degree a ∧ (∀ x∈F,q x=t) ∧
      (∀ x∈A∩parity G r p,x≠r → q x∉A∪parity G r p) := by
  classical
  let d (x : V) := G.dist x r
  let par (x : V) := if h : x=r then r else (Graffiti169.exists_predecessor G gc r x h).choose
  have parent (x : V) (xr : x≠r) : G.Adj x (par x) ∧ d x=d (par x)+1 := by
    simpa [d,par,xr] using (Graffiti169.exists_predecessor G gc r x xr).choose_spec
  let b := par a
  have ab := parent a ar
  change G.Adj a b ∧ d a=d b+1 at ab
  let red (x : V) := x=t ∧ G.Adj a t ∧ d t=d a
  let tag (x : V) := if x=a then 0 else if x=b then 4 else if red x then 1 else if x∈F then 12 else 10
  let k (x : V) := 9*d x+tag x
  let q (x : V) := if G.Adj a x ∧ x≠b then a else if x∈F then t else par x
  have notTarget : t∉F := fun h => G.loopless _ (sources t h).2.2.2
  have bound (x : V) : tag x≤12 := by simp only [tag];split_ifs <;> decide
  have tagA : tag a=0 := by simp [tag]
  have tagB : tag b=4 := by simp [tag,ab.1.ne.symm]
  have tagF (x : V) (xm : x∈F) : tag x=12 := by
    obtain ⟨_,outside,xa,_⟩ := sources x xm
    have xb : x≠b := fun eq => outside (eq ▸ ab.1)
    have nr : ¬red x := fun h => outside (h.1 ▸ h.2.1)
    simp [tag,xa,xb,nr,xm]
  have normal (x : V) (xa : x≠a) (xb : x≠b) (no : ¬red x) : 10≤tag x := by
    simp only [tag,if_neg xa,if_neg xb,if_neg no];split_ifs <;> decide
  have unit {x : V} (edge : G.Adj a x) : d a≤d x+1 := by
    have h := gc.dist_triangle (u:=a) (v:=x) (w:=r)
    rw [dist_eq_one_iff_adj.mpr edge] at h
    change G.dist a r≤G.dist x r+1;omega
  have qt (x : V) (xm : x∈F) : q x=t := by simp [q,(sources x xm).2.1,xm]
  have qa : q a=b := by
    have nf : a∉F := fun m => (sources a m).2.2.1 rfl
    simp [q,nf,b]
  have step (x : V) (xr : x≠r) : G.Adj x (q x) ∧ k (q x)<k x := by
    by_cases spoke : G.Adj a x ∧ x≠b
    · rw [show q x=a from if_pos spoke]
      refine ⟨spoke.1.symm,?_⟩
      change 9*d a+tag a<9*d x+tag x
      have near := unit spoke.1
      by_cases redX : red x
      · have eq : d x=d a := redX.1 ▸ redX.2.2
        have tx : tag x=1 := by simp [tag,spoke.1.ne.symm,spoke.2,redX]
        omega
      · have large := normal x spoke.1.ne.symm spoke.2 redX
        omega
    · by_cases xm : x∈F
      · rw [qt x xm]
        refine ⟨(sources x xm).2.2.2,?_⟩
        change 9*d t+tag t<9*d x+tag x
        have tx := tagF x xm
        rcases levels x xm with less|⟨at',eq,less⟩
        · have tt : tag t<12 := by simp only [tag,if_neg notTarget];split_ifs <;> decide
          change d t≤d x at less;omega
        · have tb : t≠b := by intro e;change d t=d a at eq;rw [e] at eq;omega
          have rd : red t := ⟨rfl,at',eq⟩
          have tt : tag t=1 := by simp [tag,at'.ne.symm,tb,rd]
          change d t≤d x+1 at less;omega
      · rw [show q x=par x from by simp [q,spoke,xm]]
        obtain ⟨ed,h⟩ := parent x xr
        refine ⟨ed,?_⟩
        change 9*d (par x)+tag (par x)<9*d x+tag x
        have upper := bound (par x)
        by_cases xa : x=a
        · subst x;change 9*d b+tag b<9*d a+tag a;omega
        by_cases xb : x=b
        · subst x;omega
        have nr : ¬red x := fun m => spoke ⟨m.1 ▸ m.2.1,xb⟩
        have lower := normal x xa xb nr
        omega
  obtain ⟨T,tree,take⟩ := virtual_tree r q k (fun x xr => (step x xr).2)
  have all := parent_image T tree r q k (fun x xr => (step x xr).2) take
  have sub : T≤G := by
    intro x y ed
    have mem : s(x,y)∈T.edgeFinset := mem_edgeFinset.mpr ed
    rw [←all] at mem
    obtain ⟨z,zm,eq⟩ := mem_image.mp mem
    have e := (step z (mem_erase.mp zm).1).1
    rcases Sym2.eq_iff.mp eq with ⟨u,v⟩|⟨u,v⟩
    · exact u ▸ v ▸ e
    · exact u ▸ v ▸ e.symm
  have full (y : V) (ed : G.Adj a y) : T.Adj a y := by
    by_cases yb : y=b
    · rw [yb,←qa];exact take a ar
    · have yr : y≠r := by
        intro eq
        have one : d a=1 := dist_eq_one_iff_adj.mpr (eq ▸ ed)
        have br : b=r := gc.dist_eq_zero_iff.mp (show d b=0 by omega)
        exact yb (eq.trans br.symm)
      exact (show T.Adj y a by simpa [q,ed,yb] using take y yr).symm
  have deg : T.neighborFinset a=G.neighborFinset a := by ext y;simp only [mem_neighborFinset];exact ⟨fun e => sub e,full y⟩
  refine ⟨T,q,k,sub,tree,fun x xr => (step x xr).2,take,
    by simpa only [card_neighborFinset_eq_degree] using congrArg card deg,qt,?_⟩
  intro x xm xr
  by_cases xf : x∈F
  · rw [qt x xf];exact safe x xf xm
  have xa := (mem_inter.mp xm).1
  have xp := (mem_inter.mp xm).2
  have non : ¬G.Adj a x := fun ed => ai a am x xa ed.ne ed
  rw [show q x=par x from by simp [q,non,xf]]
  obtain ⟨ed,dt⟩ := parent x xr
  have np : par x∉parity G r p := by
    have e := (mem_parity G r x p).mp xp
    intro bad
    have f := (mem_parity G r _ p).mp bad
    change G.dist x r=G.dist (par x) r+1 at dt;omega
  exact fun m => (mem_union.mp m).elim (fun ma => ai x xa _ ma ed.ne ed) np

#print axioms star_parents
end Minimal180.OppositeGain
