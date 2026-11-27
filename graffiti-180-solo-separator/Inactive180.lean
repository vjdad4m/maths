import WingAllowance180
import TwoMixed180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem free_center (G : SimpleGraph V) (a b : V) (O : Finset V) (ab : a≠b) (na : ¬G.Adj a b)
    (empty : ∀ x∈O,¬G.Adj a x) (bi : TwoColor G (insert b O)) (t : Bool) : TerminalColor G a b O t := by
  classical
  obtain ⟨e,ok⟩ := (color_function ..).mp bi
  let f (x : V) := if x=a then true else if e x=e b then t else !t
  have nei (x : V) (xm : x∈insert b O) : ¬G.Adj a x := by
    rcases mem_insert.mp xm with eq|h
    · exact eq ▸ na
    · exact empty x h
  refine ⟨f,?_,by simp [f],by simp [f,ab.symm]⟩
  intro x xm y ym ed
  have inE (z : V) (zm : z∈({a,b}:Finset V)∪O) (no : z≠a) : z∈insert b O := by
    simp only [mem_union,mem_insert,mem_singleton] at zm ⊢
    tauto
  have xa : x≠a := by intro eq;subst x;exact nei y (inE y ym ed.ne.symm) ed
  have ya : y≠a := by intro eq;subst y;exact nei x (inE x xm xa) ed.symm
  have diff := ok x (inE x xm xa) y (inE y ym ya) ed
  cases i : e x <;> cases j : e y <;> cases k : e b <;> cases t <;> simp_all [f]

/-- Every closed union of remainder components avoiding the neighborhood
of the saturated tip accommodates either relative tip color without a
deletion, even if the unprotected tip has many neighbors there. -/
theorem inactive_free (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (rk : Fintype.card V≤bipartiteNum G+2) (r : V) (p : Bool) (A : Finset V) (ai : Indep G A)
    (a b : V) (ab : a≠b) (na : ¬G.Adj a b) (am : a∈A) (pm : a∈parity G r p)
    (sat : G.degree a=allowance G r p A+2) (O : Finset V) (sub : O⊆univ\({a,b}:Finset V))
    (cl : ClosedIn G (univ\{a,b}) O) (empty : ∀ x∈O,¬G.Adj a x) (t : Bool) :
    TerminalColor G a b O t := by
  classical
  apply free_center G a b O ab na empty _ t
  rcases O.eq_empty_or_nonempty with nil|nz
  · subst O
    exact (color_function ..).mpr ⟨fun _ => false,fun x xm y ym ed => by
      have h : x=b := by simpa using xm
      have j : y=b := by simpa using ym
      exact (ed.ne (h.trans j.symm)).elim⟩
  let S := univ\O
  let T := insert b O
  have ao : a∉O := fun h => (mem_sdiff.mp (sub h)).2 (mem_insert_self ..)
  have bo : b∉O := fun h => (mem_sdiff.mp (sub h)).2 (mem_insert_of_mem (mem_singleton_self _))
  have at' : a∉T := fun h => (not_or.mpr ⟨ab,ao⟩) (mem_insert.mp h)
  have memA : a∈S := mem_sdiff.mpr ⟨mem_univ _,ao⟩
  have stay (x : V) (xm : x∈O) (y : V) (ed : G.Adj x y) : y=b ∨ y∈O := by
    by_cases yb : y=b
    · exact Or.inl yb
    have ya : y≠a := fun eq => empty x xm (eq ▸ ed.symm)
    have ys : y∈univ\({a,b}:Finset V) := by simp [ya,yb]
    exact Or.inr ((cl x (sub xm) y ys ed).mp xm)
  have split : Split G b S T := by
    constructor
    · ext x;simp [S,T]
    · ext x;by_cases xb : x=b <;> simp [S,T,xb,bo]
    · intro x y ed
      by_cases xo : x∈O
      · exact Or.inr ⟨mem_insert_of_mem xo,mem_insert.mpr (stay x xo y ed)⟩
      by_cases yo : y∈O
      · exact Or.inr ⟨mem_insert.mpr (stay y yo x ed.symm),mem_insert_of_mem yo⟩
      exact Or.inl ⟨mem_sdiff.mpr ⟨mem_univ _,xo⟩,mem_sdiff.mpr ⟨mem_univ _,yo⟩⟩
    · rw [←card_univ]
      apply card_lt_card (ssubset_univ_iff.mpr ?_)
      obtain ⟨x,xo⟩ := nz
      exact fun eq => (mem_sdiff.mp (show x∈S from eq ▸ mem_univ _)).2 xo
    · rw [←card_univ]
      apply card_lt_card (ssubset_univ_iff.mpr ?_)
      exact fun eq => at' (eq ▸ mem_univ _)
  have col := saturated_wing_bip split gc hn rk r p A ai ⟨a,memA⟩ at' am pm sat
  obtain ⟨e,ok⟩ := (color_function ..).mp col
  apply (color_function ..).mpr
  refine ⟨fun x => e (split.flip.proj x),fun x xm y ym ed => ?_⟩
  change e (split.flip.proj x)≠e (split.flip.proj y)
  have ex : split.flip.proj x=⟨x,xm⟩ := split.flip.proj_in (⟨x,xm⟩ : ↥T)
  have ey : split.flip.proj y=⟨y,ym⟩ := split.flip.proj_in (⟨y,ym⟩ : ↥T)
  rw [ex,ey]
  exact ok _ (mem_univ _) _ (mem_univ _) ed

#print axioms inactive_free
end Minimal180.PairRepair
