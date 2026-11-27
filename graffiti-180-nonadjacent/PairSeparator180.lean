import FlipSeparator180
import PairColors180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- After choosing the two tip colors, bipartite repair is exactly a
vertex separator problem in the original bipartite remainder. Deleted
tips count against the same budget and protected vertices cannot be deleted. -/
theorem separator_iff (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A X : Finset V) (ai : Indep G A) (xi : Indep G X)
    (c : V→Bool) (cp : ProperOn G (univ\X) c) :
    Protected G r p A ↔ ∃ M : Finset V,Disjoint M (A∩insert r (parity G r p)) ∧ M.card≤allowance G r p A ∧
      ∃ d : V→Bool,Compatible G ((univ\X)\M) (X\M) c d := by
  classical
  let K := A∩insert r (parity G r p)
  have parts (M : Finset V) : ((univ\X)\M)∪(X\M)=univ\M := by
    ext x;simp only [mem_union,mem_sdiff,mem_univ,true_and];tauto
  have rule (M : Finset V) (d : V→Bool) :
      (∃ e,ProperOn G (univ\M) e ∧ ∀ t∈X\M,e t=d t) ↔ Compatible G ((univ\X)\M) (X\M) c d := by
    rw [←parts]
    apply extension_iff
    · exact disjoint_left.mpr (fun x xm xt => (mem_sdiff.mp (mem_sdiff.mp xm).1).2 (mem_sdiff.mp xt).1)
    · exact fun x xm y ym => cp x (mem_sdiff.mp xm).1 y (mem_sdiff.mp ym).1
    · exact fun x xm y ym ed => (xi x (mem_sdiff.mp xm).1 y (mem_sdiff.mp ym).1 ed.ne ed).elim
  rw [protected_iff G gc hn r p A ai]
  constructor
  · rintro ⟨Z,col,inZ,bound⟩
    let M := univ\Z
    have restored : univ\M=Z := Finset.sdiff_sdiff_eq_self (subset_univ _)
    have dis : Disjoint M K := disjoint_left.mpr (fun _ xm xk => (mem_sdiff.mp xm).2 (inZ xk))
    obtain ⟨e,ok⟩ := (color_function ..).mp col
    have sz := card_sdiff_add_card_eq_card (subset_univ Z);rw [card_univ] at sz
    refine ⟨M,dis,by change (univ\Z).card≤_;omega,e,(rule M e).mp ⟨e,restored ▸ ok,fun _ _ => rfl⟩⟩
  · rintro ⟨M,dis,bound,d,yes⟩
    obtain ⟨e,ok,_⟩ := (rule M d).mpr yes
    have sz := card_sdiff_add_card_eq_card (subset_univ M);rw [card_univ] at sz
    exact ⟨univ\M,(color_function ..).mpr ⟨e,ok⟩,
      fun x xk => mem_sdiff.mpr ⟨mem_univ _,fun xm => disjoint_left.mp dis xm xk⟩,by omega⟩

omit [Fintype V] [DecidableEq V] in
/-- For a singleton retained tip, all conflicts have the form of two
oppositely colored neighbors still joined by a path in the remainder. -/
theorem one_compatible (G : SimpleGraph V) (S : Finset V) (a : V) (c : V→Bool) :
    Compatible G S {a} c (fun _ => true) ↔
      ∀ x y,G.Adj a x → G.Adj a y → c x=true → c y=false → ¬Joined G S x y := by
  constructor
  · intro ok x y ax ay px py
    exact ok x y ⟨a,mem_singleton_self _,ax,by simp [px]⟩ ⟨a,mem_singleton_self _,ay,by simp [py]⟩
  · intro ok x y ⟨t,tm,tx,on⟩ ⟨u,um,uy,off⟩
    obtain rfl := mem_singleton.mp tm
    obtain rfl := mem_singleton.mp um
    exact ok x y tx uy (by simpa using on) (by simpa using off)

/-- In the single-protected failed branch, even after losing any one
additional unprotected remainder vertex there must be a path between
opposite-colored neighbors of a. The assertion also covers an empty deletion. -/
theorem solo_paths (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (bad : ¬Protected G r p A)
    (a b : V) (ab : a≠b) (bi : TwoColor G (univ\{a,b}))
    (ak : a∈A∩insert r (parity G r p)) (bk : b∉A∩insert r (parity G r p))
    (c : V→Bool) (cp : ProperOn G (univ\{a,b}) c) (F : Finset V)
    (dis : Disjoint F (A∩insert r (parity G r p))) (small : F.card≤1) :
    ∃ x y,G.Adj a x ∧ G.Adj a y ∧ c x=true ∧ c y=false ∧ Joined G ((univ\{a,b})\F) x y := by
  classical
  let X : Finset V := {a,b}
  let M := insert b F
  have na := (pair_obstruction G gc hn r p A ai bad a b ab bi).1
  have xi : Indep G X := pair_indep G na
  have am : a∉F := fun m => disjoint_left.mp dis m ak
  have tips : X\M={a} := by
    ext x
    simp only [X,M,mem_sdiff,mem_insert,mem_singleton]
    constructor
    · rintro ⟨alt,no⟩
      exact alt.resolve_right (fun xb => no (Or.inl xb))
    · rintro rfl
      exact ⟨Or.inl rfl,not_or.mpr ⟨ab,am⟩⟩
  have outside : (univ\X)\M=(univ\X)\F := by ext x;simp only [X,M,mem_sdiff,mem_univ,mem_insert,mem_singleton];tauto
  by_contra! no
  apply bad
  apply (separator_iff G gc hn r p A X ai xi c cp).mpr
  have budget := (solo_rigidity G gc hn r p A ai bad a b ab bi ak bk).2.1
  refine ⟨M,disjoint_insert_left.mpr ⟨bk,dis⟩,?_,fun _ => true,?_⟩
  · have cap := card_insert_le b F;change (insert b F).card≤_;omega
  · rw [tips,outside,one_compatible]
    exact no

#print axioms separator_iff
#print axioms one_compatible
#print axioms solo_paths
end Minimal180.PairRepair
