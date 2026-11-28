import SharedZeroAnchor
import HallFiniteBase

namespace Graffiti384b.OddStars.HallArms
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]

def domain (e z : V) : Finset V := (({e,z}:Finset V)∪J.neighborFinset z)ᶜ

def options (e z v : V) : Finset V :=
  (insert v ((inside J ({e,z}ᶜ)).neighborFinset v)) \ J.neighborFinset e

omit [Fintype V] [DecidableEq V] in
private theorem closed_walk {K : SimpleGraph V} {R : Finset V}
    (closed : ∀{a b},K.Adj a b → a∈R → b∈R) {s t : V} (walk : K.Walk s t) (sm : s∈R) : t∈R := by
  induction walk with
  | nil => exact sm
  | cons edge tail ih => exact ih (closed edge sm)

/-- For two nonadjacent terminals, connectivity after deleting any third
vertex supplies a matching of the nonterminal vertices outside the final neighborhood.
The first terminal must have degree two. -/
theorem hall_matching {e z : V} (ez : e≠z) (off : ¬J.Adj e z) (de : J.degree e=2)
    (survive : ∀c,e≠c → z≠c → (inside J ({c}ᶜ)).Reachable e z) :
    ∃f : (v : domain J e z) → V, Function.Injective f ∧ ∀v : domain J e z,f v∈options J e z v := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' (fun (v : domain J e z) => options J e z v)).mp
  intro S
  let X := S.image Subtype.val
  let A := J.neighborFinset e
  let Y := S.biUnion (fun v => options J e z v)
  let F := Y\X
  let U := (A\X)∪F
  have sx : X.card=S.card := card_image_of_injective S Subtype.val_injective
  have xsub : X⊆domain J e z := by
    intro a am; obtain ⟨v,_,rfl⟩ := mem_image.mp am; exact v.2
  have clean {a : V} (m : a∈X) : a∉({e,z}:Finset V) ∧ ¬J.Adj z a := by
    have dm := mem_compl.mp (xsub m)
    exact ⟨fun h => dm (mem_union_left _ h),fun h => dm (mem_union_right _ ((J.mem_neighborFinset ..).mpr h))⟩
  have opt {a b : V} (am : a∈X) (bm : b∈options J e z a) : b∈Y := by
    obtain ⟨v,vm,rfl⟩ := mem_image.mp am; exact mem_biUnion.mpr ⟨v,vm,bm⟩
  have int : Y∩X=X\A := by
    ext a
    constructor
    · intro m; obtain ⟨v,_,om⟩ := mem_biUnion.mp (mem_inter.mp m).1
      exact mem_sdiff.mpr ⟨(mem_inter.mp m).2,(mem_sdiff.mp om).2⟩
    · intro m; obtain ⟨xm,na⟩ := mem_sdiff.mp m
      exact mem_inter.mpr ⟨opt xm (mem_sdiff.mpr ⟨mem_insert_self ..,na⟩),xm⟩
  have yy : ∀a∈Y,a∉({e,z}:Finset V) := by
    intro a am
    obtain ⟨v,vm,om⟩ := mem_biUnion.mp am
    rcases mem_insert.mp (mem_sdiff.mp om).1 with rfl|m
    · exact (clean (mem_image_of_mem Subtype.val vm)).1
    · have h := ((inside J ({e,z}ᶜ)).mem_neighborFinset ..).mp m
      exact mem_compl.mp h.2.2
  apply Nat.le_of_not_gt; intro small
  change Y.card<S.card at small
  have c₁ := card_sdiff_add_card_inter Y X
  rw [int] at c₁
  have c₂ := card_sdiff_add_card_inter X A
  have c₃ := card_sdiff_add_card_inter A X
  rw [inter_comm A X] at c₃
  have ca : A.card=2 := (J.card_neighborFinset_eq_degree _).trans de
  have us : U.card≤1 := by
    have up := card_union_le (A\X) F
    change (A\X).card+F.card ≥ U.card at up
    change F.card+(X\A).card=Y.card at c₁
    omega
  have extremes {a : V} (am : a∈U) : a≠e ∧ a≠z := by
    rcases mem_union.mp am with m|m
    · have ea := (J.mem_neighborFinset ..).mp (mem_sdiff.mp m).1
      exact ⟨ea.ne.symm,fun h => off (h ▸ ea)⟩
    · have n := yy _ (mem_sdiff.mp m).1
      exact ⟨fun h => n (h ▸ mem_insert_self ..),fun h => n (h ▸ mem_insert_of_mem (mem_singleton_self _))⟩
  obtain ⟨c,ec,zc,sub⟩ : ∃c,e≠c ∧ z≠c ∧ U⊆{c} := by
    by_cases h : U.Nonempty
    · obtain ⟨c,m⟩ := h
      exact ⟨c,(extremes m).1.symm,(extremes m).2.symm, fun a am => mem_singleton.mpr (card_le_one.mp us _ am _ m)⟩
    · obtain ⟨c,m⟩ := card_pos.mp (show 0<A.card by omega)
      have ec := (J.mem_neighborFinset ..).mp m
      exact ⟨c,ec.ne,fun eq => off (eq.symm ▸ ec), fun _ am => (h ⟨_,am⟩).elim⟩
  let K := inside J ({c}ᶜ)
  let R := insert e X
  have closed {a b : V} (ab : K.Adj a b) (ar : a∈R) : b∈R := by
    have nb : b∉U := fun h => mem_compl.mp ab.2.2 (sub h)
    have ba (m : b∈A) : b∈X := by
      by_contra nx; exact nb (mem_union_left _ (mem_sdiff.mpr ⟨m,nx⟩))
    rcases mem_insert.mp ar with rfl|ax
    · exact mem_insert_of_mem (ba ((J.mem_neighborFinset ..).mpr ab.1))
    by_cases be : b=e
    · exact mem_insert.mpr (Or.inl be)
    have bz : b≠z := fun eq => (clean ax).2 (eq ▸ ab.1.symm)
    by_cases bm : b∈A
    · exact mem_insert_of_mem (ba bm)
    have edge : (inside J ({e,z}ᶜ)).Adj a b := ⟨ab.1,mem_compl.mpr (clean ax).1,by simp [be,bz]⟩
    have bym := opt ax (mem_sdiff.mpr ⟨mem_insert_of_mem (((inside J ({e,z}ᶜ)).mem_neighborFinset ..).mpr edge),bm⟩)
    apply mem_insert_of_mem
    by_contra n
    exact nb (mem_union_right _ (mem_sdiff.mpr ⟨bym,n⟩))
  obtain ⟨walk⟩ := survive c ec zc
  have hit := closed_walk (K:=K) (R:=R) (fun edge m => closed edge m) walk (mem_insert_self ..)
  have zx := (mem_insert.mp hit).resolve_left ez.symm
  exact (clean zx).1 (by simp)

end Graffiti384b.OddStars.HallArms
#print axioms Finset.all_card_le_biUnion_card_iff_existsInjective'
#print axioms Graffiti384b.OddStars.HallArms.hall_matching