import BagMetric180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B}

/-- The fiber over i contains two distinct nonadjacent vertices. -/
def NonCliqueBag (H : SimpleGraph V) (f : V→B) (i : B) : Prop :=
  ∃ x y,f x=i ∧ f y=i ∧ x≠y ∧ ¬H.Adj x y

/-- For each independent base support, one maximum bipartite witness
contains all the nonclique bags on that support. -/
def CoversBags (H : SimpleGraph V) (G : SimpleGraph B) (f : V→B) : Prop :=
  ∀ I : Finset B,Indep G I → ∃ Z : Finset B,TwoColor G Z ∧ Z.card=bipartiteNum G ∧
    ∀ i∈I,NonCliqueBag H f i → i∈Z

omit [Fintype V] [DecidableEq V] [Fintype B] in
theorem Bags.indSupport (h : Bags H G f) (A : Finset V) (ai : Indep H A) : Indep G (A.image f) := by
  classical
  intro i im j jm ne edge
  obtain ⟨x,xm,rfl⟩ := mem_image.mp im; obtain ⟨y,ym,rfl⟩ := mem_image.mp jm
  exact ai x xm y ym (fun same => ne (congrArg f same)) (h.edgeUp edge)

theorem Bags.colorExtra (h : Bags H G f) (t : B→V) (sec : Function.LeftInverse f t)
    (Z : Finset B) (col : TwoColor G Z) (X : Finset V) (ind : Indep H X)
    (over : ∀ x∈X,f x∈Z) (avoid : ∀ x∈X,¬H.Adj x (t (f x)))
    (out : Disjoint X (univ.image t)) :
    Z.card+X.card≤bipartiteNum H := by
  classical
  obtain ⟨c,colors⟩ := (color_function ..).mp col
  let W := Z.image t ∪ X
  have inZ {x : V} (xm : x∈W) : f x∈Z := by
    rcases mem_union.mp xm with hit|xx
    · obtain ⟨i,im,rfl⟩ := mem_image.mp hit; rwa [sec i]
    · exact over x xx
  have upper : TwoColor H W := by
    apply (color_function ..).mpr
    refine ⟨fun x => c (f x),fun x xm y ym edge => ?_⟩
    by_cases ne : f x≠f y
    · exact colors _ (inZ xm) _ (inZ ym) ((h.across ne).mp edge)
    exfalso
    have eq : f x=f y := not_not.mp ne
    rcases mem_union.mp xm with xr|xx <;> rcases mem_union.mp ym with yr|yy
    · obtain ⟨i,_,rfl⟩ := mem_image.mp xr; obtain ⟨j,_,rfl⟩ := mem_image.mp yr
      rw [sec i,sec j] at eq; exact edge.ne (congrArg t eq)
    · obtain ⟨i,_,rfl⟩ := mem_image.mp xr
      rw [sec i] at eq; exact avoid y yy (eq ▸ edge.symm)
    · obtain ⟨j,_,rfl⟩ := mem_image.mp yr
      rw [sec j] at eq; exact avoid x xx (eq.symm ▸ edge)
    · exact ind _ xx _ yy edge.ne edge
  have dis : Disjoint (Z.image t) X := out.symm.mono_left (image_subset_image (subset_univ _))
  have b := size_bip H upper
  change (Z.image t∪X).card≤_ at b
  rwa [card_union_of_disjoint dis,card_image_of_injective _ sec.injective] at b

theorem Bags.reserve (h : Bags H G f) (cover : CoversBags H G f)
    (A P : Finset V) (ai : Indep H A) (t : B→V) (sec : Function.LeftInverse f t)
    (avoid : ∀ x∈(A∩P)\univ.image t,¬H.Adj x (t (f x))) :
    bipartiteNum G+((A∩P)\univ.image t).card≤bipartiteNum H := by
  classical
  let X := (A∩P)\univ.image t
  obtain ⟨Z,col,sz,all⟩ := cover (A.image f) (h.indSupport A ai)
  have ind : Indep H X := fun x hx y hy => ai x (mem_inter.mp (mem_sdiff.mp hx).1).1 y (mem_inter.mp (mem_sdiff.mp hy).1).1
  have over (x : V) (xm : x∈X) : f x∈Z := by
    apply all (f x) (mem_image_of_mem _ (mem_inter.mp (mem_sdiff.mp xm).1).1)
    exact ⟨x,t (f x),rfl,sec _,fun eq => (mem_sdiff.mp xm).2 (eq ▸ mem_image_of_mem _ (mem_univ _)),avoid x xm⟩
  rw [←sz]; exact h.colorExtra t sec Z col X ind over avoid (disjoint_left.mpr (fun _ m => (mem_sdiff.mp m).2))

#print axioms Bags.indSupport
#print axioms Bags.colorExtra
#print axioms Bags.reserve
end Minimal180.Substitution
