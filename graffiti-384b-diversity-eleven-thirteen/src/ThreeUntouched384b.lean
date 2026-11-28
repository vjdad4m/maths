import LargeLowerProfile384b
import FixedCubics

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open private Repair.nbr_add Repair.full_nbr Repair.omit_set Repair.triangles_le_choose from Repair384b
open private OddStars.FixedCubics.separated from FixedCubics
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem cubic_pair_nonadjacent
    {x y : V} (xd : G.degree x=3) (yd : G.degree y=3)
    (xs : 2≤trianglesAt G x) (ys : 2≤trianglesAt G y)
    (diff : trianglesAt G x≠trianglesAt G y) : ¬G.Adj x y := by
  have ax := Repair.triangles_le_choose G x
  have ay := Repair.triangles_le_choose G y
  have c : Nat.choose 3 2=3 := by decide
  rw [xd,c] at ax
  rw [yd,c] at ay
  by_cases q : trianglesAt G x=2
  · exact OddStars.FixedCubics.separated G xd yd q (by omega)
  · exact fun xy => OddStars.FixedCubics.separated G yd xd (by omega) (by omega) xy.symm

private theorem choose_three {U : Finset V} (four : 4≤U.card)
    (high : ∀ x∈U,3≤G.degree x) (scores : Set.InjOn (trianglesAt G) (U : Set V))
    (min : ∀ x∈U,2≤trianglesAt G x) :
    ∃ X⊆U,X.card=3 ∧ ∀ x∈X,2+nbr G x X≤G.degree x := by
  classical
  let B := U.filter (fun x=>G.degree x=3)
  let A := U.filter (fun x=>4≤G.degree x)
  have As : A ⊆ U := filter_subset _ _
  have Bs : B ⊆ U := filter_subset _ _
  have cover : A∪B=U := by
    ext x
    simp only [A,B,mem_union,mem_filter]
    constructor
    · exact fun h=>h.elim And.left And.left
    · intro xu
      have d := high x xu
      by_cases k : G.degree x=3
      · exact Or.inr ⟨xu,k⟩
      · exact Or.inl ⟨xu,by omega⟩
  have dis : Disjoint A B := by
    refine Finset.disjoint_left.mpr (fun x xa xb=>?_ )
    have ad := (mem_filter.mp xa).2
    have bd := (mem_filter.mp xb).2
    omega
  have split := card_union_of_disjoint dis
  rw [cover] at split
  have bcap : B.card≤2 := by
    let Y := B.image (trianglesAt G)
    have same : Y.card=B.card := card_image_of_injOn (fun x hx y hy eq=>
      scores (Bs hx) (Bs hy) eq)
    have sub : Y ⊆ ({2,3} : Finset Nat) := by
      intro j jm
      obtain ⟨x,xb,rfl⟩ := mem_image.mp jm
      have d := (mem_filter.mp xb).2
      have cap := Repair.triangles_le_choose G x
      have c : Nat.choose 3 2=3 := by decide
      rw [d,c] at cap
      have p := min x (Bs xb)
      have eq : trianglesAt G x=2 ∨ trianglesAt G x=3 := by omega
      simpa using eq
    have c := card_le_card sub
    rw [same,card_pair (by decide : (2:Nat)≠3)] at c
    exact c
  have upper (X : Finset V) (xc : X.card=3) {x : V} (xm : x∈X) :
      nbr G x X≤2 := by
    have incl : X.filter (G.Adj x) ⊆ X.erase x := by
      intro y ym
      exact mem_erase.mpr ⟨(mem_filter.mp ym).2.ne.symm,(mem_filter.mp ym).1⟩
    have c := card_le_card incl
    rwa [card_erase_of_mem xm,xc] at c
  by_cases enough : 3≤A.card
  · obtain ⟨X,XA,xc⟩ := exists_subset_card_eq enough
    refine ⟨X,XA.trans As,xc,fun x xm=>?_⟩
    have d := (mem_filter.mp (XA xm)).2
    have c := upper X xc xm
    omega
  · have be : B.card=2 := by omega
    have ae : A.card=2 := by omega
    obtain ⟨x,y,xy,eq⟩ := card_eq_two.mp be
    have xb : x∈B := eq ▸ mem_insert_self ..
    have yb : y∈B := eq ▸ mem_insert_of_mem (mem_singleton_self _)
    obtain ⟨z,za⟩ := card_pos.mp (show 0<A.card by omega)
    have xz : x≠z := fun h=>Finset.disjoint_left.mp dis (h ▸ za) xb
    have yz : y≠z := fun h=>Finset.disjoint_left.mp dis (h ▸ za) yb
    let X : Finset V := {x,y,z}
    have xc : X.card=3 := by
      have xout : x∉({y,z} : Finset V) := by simp [xy,xz]
      simp only [X,card_insert_of_not_mem xout,card_pair yz]
    have xy0 := cubic_pair_nonadjacent G (mem_filter.mp xb).2 (mem_filter.mp yb).2
      (min x (Bs xb)) (min y (Bs yb)) (fun h=>xy (scores (Bs xb) (Bs yb) h))
    refine ⟨X,?_,xc,?_⟩
    · intro u um
      rcases (show u=x ∨ u=y ∨ u=z by simpa [X] using um) with rfl|rfl|rfl
      · exact Bs xb
      · exact Bs yb
      · exact As za
    · have small {u v : V} (uv : ¬G.Adj u v)
          (shape : ∀ w,w∈X → w=u ∨ w=v ∨ w=z) :
          nbr G u X≤1 := by
        have sub : X.filter (G.Adj u)⊆({z} : Finset V) := by
          intro w wm
          obtain ⟨wx,uw⟩ := mem_filter.mp wm
          rcases shape w wx with w0|w0|w0
          · exact (uw.ne w0.symm).elim
          · exact (uv (w0 ▸ uw)).elim
          · exact mem_singleton.mpr w0
        simpa only [nbr,card_singleton] using card_le_card sub
      intro u um
      have shape (w : V) (wm : w∈X) : w=x ∨ w=y ∨ w=z := by simpa [X] using wm
      rcases shape u um with hu|hu|hu
      · subst u
        have n := small xy0 shape
        have d := (mem_filter.mp xb).2
        omega
      · subst u
        have n := small (fun h=>xy0 h.symm) (fun w wm=>(shape w wm).elim
          (fun h=>Or.inr (Or.inl h)) (fun h=>h.elim Or.inl (fun h=>Or.inr (Or.inr h))))
        have d := (mem_filter.mp yb).2
        omega
      · subst u
        have n := upper X xc um
        have d := (mem_filter.mp za).2
        omega

theorem exact_of_three_low_footprint_five (t : (types G).card=11)
    (nine : (high G).card=9)
    (scores : Set.InjOn (trianglesAt G) (high G : Set V))
    (min : ∀ x∈high G,2≤trianglesAt G x)
    {O P : Finset V} (three : 3≤O.card)
    (low : Disjoint O (high G))
    (deg : ∀ x∈O,2≤G.degree x)
    (ind : ∀ x∈O,∀ y∈O,¬G.Adj x y)
    (touch : ∀ z∈high G,(∃ x∈O,G.Adj x z)→z∈P)
    (five : P.card≤5) : gamma G≤bound G := by
  classical
  let U := high G \ P
  have us : U ⊆ high G := sdiff_subset
  have four : 4≤U.card := by
    have cnt := card_sdiff_add_card_eq_card (show high G∩P ⊆ high G from inter_subset_left)
    have cap := card_le_card (show high G∩P ⊆ P from inter_subset_right)
    have eq : high G \ (high G∩P)=U := by ext x; simp [U]
    rw [eq] at cnt
    omega
  obtain ⟨X,xu,xc,feas⟩ := choose_three G four (fun x h=>(mem_filter.mp (us h)).2)
    (fun _ hx _ hy eq=>scores (us hx) (us hy) eq) (fun x h=>min x (us h))
  have dis := low.mono_right (xu.trans us)
  have unt (x : V) (xo : x∈O) (y : V) (yx : y∈X) : ¬G.Adj x y :=
    fun a=>(mem_sdiff.mp (xu yx)).2 (touch y (us (xu yx)) ⟨x,xo,a⟩)
  have om := Repair.omit_set G (O∪X) (by
    intro x xm
    have part := Repair.full_nbr G x (O∪X)
    rw [Repair.nbr_add G x dis] at part
    have nz (S : Finset V) (h : ∀ y∈S,¬G.Adj x y) : nbr G x S=0 := by
      rw [nbr,filter_eq_empty_iff.mpr h,card_empty]
    rcases mem_union.mp xm with xo|xx
    · have a := nz O (ind x xo)
      have b := nz X (unt x xo)
      have d := deg x xo
      omega
    · have a := nz O (fun y yo h=>unt y yo x xx h.symm)
      have b := feas x xx
      omega)
  have ca := card_union_of_disjoint dis
  unfold bound
  rw [t]
  omega

#print axioms exact_of_three_low_footprint_five
end Graffiti384b.DiversityEleven
