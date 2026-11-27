import MinimalAtomDomain

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.OddUncross
open ThreePort FourRingCutAux
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem shore_two_acyclic (c : V→Bool) (small : Fintype.card (Shore c)≤2) :
    (shoreGraph G c).IsAcyclic := by
  intro a w cy
  have lo := cy.three_le_length
  let f : Fin w.length→Shore c := fun i=>w.getVert i.val
  have inj : Function.Injective f := by
    intro p q eq
    apply Fin.ext
    exact cy.getVert_injOn' (show p.val≤w.length-1 by omega)
      (show q.val≤w.length-1 by omega) eq
  have hi := Fintype.card_le_of_injective f inj
  rw [Fintype.card_fin] at hi
  omega

private theorem shore_three_of_cubic (cub : ∀ v,G.degree v=3) {A : Finset V}
    (h : ShoreThree G A) : 3≤A.card := by
  classical
  refine Classical.byContradiction ?_
  intro not
  let c := colourOf A
  have le : Fintype.card (Shore c)≤2 := by
    let e : Shore c ↪ ↥A := ⟨fun u=>⟨u.val,colour_true.mp u.property⟩,
      fun _ _ eq=>Subtype.ext (congrArg (fun a : ↥A=>a.val) eq)⟩
    have eq := Fintype.card_le_of_injective e e.injective
    rw [Fintype.card_coe] at eq
    omega
  have ac := shore_two_acyclic (G:=G) c le
  apply h.2
  left
  intro x y xt yt
  refine Classical.byContradiction ?_
  intro ne
  have l := acyclic_shore_large_cut G c cub ac xt yt ne
  have eq : (boundary G c).card=3 := h.1
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem colour_safe_walk {D : Finset V} (c : V→Bool)
    (safe : ∀ {a b},a∉D→b∉D→G.Adj a b→c a=c b)
    {a b : {x : V // x∉D}} (w : (G.induce {v|v∉D}).Walk a b) : c a.val=c b.val := by
  induction w with
  | nil => rfl
  | @cons a b d e tail ih => exact (safe a.property b.property e).trans ih

private theorem fst_inj_on_shore (cub : ∀ v,G.degree v=3)
    (conn : KelmansStarter.ThreeConnected G) {A : Finset V}
    (h : ShoreThree G A) :
    Set.InjOn Prod.fst (↑(boundary G (colourOf A)) : Set (V×V)) := by
  classical
  let c := colourOf A
  let E := boundary G c
  let D := E.image Prod.fst
  have c3 : E.card=3 := h.1
  refine Classical.byContradiction ?_
  intro no
  have sm : D.card≤2 := by
    have le : D.card≤E.card := card_image_le
    have ne : D.card≠E.card := fun eq=>no (Finset.card_image_iff.mp eq)
    omega
  have inside : D⊆A := by
    intro v vm
    obtain ⟨k,km,kv⟩ := mem_image.mp vm
    exact kv ▸ colour_true.mp (mem_boundary.mp km).1
  have gap := shore_three_of_cubic cub h
  obtain ⟨x,xt,xD⟩ := exists_mem_not_mem_of_card_lt_card (show D.card<A.card by omega)
  obtain ⟨_,⟨y,yf⟩⟩ := both_colours_of_nontrivial h.2
  have yD : y∉D := fun d=>colour_false.mp yf (inside d)
  have safe {a b : V} (aD : a∉D) (bD : b∉D) (e : G.Adj a b) : c a=c b := by
    cases ha : c a <;> cases hb : c b
    · rfl
    · exact (bD (mem_image.mpr ⟨(b,a),mem_boundary.mpr ⟨hb,ha,e.symm⟩,rfl⟩)).elim
    · exact (aD (mem_image.mpr ⟨(a,b),mem_boundary.mpr ⟨ha,hb,e⟩,rfl⟩)).elim
    · rfl
  obtain ⟨w⟩ := (conn.2 D sm).preconnected ⟨x,xD⟩ ⟨y,yD⟩
  have equ := colour_safe_walk c safe w
  exact Bool.false_ne_true (((colour_true.mpr xt).symm.trans (equ.trans yf)).symm)

private theorem snd_inj_on_shore (cub : ∀ v,G.degree v=3)
    (conn : KelmansStarter.ThreeConnected G) {A : Finset V}
    (h : ShoreThree G A) :
    Set.InjOn Prod.snd (↑(boundary G (colourOf A)) : Set (V×V)) := by
  classical
  rintro ⟨a,b⟩ ab ⟨c,d⟩ cd eq
  obtain ⟨aA,bA,abE⟩ := mem_boundary.mp ab
  obtain ⟨cA,dA,cdE⟩ := mem_boundary.mp cd
  have conv {u v : V} (hf : colourOf A u=false) (ht : colourOf A v=true) (e : G.Adj u v) :
      (u,v)∈boundary G (colourOf Aᶜ) := by
    rw [colour_compl]
    exact mem_boundary.mpr ⟨by simp [hf],by simp [ht],e⟩
  have hcomp := fst_inj_on_shore cub conn (shore_compl G h)
  have rev : (b,a)=(d,c) := hcomp (conv bA aA abE.symm) (conv dA cA cdE.symm) eq
  exact congrArg Prod.swap rev

/-- Every nontrivial three-cut in a cubic 3-vertex-connected graph can
be enumerated as an exact three-port matching seam. -/
theorem shore_three_has_exact_seam (cub : ∀ v,G.degree v=3)
    (conn : KelmansStarter.ThreeConnected G) {A : Finset V}
    (h : ShoreThree G A) : ∃ p q : Fin 3→V, Seam (G:=G) A p q := by
  classical
  let E := boundary G (colourOf A)
  have n : Fintype.card (↑E : Type _) = 3 := (Fintype.card_coe E).trans h.1
  let beta : Fin 3≃(↑E : Type _) := (Fintype.equivFinOfCardEq n).symm
  let p (i : Fin 3) := (beta i).val.1
  let q (i : Fin 3) := (beta i).val.2
  have along (i : Fin 3) : colourOf A (p i)=true ∧ colourOf A (q i)=false ∧
      G.Adj (p i) (q i) := mem_boundary.mp (beta i).property
  refine ⟨p,q,⟨fun i=>colour_true.mp (along i).1,fun i=>colour_false.mp (along i).2.1,?_,?_,?_⟩⟩
  · intro i j eq
    have o := fst_inj_on_shore cub conn h (beta i).property (beta j).property eq
    exact beta.injective (Subtype.ext o)
  · intro i j eq
    have o := snd_inj_on_shore cub conn h (beta i).property (beta j).property eq
    exact beta.injective (Subtype.ext o)
  · intro a sa b sb
    constructor
    · intro f
      let l : (↑E : Type _) := ⟨(a,b),mem_boundary.mpr ⟨colour_true.mpr sa,colour_false.mpr sb,f⟩⟩
      let i := beta.symm l
      have eq := beta.apply_symm_apply l
      exact ⟨i,congrArg (fun z : (↑E : Type _)=>z.val.1) eq,
        congrArg (fun z : (↑E : Type _)=>z.val.2) eq⟩
    · rintro ⟨i,rfl,rfl⟩
      exact (along i).2.2

#print axioms shore_three_has_exact_seam
end
end KelmansCactus.AtomicBridge.OddUncross
