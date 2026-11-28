import AdjacentCutFiveFourteenDarkBridge189

namespace Graffiti189LongestPath.CrossSaturation.FiveAdjacent
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem terminal_route_on_of_local_ore (S : Finset V) {x y : V}
    (xm : x∈S) (ym : y∈S) (xy : x≠y)
    (ore : ∀ u∈S,∀ v∈S,u≠v → ¬G.Adj u v →
      S.card+1≤(inside G S u).card+(inside G S v).card) :
    RouteOn G S x y := by
  classical
  let T := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let x' : T := ⟨x,xm⟩
  let y' : T := ⟨y,ym⟩
  have sz : Fintype.card T=S.card := Fintype.card_coe S
  have f (u v : T) (h : u≠v) (no : ¬J.Adj u v) : Fintype.card T+1≤J.degree u+J.degree v := by
    rw [sz,←inside_card_eq_degree_induce (G:=G) S u,←inside_card_eq_degree_induce (G:=G) S v]
    exact ore u.val u.property v.val v.property (fun e=>h (Subtype.ext e)) no
  obtain ⟨p,pp,ps⟩ := hamilton_connected_of_ore f (x:=x') (y:=y')
    (fun e=>xy (congrArg Subtype.val e))
  exact lift_side_path S p pp ps

theorem terminal_route_on_via_one_exception (S : Finset V) {l x y u v : V}
    (lm : l∈S) (xm : x∈S.erase l) (ym : y∈S.erase l) (xy : x≠y)
    (um : u∈S.erase l) (vm : v∈S.erase l) (uv : u≠v)
    (lu : G.Adj l u) (lv : G.Adj l v)
    (avoid : ¬((x=u ∧ y=v) ∨ (x=v ∧ y=u)))
    (ore : ∀ u∈S.erase l,∀ v∈S.erase l,u≠v → ¬G.Adj u v →
      S.card+1≤(inside G S u).card+(inside G S v).card) :
    RouteOn G S x y := by
  classical
  let T := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let l' : T := ⟨l,lm⟩
  let x' : T := ⟨x,(mem_erase.mp xm).2⟩
  let y' : T := ⟨y,(mem_erase.mp ym).2⟩
  let u' : T := ⟨u,(mem_erase.mp um).2⟩
  let v' : T := ⟨v,(mem_erase.mp vm).2⟩
  let A := (univ : Finset T).erase l'
  have sz : Fintype.card T=S.card := Fintype.card_coe S
  have f (u : T) (um : u∈A) (v : T) (vm : v∈A) (h : u≠v) (no : ¬J.Adj u v) :
      Fintype.card T+1≤J.degree u+J.degree v := by
    rw [sz,←inside_card_eq_degree_induce (G:=G) S u,←inside_card_eq_degree_induce (G:=G) S v]
    exact ore u.val (mem_erase.mpr ⟨fun e=>(mem_erase.mp um).1 (Subtype.ext e),u.property⟩)
      v.val (mem_erase.mpr ⟨fun e=>(mem_erase.mp vm).1 (Subtype.ext e),v.property⟩)
      (fun e=>h (Subtype.ext e)) no
  have memA {z : T} (h : z.val∈S.erase l) : z∈A :=
    mem_erase.mpr ⟨fun e=>(mem_erase.mp h).1 (congrArg Subtype.val e),mem_univ _⟩
  have o' : ¬((x'=u' ∧ y'=v') ∨ (x'=v' ∧ y'=u')) := by
    intro z
    rcases z with ⟨h,k⟩|⟨h,k⟩
    · exact avoid (.inl ⟨congrArg Subtype.val h,congrArg Subtype.val k⟩)
    · exact avoid (.inr ⟨congrArg Subtype.val h,congrArg Subtype.val k⟩)
  obtain ⟨p,pp,ps⟩ := terminal_route_through_one_dark_exception (J:=J) A
    (insert_erase (mem_univ _)) (not_mem_erase _ _) (memA xm) (memA ym)
    (fun e=>xy (congrArg Subtype.val e)) (memA um) (memA vm)
    (fun e=>uv (congrArg Subtype.val e)) (show J.Adj l' u' from lu) (show J.Adj l' v' from lv) o' f
  exact lift_side_path S p pp (fun z=>(ps z).mpr (mem_univ _))

#print axioms terminal_route_on_of_local_ore
#print axioms terminal_route_on_via_one_exception
end Graffiti189LongestPath.CrossSaturation.FiveAdjacent
