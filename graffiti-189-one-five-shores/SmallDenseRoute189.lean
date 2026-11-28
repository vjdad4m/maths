import TerminalOreClosure189
import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph Finset ArticulationPair
open private lift_side_path from DegreeFiveSmallSides189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

theorem terminal_route_of_dense_finset
    (S : Finset V) {x y : V} (xs : x∈S) (ys : y∈S) (xy : x≠y)
    (dense : ∀ u∈S, S.card+1 ≤ 2*(S.filter (G.Adj u)).card) :
    RouteOn G S x y := by
  classical
  let U := ↑(↑S : Set V)
  let J := G.induce (↑S : Set V)
  let H := completeWith J (univ : Finset U)
  letI : DecidableRel H.Adj := Classical.decRel _
  let xx : U := ⟨x,xs⟩
  let yy : U := ⟨y,ys⟩
  obtain ⟨p,hp,hs⟩ := path_between_in_clique (univ : Finset U)
    (completeWith_of_mem J _) (mem_univ xx) (mem_univ yy) (fun e=>xy (congrArg Subtype.val e))
  have cap (u v : U) (_ : H.Adj u v) (_ : ¬J.Adj u v) :
      Fintype.card U+1≤J.degree u+J.degree v := by
    have num : Fintype.card U=S.card := Fintype.card_coe S
    have h := dense u.val u.property
    have k := dense v.val v.property
    change S.card+1≤2*(inside G S u.val).card at h
    change S.card+1≤2*(inside G S v.val).card at k
    rw [inside_card_eq_degree_induce (G:=G) S u] at h
    rw [inside_card_eq_degree_induce (G:=G) S v] at k
    change S.card+1≤2*J.degree u at h
    change S.card+1≤2*J.degree v at k
    omega
  obtain ⟨q,hq,all⟩ := terminal_ore_closure (completeWith_mono J _) cap p hp
    (fun u=>(hs u).mpr (mem_univ _))
  exact lift_side_path S q hq all

theorem three_finset_spanning_path
    (T : Finset V) (three : T.card=3)
    (noiso : ∀ x∈T,∃ y∈T,G.Adj x y) :
    ∃ x∈T,∃ y∈T,RouteOn G T x y := by
  classical
  obtain ⟨x,y,z,xy,xz,yz,eq⟩ := card_eq_three.mp three
  have xT : x∈T := by simp [eq]
  have yT : y∈T := by simp [eq]
  have zT : z∈T := by simp [eq]
  have hit (u : V) (uT : u∈T) : G.Adj u x ∨ G.Adj u y ∨ G.Adj u z := by
    obtain ⟨v,vT,uv⟩ := noiso u uT
    have vCases : v=x ∨ v=y ∨ v=z := by simpa [eq] using vT
    rcases vCases with e|e|e
    · exact .inl (e ▸ uv)
    · exact .inr (.inl (e ▸ uv))
    exact .inr (.inr (e ▸ uv))
  by_cases ex : G.Adj x y
  · have h : G.Adj z x ∨ G.Adj z y := by
      rcases hit z zT with x|y|z
      · exact .inl x
      · exact .inr y
      exact (G.loopless _ z).elim
    rcases h with zx|zy
    · have e : ({z,x,y} : Finset V)=T := by rw [eq]; ext v; simp [or_comm,or_left_comm,or_assoc]
      exact ⟨z,zT,y,yT,e ▸ RouteOn.three zx ex yz.symm⟩
    exact ⟨x,xT,z,zT,eq.symm ▸ RouteOn.three ex zy.symm xz⟩
  have xz' : G.Adj x z := by
    rcases hit x xT with h|h|h
    · exact (G.loopless x h).elim
    · exact (ex h).elim
    exact h
  have yz' : G.Adj y z := by
    rcases hit y yT with h|h|h
    · exact (ex h.symm).elim
    · exact (G.loopless y h).elim
    exact h
  have e : ({x,z,y} : Finset V)=T := by rw [eq]; ext v; simp [or_comm,or_left_comm,or_assoc]
  exact ⟨x,xT,y,yT,e ▸ RouteOn.three xz' yz'.symm xy⟩

#print axioms terminal_route_of_dense_finset
#print axioms three_finset_spanning_path
end Graffiti189LongestPath.CrossSaturation
