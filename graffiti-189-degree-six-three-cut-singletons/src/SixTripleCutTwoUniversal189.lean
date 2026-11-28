import SixTripleCutSingletonActual189

namespace Graffiti189LongestPath.ThresholdSix.ThreeCut
open Finset SimpleGraph SimpleGraph.Walk
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark from SixTripleCutSingleton189
open private Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible from SixTripleCutNonSingletonIsolate189

theorem Shore.dark_degree_le_inside {S A : Finset V} (sh : Shore G S A)
    {x : V} (xd : x∈dark G S A) : G.degree x≤A.card-1 := by
  have xa := (mem_sdiff.mp xd).1
  have sub : G.neighborFinset x⊆A.erase x := by
    intro y ym
    have xy := (G.mem_neighborFinset ..).mp ym
    have ya := (sh.closed x xa y xy).resolve_right
      (fun h=>Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark xd h xy)
    exact mem_erase.mpr ⟨xy.ne.symm,ya⟩
  have c := card_le_card sub
  rwa [card_neighborFinset_eq_degree,card_erase_of_mem xa] at c

theorem Shore.dark_foreign_dist_ge_four (hc : G.Connected) {S A B : Finset V}
    (shA : Shore G S A) (shB : Shore G S B) (ab : Disjoint A B)
    {x y : V} (xa : x∈dark G S A) (yb : y∈dark G S B) : 4≤G.dist x y := by
  classical
  have xn := (mem_sdiff.mp xa).1
  have yn := (mem_sdiff.mp yb).1
  have ne : x≠y := fun e=>disjoint_left.mp ab xn (e ▸ yn)
  have no : ¬G.Adj x y := fun h=>
    (shA.closed x xn y h).elim (fun ya=>disjoint_left.mp ab ya yn)
      (fun ys=>disjoint_left.mp shB.disjoint yn ys)
  have gt := hc.one_lt_dist_of_ne_of_not_adj ne no
  by_contra! low
  obtain ⟨p,pl⟩ := hc.exists_walk_length_eq_dist x y
  let u := p.getVert 1
  have xu : G.Adj x u := by simpa [u] using p.adj_getVert_succ (i:=0) (by omega : 0<p.length)
  have us := (shA.closed x xn u xu).resolve_right
    (fun h=>Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark xa h xu)
  by_cases l2 : p.length=2
  · have uy : G.Adj u y := by
      have adj := p.adj_getVert_succ (i:=1) (by omega)
      rwa [show p.getVert 2=y by rw [←l2,getVert_length]] at adj
    have ub := (shB.closed y yn u uy.symm).resolve_right
      (fun h=>Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark yb h uy.symm)
    exact disjoint_left.mp ab us ub
  · have l3 : p.length=3 := by omega
    let v := p.getVert 2
    have uv : G.Adj u v := p.adj_getVert_succ (i:=1) (by omega)
    have vy : G.Adj v y := by
      have adj := p.adj_getVert_succ (i:=2) (by omega)
      rwa [show p.getVert 3=y by rw [←l3,getVert_length]] at adj
    have vb := (shB.closed y yn v vy.symm).resolve_right
      (fun h=>Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark yb h vy.symm)
    exact (shA.closed u us v uv).elim (fun va=>disjoint_left.mp ab va vb)
      (fun vs=>disjoint_left.mp shB.disjoint vb vs)

private theorem two_univ_small_side_impossible
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S A B : Finset V} (ss : S.card=3)
    (shA : Shore G S A) (shB : Shore G S B) (ab : Disjoint A B)
    (a4 : 4≤A.card) (b4 : 4≤B.card) (aSmall : A.card<7)
    (va3 : (visible G S A).card=3) (vb3 : (visible G S B).card=3)
    {x y : V} (_xa : x∈A) (_yb : y∈B) (ux : ∀ t∈S,G.Adj x t) (uy : ∀ t∈S,G.Adj y t)
    (insideA : ∀ w∈A,w=x∨G.Adj x w) (insideB : ∀ w∈B,w=y∨G.Adj y w) : False := by
  classical
  have vA : visible G S A⊆A := filter_subset _ _
  have vB : visible G S B⊆B := filter_subset _ _
  obtain ⟨s,sd⟩ := card_pos.mp (show 0<(dark G S A).card by
    unfold dark
    rw [card_sdiff vA,va3]
    omega)
  have sa := (mem_sdiff.mp sd).1
  have low : G.degree s<6 := by have d := shA.dark_degree_le_inside sd; omega
  have high (z : V) (zb : z∈B) : 6≤G.degree z := by
    have ne : z≠s := fun e=>disjoint_left.mp ab sa (e ▸ zb)
    exact (degree z s ne).resolve_right (by omega)
  have b7 := seven_of_three_visible_and_all_high shB b4 vb3 high
  have bDark : 4≤(dark G S B).card := by
    unfold dark
    rw [card_sdiff vB,vb3]
    omega
  obtain ⟨t,ts⟩ := card_pos.mp (show 0<S.card by omega)
  have sx : G.Adj s x := by
    apply SimpleGraph.Adj.symm
    refine (insideA s sa).resolve_left ?_
    intro e
    have d := Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark sd ts
    exact d (e ▸ ux t ts)
  have far (z : V) (zd : z∈dark G S B) : G.dist s z=4 := by
    have za := (mem_sdiff.mp zd).1
    have yz : G.Adj y z := (insideB z za).resolve_left (fun e=>
      Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark zd ts (e ▸ uy t ts))
    have upper := G.dist_le (Walk.cons sx (Walk.cons (ux t ts)
      (Walk.cons (uy t ts).symm (Walk.cons yz .nil))))
    have lower := shA.dark_foreign_dist_ge_four hc shB ab sd zd
    simp only [length_cons,length_nil] at upper
    omega
  let F := S∪dark G S B
  have dis : Disjoint S (dark G S B) := shB.disjoint.symm.mono_right sdiff_subset
  have off : s∉F := fun h=>(mem_union.mp h).elim (fun h=>disjoint_left.mp shA.disjoint sa h)
    (fun h=>disjoint_left.mp ab sa (mem_sdiff.mp h).1)
  have sub : insert s F⊆EvenFrom G s := by
    intro z zm
    rcases mem_insert.mp zm with rfl|h
    · simp [EvenFrom,SimpleGraph.dist_self]
    rcases mem_union.mp h with zs|zd
    · have ne : s≠z := fun e=>disjoint_left.mp shA.disjoint sa (e ▸ zs)
      have d := two_of_common hc ne
        (Graffiti189LongestPath.ThresholdSix.ThreeCut.no_adj_dark sd zs) sx (ux z zs)
      have e : G.dist s z=2 := by simpa [DistanceTwo] using d
      simp only [EvenFrom,mem_filter,mem_univ,true_and,e]
      decide
    · have e := far z zd
      simp only [EvenFrom,mem_filter,mem_univ,true_and,e]
      decide
  have count := (card_le_card sub).trans (cap s)
  rw [card_insert_of_not_mem off,show F.card=S.card+(dark G S B).card from card_union_of_disjoint dis,ss] at count
  omega

/-- Without a singleton component, universal ports cannot occur in
two different shores of a degree-six three-cut. -/
theorem no_two_universal_nonsingleton_shores
    (hc : G.Connected) (cap : ∀ v,(EvenFrom G v).card≤7) (conn : ThreeConnected G)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    {S A B C : Finset V} (ss : S.card=3)
    (shA : Shore G S A) (shB : Shore G S B) (shC : Shore G S C)
    (cA : (G.induce (↑A : Set V)).Connected) (cB : (G.induce (↑B : Set V)).Connected)
    (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C)
    (a4 : 4≤A.card) (b4 : 4≤B.card) (c4 : 4≤C.card)
    {x y : V} (xa : x∈A) (yb : y∈B) (ux : ∀ t∈S,G.Adj x t) (uy : ∀ t∈S,G.Adj y t) : False := by
  classical
  have va := shA.visible_lower ss conn (by omega)
  have vb := shB.visible_lower ss conn (by omega)
  have vc := shC.visible_lower ss conn (by omega)
  obtain ⟨vb3,_,insideA⟩ := universal_port_saturates_other_shores hc cap shA cA shB shC
    ab ac bc vb vc xa ux
  obtain ⟨va3,_,insideB⟩ := universal_port_saturates_other_shores hc cap shB cB shA shC
    ab.symm bc ac va vc yb uy
  by_cases aSmall : A.card<7
  · exact two_univ_small_side_impossible hc cap degree ss shA shB ab a4 b4 aSmall va3 vb3
      xa yb ux uy insideA insideB
  by_cases bSmall : B.card<7
  · exact two_univ_small_side_impossible hc cap degree ss shB shA ab.symm b4 a4 bSmall vb3 va3
      yb xa uy ux insideB insideA
  obtain ⟨t,ts⟩ := card_pos.mp (show 0<S.card by omega)
  have a := shore_card_of_universal_inside hc shA xa ux insideA ts
  have b := shore_card_of_universal_inside hc shB yb uy insideB ts
  have aa := card_le_card (Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible (G:=G) (W:=A) ts)
  have bb := card_le_card (Graffiti189LongestPath.ThresholdSix.ThreeCut.ports_subset_visible (G:=G) (W:=B) ts)
  have lim := three_local_twos_le_six cap ab ac bc t
  omega

#print axioms Shore.dark_foreign_dist_ge_four
#print axioms no_two_universal_nonsingleton_shores
end Graffiti189LongestPath.ThresholdSix.ThreeCut
