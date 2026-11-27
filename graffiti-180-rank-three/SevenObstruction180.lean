import SevenData180
import ParentFiber180

set_option warningAsError true
set_option compiler.extract_closed false
namespace Minimal180.HigherRank.Seven
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180

/-- At least one of 2, 3 and 6 must be internal in every spanning tree. -/
theorem missing_leaf (T : SimpleGraph V) (sub : T≤G) (tr : T.IsTree) :
    ∃ q∈({2,3,6}:Finset V),q∉leaves T := by
  classical
  by_cases h : (6:V)∈leaves T
  · obtain ⟨q,eq⟩ := exists_adj T tr.isConnected (by decide) 6
    have qIn := (show ∀ y : V,G.Adj 6 y → y∈({2,3,6}:Finset V) by decide) q (sub eq)
    exact ⟨q,qIn,fun qlf => leaves_nonadjacent T tr (by decide) eq h qlf⟩
  · exact ⟨6,by decide,h⟩

theorem leaf_caps (T : SimpleGraph V) (sub : T≤G) (tr : T.IsTree) :
    (U∩leaves T).card≤4 ∧ ((5:V)∉leaves T → (U∩leaves T).card≤3) := by
  obtain ⟨q,qc,notq⟩ := missing_leaf T sub tr
  have remove : U∩leaves T⊆U.erase q := fun v hv =>
    mem_erase.mpr ⟨fun eq => notq (eq ▸ (mem_inter.mp hv).2),(mem_inter.mp hv).1⟩
  constructor
  · exact (card_le_card remove).trans ((show ∀ x∈({2,3,6}:Finset V),(U.erase x).card≤4 by decide) q qc)
  · intro no
    have rem : U∩leaves T⊆(U.erase q).erase 5 := fun v hv =>
      mem_erase.mpr ⟨fun eq => no (eq ▸ (mem_inter.mp hv).2),remove hv⟩
    exact (card_le_card rem).trans ((show ∀ x∈({2,3,6}:Finset V),((U.erase x).erase 5).card≤3 by decide) q qc)

theorem prescribed_leaf_witness (r : V) (p : V→V) (S : Finset V)
    (ok : ∀ x≠r,G.Adj x (p x) ∧ d r x=d r (p x)+1)
    (zero : ∀ v∈S,v≠r ∧ ((univ.erase r).filter (fun x => p x=v)).card=0) :
    ∃ T≤G,T.IsTree ∧ (∀ x,T.dist x r=G.dist x r) ∧ S⊆leaves T := by
  classical
  have pred (x : V) (xr : x≠r) : G.Adj x (p x) ∧ G.dist x r=G.dist (p x) r+1 := by
    refine ⟨(ok x xr).1,?_⟩
    rw [(distances r).2,(distances r).2,(ok x xr).2]
  obtain ⟨T,sub,tr,_,take,_⟩ := predecessor_tree G (distances r).1 r false p pred
  have depth := layers T r (d r) ((show ∀ z : V,d z z=0 by decide) r)
    (fun {x y} e => (show ∀ i j k : V,G.Adj j k → d i j≤d i k+1 by decide) r x y (sub e))
    (fun x xr => ⟨p x,take x xr,(ok x xr).2⟩)
  refine ⟨T,sub,tr,fun x => (depth.2 x).trans ((distances r).2 x).symm,?_⟩
  intro v vs
  obtain ⟨vr,z⟩ := zero v vs
  have down (x : V) (xr : x≠r) : d r (p x)<d r x := by rw [(ok x xr).2]; omega
  have deg := parent_neighbors T tr r p (d r) down take v vr
  rw [z] at deg
  have eq : v∈leaves T ↔ T.degree v=1 := by simp [leaves,SimpleGraph.degree,SimpleGraph.neighborFinset]
  exact eq.mpr deg

noncomputable def p2 (x : V) : V := if x=5 then 0 else 2
noncomputable def p5 (x : V) : V := ([5,5,0,0,0,5,2]:List V)[x.val]!

theorem optima : weightedLeaves G U=4 ∧
    (∃ T≤G,T.IsTree ∧ (∀ x,T.dist x 5=G.dist x 5) ∧ (U∩leaves T).card=3) ∧
    (∀ T≤G,T.IsTree → (5:V)∉leaves T → (U∩leaves T).card≤3) ∧ 5≤maxLeaves G := by
  classical
  obtain ⟨T,sub,tr,_,lf⟩ := prescribed_leaf_witness 2 p2 {1,3,4,5,6} (by decide) (by decide)
  have low : ({3,4,5,6}:Finset V)⊆U∩leaves T := fun x hx => mem_inter.mpr
    ⟨(show ({3,4,5,6}:Finset V)⊆U by decide) hx,lf ((show ({3,4,5,6}:Finset V)⊆{1,3,4,5,6} by decide) hx)⟩
  have four : 4≤(U∩leaves T).card := (show 4≤({3,4,5,6}:Finset V).card by decide).trans (card_le_card low)
  have maxw : (U∩leaves T).card≤weightedLeaves G U :=
    score_of_tree G T sub tr U
  have maxT : (leaves T).card≤maxLeaves G := by
    simpa only [univ_inter,weighted_all] using score_of_tree G T sub tr univ
  obtain ⟨J,jg,jt,dist,jl⟩ := prescribed_leaf_witness 5 p5 {3,4,6} (by decide) (by decide)
  have root : (5:V)∉leaves J := by
    intro m
    have eq (x : V) (a : G.Adj 5 x) : J.Adj 5 x := by
      apply dist_eq_one_iff_adj.mp
      rw [dist_comm,dist,dist_eq_one_iff_adj.mpr a.symm]
    exact (show (0:V)≠1 by decide) (leaf_unique J m (eq 0 (by decide)) (eq 1 (by decide)))
  have hits : ({3,4,6}:Finset V)⊆U∩leaves J := fun x hx =>
    mem_inter.mpr ⟨(show ({3,4,6}:Finset V)⊆U by decide) hx,jl hx⟩
  have three : 3≤(U∩leaves J).card := (show 3≤({3,4,6}:Finset V).card by decide).trans (card_le_card hits)
  refine ⟨le_antisymm ?_ (four.trans maxw),⟨J,jg,jt,dist,le_antisymm ((leaf_caps J jg jt).2 root) three⟩,
    fun M mg mt => (leaf_caps M mg mt).2,?_⟩
  · obtain ⟨M,mg,mt,eq⟩ := tree_opt G (distances 5).1 U
    rw [←eq]; exact (leaf_caps M mg mt).1
  · exact (show 5≤({1,3,4,5,6}:Finset V).card by decide).trans ((card_le_card lf).trans maxT)

/-- This genuine rank-three block has a maximizing even root and maximum
independent marking. Every tree witnessing their rooted inequality must
make the root a leaf. The ordinary conjecture holds for the example. -/
theorem internal_root_obstruction :
    G.Connected ∧ NoCut G ∧ Fintype.card V=bipartiteNum G+3 ∧
    Indep G A ∧ A.card=independence G ∧ parity G 5 false=P ∧ evenCount G 5=maxEven G ∧
    eligible A P 5=U ∧ weightedLeaves G U+bipartiteNum G=1+A.card+P.card ∧
    (∀ T≤G,T.IsTree → (5:V)∉leaves T → (U∩leaves T).card+bipartiteNum G<1+A.card+P.card) ∧
    1+independence G+maxEven G≤maxLeaves G+bipartiteNum G := by
  have ⟨i,p,u,e,m⟩ := data
  have ⟨alpha,b⟩ := ranks
  have ⟨w,_,no,ell⟩ := optima
  have a : A.card=3 := by decide
  have v : P.card=4 := by decide
  exact ⟨(distances 5).1,block,by rw [b]; decide,i,a.trans alpha.symm,p,e.trans m.symm,u,
    by omega,fun T sub tr nr => by have := no T sub tr nr; omega,by omega⟩

#print axioms prescribed_leaf_witness
#print axioms missing_leaf
#print axioms leaf_caps
#print axioms optima
#print axioms internal_root_obstruction
end Minimal180.HigherRank.Seven
