import DetachedPair180
import AllTipsBase180
import LeafPatterns180

set_option warningAsError true
set_option compiler.extract_closed false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 4096
namespace Minimal180.DetachedExample
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180 PrivateCore
abbrev V := Fin 14
noncomputable def E : List (V×V) := [(0,9),(0,10),(1,9),(1,10),(2,9),(2,10),(3,4),(0,4),(3,5),(1,5),(2,5),(6,9),(6,7),(6,8),(1,7),(2,8),(9,11),(10,11),(4,11),(0,12),(1,12),(0,13),(3,13)]
noncomputable abbrev J := Case14.graph E
noncomputable abbrev G := Case14.graph ((3,0)::E)
noncomputable abbrev U : Finset V := {0,1,2,3,4,5,6,7,8,12,13}
noncomputable abbrev C : Finset V := {3,4,5,6,7,8,12,13}
noncomputable abbrev S : Finset V := univ\C
noncomputable abbrev A : Finset V := {4,5,7,8,12,13}
noncomputable abbrev P : Finset V := {0,1,2,3,6,11}
private noncomputable def depth (i : V) : ℕ := ([2, 2, 2, 2, 1, 3, 2, 3, 3, 1, 1, 0, 3, 3]:List ℕ)[i.val]!
theorem root_data : (J.Connected ∧ ∀ i,J.dist i 11=depth i) ∧
    (G.Connected ∧ ∀ i,G.dist i 11=depth i) := by
  constructor <;> apply layers <;> decide

theorem add_eq : J⊔SimpleGraph.edge 3 0=G := by
  ext a b
  change (J.Adj a b ∨ (SimpleGraph.edge 3 0).Adj a b) ↔ _
  rw [edge_adj]
  exact (show ∀ i j : V,(J.Adj i j ∨ ((i=3 ∧ j=0 ∨ i=0 ∧ j=3) ∧ i≠j)) ↔ G.Adj i j by decide) a b

private noncomputable def avoidD (c i:V) : ℕ := (([[88, 0, 2, 2, 3, 1, 2, 1, 3, 1, 1, 2, 1, 3], [2, 88, 0, 2, 3, 1, 2, 3, 1, 1, 1, 2, 3, 3], [1, 2, 88, 0, 1, 1, 3, 3, 4, 2, 2, 2, 2, 1], [1, 3, 3, 88, 0, 4, 3, 4, 4, 2, 2, 1, 2, 2], [2, 1, 1, 1, 88, 0, 3, 2, 2, 2, 2, 3, 2, 2], [2, 2, 2, 3, 3, 88, 0, 1, 1, 1, 3, 2, 3, 3], [3, 1, 3, 3, 4, 2, 88, 0, 4, 2, 2, 3, 2, 4], [3, 3, 1, 3, 4, 2, 1, 88, 0, 2, 2, 3, 4, 4], [1, 1, 1, 2, 2, 2, 1, 2, 88, 0, 2, 1, 2, 2], [1, 1, 1, 2, 2, 2, 3, 2, 2, 88, 0, 1, 2, 2], [2, 2, 2, 2, 1, 3, 2, 3, 3, 1, 88, 0, 3, 3], [1, 1, 3, 2, 2, 2, 3, 2, 4, 2, 2, 88, 0, 2], [1, 3, 3, 1, 2, 2, 3, 4, 4, 2, 2, 3, 88, 0], [0, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 88]]:List (List ℕ))[c.val]!)[i.val]!
theorem block : NoCut G := by apply noCut_of_routes G (fun c=>c+1) avoidD <;> decide
private noncomputable def coreRoot (z : V) : V := if z=0 then 1 else 0
private noncomputable def coreD (z i:V) : ℕ := (([[88, 0, 2, 88, 88, 88, 88, 88, 88, 1, 1, 2, 88, 88], [0, 88, 2, 88, 88, 88, 88, 88, 88, 1, 1, 2, 88, 88], [0, 2, 88, 88, 88, 88, 88, 88, 88, 1, 1, 2, 88, 88], [0, 2, 2, 88, 88, 88, 88, 88, 88, 1, 1, 2, 88, 88], [0, 2, 2, 88, 88, 88, 88, 88, 88, 1, 1, 2, 88, 88], [0, 2, 2, 88, 88, 88, 88, 88, 88, 1, 1, 2, 88, 88], [0, 2, 2, 88, 88, 88, 88, 88, 88, 1, 1, 2, 88, 88], [0, 2, 2, 88, 88, 88, 88, 88, 88, 1, 1, 2, 88, 88], [0, 2, 2, 88, 88, 88, 88, 88, 88, 1, 1, 2, 88, 88], [0, 2, 2, 88, 88, 88, 88, 88, 88, 88, 1, 2, 88, 88], [0, 2, 2, 88, 88, 88, 88, 88, 88, 1, 88, 2, 88, 88], [0, 2, 2, 88, 88, 88, 88, 88, 88, 1, 1, 88, 88, 88], [0, 2, 2, 88, 88, 88, 88, 88, 88, 1, 1, 2, 88, 88], [0, 2, 2, 88, 88, 88, 88, 88, 88, 1, 1, 2, 88, 88]]:List (List ℕ))[z.val]!)[i.val]!

theorem old_core_no_cut : 3≤S.card ∧ Con J S ∧ ∀ z∈S, Con J (S.erase z) := by
  refine ⟨by decide,Case14.con 0 (fun i => ([0, 2, 2, 88, 88, 88, 88, 88, 88, 1, 1, 2, 88, 88]:List ℕ)[i.val]!) (by decide) (by decide),?_⟩
  intro z hz
  apply Case14.con (coreRoot z) (coreD z)
  · exact (show ∀ a∈S,coreRoot a∈S.erase a by decide) z hz
  · exact (show ∀ a∈S,∀ v∈S.erase a,v≠coreRoot a → ∃ i∈S.erase a,J.Adj v i ∧ coreD a i<coreD a v by decide) z hz

theorem tip : NeedsTip J C S 3 0 := by
  refine ⟨by decide,by decide,old_core_no_cut.2.1,?_,?_⟩ <;> unfold Dominates <;> decide

theorem ranks : bipartiteNum J=14 ∧ bipartiteNum G=13 := by
  let Q : Finset V := {4,5,7,8,9,10,12,13}
  have cj : TwoColor J (P∪Q) := by
    refine ⟨P,Q,by decide,rfl,?_,?_⟩ <;> unfold Indep <;> decide
  have cg : TwoColor G (P.erase 3∪Q) := by
    refine ⟨P.erase 3,Q,by decide,rfl,?_,?_⟩ <;> unfold Indep <;> decide
  have lj := size_bip J cj
  have lg := size_bip G cg
  have nj : (P∪Q).card=14 := by decide
  have ng : (P.erase 3∪Q).card=13 := by decide
  obtain ⟨B,_,sb⟩ := optB J
  obtain ⟨T,col,st⟩ := optB G
  obtain ⟨a,_,out⟩ := Finset.not_subset.mp (triangle_excluded G T col 3 0 4 (by decide) (by decide) (by decide))
  have sub : T ⊂ univ := Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,fun h => out (h ▸ mem_univ a)⟩
  have lt := card_lt_card sub
  have le := card_le_univ B
  rw [card_univ,Fintype.card_fin] at lt
  rw [Fintype.card_fin] at le
  omega

theorem marks : Indep G A ∧ parity G 11 false=P ∧ eligible A P 11=U ∧
    G.dist 3 11=G.dist 0 11 ∧ (∀ i,J.dist i 11=G.dist i 11) := by
  refine ⟨?_,?_,?_,?_,fun i => (root_data.1.2 i).trans (root_data.2.2 i).symm⟩
  · unfold Indep; decide
  · ext i
    rw [mem_parity,root_data.2.2]
    exact (show ∀ j : V,depth j%2=false.toNat ↔ j∈P by decide) i
  · unfold eligible; decide
  · rw [root_data.2.2,root_data.2.2]; decide

#print axioms old_core_no_cut
#print axioms ranks
#print axioms marks
end Minimal180.DetachedExample
