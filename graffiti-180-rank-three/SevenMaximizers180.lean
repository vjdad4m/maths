import SevenObstruction180

set_option warningAsError true
set_option compiler.extract_closed false
namespace Minimal180.HigherRank.Seven
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180

theorem unique_maximum (B : Finset V) (ind : Indep G B) (mx : B.card=independence G) : B=A := by
  rw [ranks.1] at mx
  obtain ⟨a,b,c,ab,ac,bc,shape⟩ := card_eq_three.mp mx
  have am : a∈B := shape ▸ mem_insert_self _ _
  have bm : b∈B := shape ▸ mem_insert_of_mem (mem_insert_self _ _)
  have cm : c∈B := shape ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have eq := (show ∀ x y z : V,x≠y → x≠z → y≠z → ¬G.Adj x y → ¬G.Adj x z → ¬G.Adj y z →
    ({x,y,z}:Finset V)=A by decide) a b c ab ac bc (ind a am b bm ab) (ind a am c cm ac) (ind b bm c cm bc)
  exact shape.trans eq

noncomputable abbrev P6 : Finset V := {0,1,4,6}
noncomputable abbrev U6 : Finset V := {0,1,4,5,6}

theorem maximizing_roots (r : V) : evenCount G r=maxEven G ↔ r=5 ∨ r=6 := by
  have par : parity G r false=univ.filter (fun x : V => d r x%2=0) := by
    ext x; simp [mem_parity,(distances r).2]
  rw [even_equiv,par,data.2.2.2.2]
  exact (show ∀ j : V, (univ.filter (fun x : V => d j x%2=0)).card=4 ↔ j=5 ∨ j=6 by decide) r

theorem six_caps (T : SimpleGraph V) (sub : T≤G) (tr : T.IsTree) :
    (U6∩leaves T).card≤4 ∧ ((6:V)∉leaves T → (U6∩leaves T).card≤3) := by
  classical
  have miss : ∃ q∈({0,1,5}:Finset V),q∉leaves T := by
    by_cases h : (5:V)∈leaves T
    · obtain ⟨q,eq⟩ := exists_adj T tr.isConnected (by decide) 5
      have qIn := (show ∀ y : V,G.Adj 5 y → y∈({0,1,5}:Finset V) by decide) q (sub eq)
      exact ⟨q,qIn,fun qlf => leaves_nonadjacent T tr (by decide) eq h qlf⟩
    · exact ⟨5,by decide,h⟩
  obtain ⟨q,qc,notq⟩ := miss
  have remove : U6∩leaves T⊆U6.erase q := fun v hv =>
    mem_erase.mpr ⟨fun eq => notq (eq ▸ (mem_inter.mp hv).2),(mem_inter.mp hv).1⟩
  constructor
  · exact (card_le_card remove).trans ((show ∀ x∈({0,1,5}:Finset V),(U6.erase x).card≤4 by decide) q qc)
  · intro no
    have rem : U6∩leaves T⊆(U6.erase q).erase 6 := fun v hv =>
      mem_erase.mpr ⟨fun eq => no (eq ▸ (mem_inter.mp hv).2),remove hv⟩
    exact (card_le_card rem).trans ((show ∀ x∈({0,1,5}:Finset V),((U6.erase x).erase 6).card≤3 by decide) q qc)

noncomputable def p0 (x : V) : V := if x=6 then 2 else 0

theorem six_optimum : parity G 6 false=P6 ∧ eligible A P6 6=U6 ∧ weightedLeaves G U6=4 := by
  classical
  have par : parity G 6 false=univ.filter (fun x : V => d 6 x%2=0) := by
    ext x; simp [mem_parity,(distances 6).2]
  obtain ⟨T,sub,tr,_,lf⟩ := prescribed_leaf_witness 0 p0 {1,3,4,5,6} (by decide) (by decide)
  have low : ({1,4,5,6}:Finset V)⊆U6∩leaves T := fun x hx => mem_inter.mpr
    ⟨(show ({1,4,5,6}:Finset V)⊆U6 by decide) hx,lf ((show ({1,4,5,6}:Finset V)⊆{1,3,4,5,6} by decide) hx)⟩
  obtain ⟨M,mg,mt,eq⟩ := tree_opt G (distances 6).1 U6
  refine ⟨par.trans (by decide),by decide,le_antisymm (eq ▸ (six_caps M mg mt).1) ?_⟩
  exact (show 4≤({1,4,5,6}:Finset V).card by decide).trans ((card_le_card low).trans (score_of_tree G T sub tr U6))

/-- Neither changing the maximizing even root nor changing the maximum
independent set can yield an internal-root witness on this block. -/
theorem all_maximizing_markings (r : V) (B : Finset V) (root : evenCount G r=maxEven G)
    (ind : Indep G B) (top : B.card=independence G) :
    let Z := parity G r false
    let Q := eligible B Z r
    weightedLeaves G Q+bipartiteNum G=1+B.card+Z.card ∧
      ∀ T≤G,T.IsTree → r∉leaves T → (Q∩leaves T).card+bipartiteNum G<1+B.card+Z.card := by
  have same := unique_maximum B ind top
  subst B
  have ac : A.card=3 := by decide
  have b := ranks.2
  rcases (maximizing_roots r).mp root with eq|eq <;> subst r
  · intro Z Q
    have eqZ : Z=P := data.2.1
    have eqQ : Q=U := by change eligible A Z 5=U; rw [eqZ,data.2.2.1]
    rw [eqZ,eqQ,optima.1,ac,b]
    have pc : P.card=4 := by decide
    rw [pc]
    exact ⟨by decide,fun T sub tr nr => by have := (leaf_caps T sub tr).2 nr; omega⟩
  · intro Z Q
    have eqZ : Z=P6 := six_optimum.1
    have eqQ : Q=U6 := by change eligible A Z 6=U6; rw [eqZ,six_optimum.2.1]
    rw [eqZ,eqQ,six_optimum.2.2,ac,b]
    have pc : P6.card=4 := by decide
    rw [pc]
    exact ⟨by decide,fun T sub tr nr => by have := (six_caps T sub tr).2 nr; omega⟩

#print axioms unique_maximum
#print axioms maximizing_roots
#print axioms six_caps
#print axioms six_optimum
#print axioms all_maximizing_markings
end Minimal180.HigherRank.Seven
