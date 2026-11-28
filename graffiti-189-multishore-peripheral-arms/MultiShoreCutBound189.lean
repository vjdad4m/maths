import SmallSeparator189
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
open Finset SimpleGraph Graffiti189LongestPath
open scoped BigOperators
open private Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two
  Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
set_option maxHeartbeats 10000000
namespace Graffiti189LongestPath.MultiShoreCutBound
variable {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Double-count the disjoint distance-two expenditure at a cut vertex,
and at one high-degree neighbor in every shore. -/
theorem multishore_budget (hc : G.Connected) (d : Nat)
    (cap : ∀ v,(DistanceTwo G v).card≤d) (k : Nat) (M : α→Finset V)
    (pair : Pairwise (fun i j => Disjoint (M i) (M j)))
    (no : ∀ i j,i≠j → ∀ u∈M i,∀ v∈M j,¬G.Adj u v)
    (s : V) (ss : ∀ i,s∉M i)
    (reaches : ∀ i,∃ u∈M i,G.Adj s u ∧ d≤G.degree u ∧
      ((G.neighborFinset u)\M i).card≤k)
    (q2 : 2≤Fintype.card α) :
    let q := (Fintype.card α:ℤ)
    ((q-1)^2-q)*(d:ℤ)+q*(q-1)≤q*(q-1)*(k:ℤ) := by
  classical
  choose u um su ud extC using reaches
  let N (i : α) := (M i).filter (G.Adj s)
  let H (i : α) := ((M i).filter (G.Adj (u i)))\N i
  let c := Fintype.card α
  let a := ∑ i,(N i).card
  let b := ∑ i,(H i).card
  have ns (i : α) : N i⊆M i := filter_subset _ _
  have hs (i : α) : H i⊆M i := fun _ z => (mem_filter.mp (mem_sdiff.mp z).1).1
  have nh (i : α) : u i∈N i := mem_filter.mpr ⟨um i,su i⟩
  have inD (i : α) : H i⊆DistanceTwo G s := by
    intro z hz
    obtain ⟨hu,hn⟩ := mem_sdiff.mp hz
    obtain ⟨zm,uz⟩ := mem_filter.mp hu
    have sz : s≠z := fun e => ss i (e.symm ▸ zm)
    have na : ¬G.Adj s z := fun e => hn (mem_filter.mpr ⟨zm,e⟩)
    exact Graffiti189LongestPath.mem_distanceTwo.mpr
      (Graffiti189LongestPath.dist_two hc sz na (su i) uz)
  have hdis : Set.PairwiseDisjoint (↑(univ:Finset α):Set α) H := by
    intro i _ j _ ne
    exact disjoint_left.mpr (fun _ a z => disjoint_left.mp (pair ne) (hs i a) (hs j z))
  have hb : b≤d := by
    have t : (univ:Finset α).biUnion H⊆DistanceTwo G s := by
      intro z zH
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp zH
      exact inD i hi
    have r := (card_le_card t).trans (cap s)
    rw [card_biUnion hdis] at r
    exact r
  have side (i : α) : d+1≤k+(N i).card+(H i).card := by
    let E := G.neighborFinset (u i)\M i
    have sub : G.neighborFinset (u i)⊆E∪(N i).erase (u i)∪H i := by
      intro z zz
      have ed := (G.mem_neighborFinset _ _).mp zz
      by_cases zi : z∈M i
      · by_cases sz : G.Adj s z
        · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr
            (mem_erase.mpr ⟨ed.ne.symm,mem_filter.mpr ⟨zi,sz⟩⟩))))
        · exact mem_union.mpr (Or.inr (mem_sdiff.mpr
            ⟨mem_filter.mpr ⟨zi,ed⟩,fun e => sz (mem_filter.mp e).2⟩))
      · exact mem_union.mpr (Or.inl (mem_union.mpr
          (Or.inl (mem_sdiff.mpr ⟨zz,zi⟩))))
    have cl := card_le_card sub
    rw [G.card_neighborFinset_eq_degree] at cl
    have cu := card_union_le E ((N i).erase (u i))
    have ch := card_union_le (E∪(N i).erase (u i)) (H i)
    have ec : E.card≤k := extC i
    have er := card_erase_add_one (nh i)
    have lo := ud i
    omega
  have const (n : Nat) : (∑ _i : α,n)=c*n := by
    have z := Finset.sum_const_nat (s:=(univ:Finset α)) (m:=n)
      (f:=fun _ => n) (fun _ _ => rfl)
    simpa only [card_univ] using z
  have lower : c*(d+1)≤c*k+a+d := by
    have z := Finset.sum_le_sum (s:=univ) (f:=fun _ : α => d+1)
      (g:=fun i => k+(N i).card+(H i).card) (fun i _ => side i)
    rw [const,Finset.sum_add_distrib,Finset.sum_add_distrib,const] at z
    change c*(d+1)≤c*k+a+b at z
    omega
  have other (i : α) : a≤d+(N i).card := by
    let Q := (univ:Finset α).erase i
    have dis : Set.PairwiseDisjoint (↑Q:Set α) N := by
      intro j _ k _ ne
      exact disjoint_left.mpr (fun _ jn kn => disjoint_left.mp (pair ne) (ns j jn) (ns k kn))
    have sub : Q.biUnion N⊆DistanceTwo G (u i) := by
      intro z zz
      obtain ⟨j,jq,zn⟩ := mem_biUnion.mp zz
      have ne := (mem_erase.mp jq).1.symm
      have zr := ns j zn
      have uz : u i≠z := fun e => disjoint_left.mp (pair ne) (um i) (e.symm ▸ zr)
      exact Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc uz (no i j ne _ (um i) z zr)
          (su i).symm (mem_filter.mp zn).2)
    have r := (card_le_card sub).trans (cap (u i))
    rw [card_biUnion dis] at r
    have eq : (∑ j∈Q,(N j).card)+(N i).card=a :=
      Finset.sum_erase_add _ _ (mem_univ i)
    omega
  have upper : c*a≤c*d+a := by
    have z := Finset.sum_le_sum (s:=univ) (f:=fun _ : α => a) (g:=fun i => d+(N i).card)
      (fun i _ => other i)
    rw [const,Finset.sum_add_distrib,const] at z
    exact z
  have l : (c:ℤ)*((d:ℤ)+1)≤(c:ℤ)*(k:ℤ)+(a:ℤ)+(d:ℤ) := by exact_mod_cast lower
  have u' : (c:ℤ)*(a:ℤ)≤(c:ℤ)*(d:ℤ)+(a:ℤ) := by exact_mod_cast upper
  have x := mul_nonneg (show 0≤(c:ℤ)-1 by dsimp [c]; omega)
    (show 0≤(c:ℤ)*(k:ℤ)+(a:ℤ)+(d:ℤ)-(c:ℤ)*((d:ℤ)+1) by omega)
  change (((c:ℤ)-1)^2-(c:ℤ))*(d:ℤ)+(c:ℤ)*((c:ℤ)-1)
    ≤(c:ℤ)*((c:ℤ)-1)*(k:ℤ)
  nlinarith only [x,u']

/-- The same bound for the shores of a minimum separator. -/
theorem degree_le_of_minimum_cut_with_many_nontrivial_shores
    (hc : G.Connected) (k d : Nat) (hk : 2≤k)
    (conn : ∀ D : Finset V,D.card<k → (G.induce ((↑D:Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v)
    (cap : ∀ v,(DistanceTwo G v).card≤d) (S : Finset V) (M : α→Finset V)
    (sc : S.card=k) (prt : (univ:Finset V)=(univ.biUnion M)∪S)
    (pair : Pairwise (fun i j => Disjoint (M i) (M j)))
    (ms : ∀ i,Disjoint (M i) S)
    (no : ∀ i j,i≠j → ∀ u∈M i,∀ v∈M j,¬G.Adj u v)
    (sz : ∀ i,1<(M i).card) (q2 : 2≤Fintype.card α) :
    let q := (Fintype.card α:ℤ)
    ((q-1)^2-q)*(d:ℤ)+q*(q-1)≤q*(q-1)*(k:ℤ) := by
  classical
  have other (i : α) : ∃ j : α, i≠j := by
    by_contra! h
    have aux : (univ : Finset α) ⊆ {i} := fun j _ => mem_singleton.mpr (h j).symm
    have c := card_le_card aux
    simp at c
    omega
  have neM (i : α) : (M i).Nonempty := card_pos.mp (by have := sz i; omega)
  have loc (v : V) : (∃ i,v∈M i) ∨ v∈S := by
    have z : v∈(univ.biUnion M)∪S := prt ▸ mem_univ v
    exact (mem_union.mp z).imp (fun z => by
      obtain ⟨i,_,zi⟩ := mem_biUnion.mp z; exact ⟨i,zi⟩) id
  have reach (i : α) (s : V) (ss : s∈S) : ∃ u∈M i,G.Adj s u := by
    by_contra bad
    obtain ⟨x,xi⟩ := neM i
    obtain ⟨j,ij⟩ := other i
    obtain ⟨y,yj⟩ := neM j
    have cl (u : V) (ui : u∈M i) (v : V) (vi : v∉M i) (uv : G.Adj u v) :
        v∈S.erase s := by
      rcases loc v with ⟨j,vj⟩|vs
      · exact (no i j (fun h => vi (h.symm ▸ vj)) u ui v vj uv).elim
      · exact mem_erase.mpr ⟨fun e => bad ⟨u,ui,e ▸ uv.symm⟩,vs⟩
    have ksmall := Graffiti189LongestPath.boundary_card_of_connectivity k conn xi
      (fun h => disjoint_left.mp (pair ij) h yj)
      (fun h => disjoint_left.mp (ms j) yj (mem_erase.mp h).2)
      (disjoint_left.mpr (fun _ zr zs => disjoint_left.mp (ms i) zr (mem_erase.mp zs).2)) cl
    have h := card_erase_add_one ss
    omega
  have result : ∃ s∈S,∀ i,∃ u∈M i,G.Adj s u ∧ d≤G.degree u := by
    by_cases someLow : ∃ i,∃ x∈M i,G.degree x<d
    · obtain ⟨i,x,xi,xl⟩ := someLow
      have high (u : V) (ux : u≠x) := (deg u x ux).resolve_right (Nat.not_le_of_lt xl)
      have reachHigh : ∃ s∈S,∃ u∈M i,G.Adj s u ∧ d≤G.degree u := by
        by_contra none
        have er := card_erase_add_one xi
        obtain ⟨u,ui⟩ := card_pos.mp (show 0<(M i |>.erase x).card from by have := sz i; omega)
        obtain ⟨j,ij⟩ := other i
        obtain ⟨v,vj⟩ := neM j
        have vr : v∉M i := fun h => disjoint_left.mp (pair ij) h vj
        have cl (a : V) (ar : a∈(M i).erase x) (b : V) (br : b∉(M i).erase x) (ab : G.Adj a b) :
            b∈({x}:Finset V) := by
          obtain ⟨ax,ai⟩ := mem_erase.mp ar
          rcases loc b with ⟨r,rb⟩|bs
          · by_cases e : i=r
            · exact mem_singleton.mpr (Classical.byContradiction
                (fun h => br (mem_erase.mpr ⟨h,e.symm ▸ rb⟩)))
            · exact (no i r e a ai b rb ab).elim
          · exact (none ⟨b,bs,a,ai,ab.symm,high a ax⟩).elim
        have small := Graffiti189LongestPath.boundary_card_of_connectivity k conn ui
          (fun h => vr (mem_erase.mp h).2)
          (fun h => vr ((mem_singleton.mp h).symm ▸ xi))
          (disjoint_left.mpr (fun _ zr zx => (mem_erase.mp zr).1 (mem_singleton.mp zx))) cl
        simp at small
        omega
      obtain ⟨s,ss,hs⟩ := reachHigh
      refine ⟨s,ss,?_⟩
      intro j
      by_cases h : i=j
      · exact h ▸ hs
      · obtain ⟨u,uj,su⟩ := reach j s ss
        exact ⟨u,uj,su,high u (fun e => disjoint_left.mp (pair h) xi (e ▸ uj))⟩
    · obtain ⟨s,ss⟩ := card_pos.mp (show 0<S.card from by omega)
      refine ⟨s,ss,?_⟩
      intro i
      obtain ⟨u,ui,su⟩ := reach i s ss
      exact ⟨u,ui,su,Nat.le_of_not_gt (fun hl => someLow ⟨i,u,ui,hl⟩)⟩
  obtain ⟨s,ss,rs⟩ := result
  subst k
  apply multishore_budget hc d cap S.card M pair no s
    (fun i h => disjoint_left.mp (ms i) h ss) _ q2
  intro i
  obtain ⟨u,ui,su,ud⟩ := rs i
  exact ⟨u,ui,su,ud,card_le_card (fun v hv => by
    obtain ⟨uv,nmi⟩ := mem_sdiff.mp hv
    rcases loc v with ⟨j,vj⟩|vs
    · exact (no i j (fun e => nmi (e.symm ▸ vj)) u ui v vj
        ((G.mem_neighborFinset _ _).mp uv)).elim
    · exact vs)⟩

/-- Below half the second-degree threshold there cannot be five such shores. -/
theorem at_most_four_shores_below_half (k d q : ℕ) (small : 2*k≤d)
    (a : (((q:ℤ)-1)^2-(q:ℤ))*(d:ℤ)+(q:ℤ)*((q:ℤ)-1)
      ≤(q:ℤ)*((q:ℤ)-1)*(k:ℤ)) : q≤4 := by
  by_contra! h
  have q5 : (5:ℤ)≤q := by exact_mod_cast h
  have q1 : 0≤(q:ℤ)-1 := by omega
  have qp : 0≤(q:ℤ) := by omega
  have qd : 0≤(d:ℤ) := by omega
  have qk : 0≤(d:ℤ)-2*(k:ℤ) := by omega
  have mass := mul_nonneg (mul_nonneg qp q1) qk
  have positive := mul_pos (show (0:ℤ)<q by omega) (show (0:ℤ)<(q:ℤ)-1 by omega)
  have extra := mul_nonneg (mul_nonneg qp (show 0≤(q:ℤ)-5 by omega)) qd
  nlinarith only [a,mass,positive,extra,qd]

#print axioms degree_le_of_minimum_cut_with_many_nontrivial_shores
#print axioms at_most_four_shores_below_half
end Graffiti189LongestPath.MultiShoreCutBound
