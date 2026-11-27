import PrivateSuccessors180

set_option warningAsError true
namespace Minimal180.PortParity
open Finset SimpleGraph Graffiti177 Graffiti318 Graffiti180 Rooted180 Converse180 Assembly180 HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At a borderline failure the private-successor conflict is nonvacuous.
A total choice function is used only for convenience outside the marked
odd vertices. -/
theorem private_choices (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V)
    (rk : Fintype.card V≤bipartiteNum G+secondDegree G+1)
    (bad : maxLeaves G+bipartiteNum G<1+independence G+evenCount G r)
    (A : Finset V) :
    ∃ f : V→V,∀ q∈oddSet G r∩A,Arc G r q (f q) := by
  classical
  have child (q : V) (qm : q∈oddSet G r∩A) : ∃ y,Arc G r q y := by
    have odd : q∉parity G r false := by
      have qo := (mem_inter.mp qm).1
      simpa only [oddSet,mem_filter,mem_univ,true_and,mem_parity,Bool.toNat_false] using qo
    exact (borderline_odd_vertex G gc hn r rk bad q odd).2.1
  exact ⟨fun q => if h : q∈oddSet G r∩A then (child q h).choose else r,
    fun q qm => by simpa only [dif_pos qm] using (child q qm).choose_spec⟩

/-- Ordinary Graffiti.pc 180 if a maximizing root and a maximum
independent set can be chosen so that its odd members all lie in one
singleton, and that member has maximum odd depth. The set may contain
no odd vertex. This includes the remaining rank-three branch with
second-smallest degree two. -/
theorem conjecture180_last_odd (G : SimpleGraph V) [DecidableRel G.Adj] (gc : G.Connected)
    (hn : 1<Fintype.card V) (r : V) (mx : evenCount G r=maxEven G)
    (rk : Fintype.card V≤bipartiteNum G+secondDegree G+1)
    (A : Finset V) (ai : Indep G A) (am : A.card=independence G) (z : V)
    (single : oddSet G r∩A⊆{z}) (last : ∀ u∈oddSet G r,G.dist u r≤G.dist z r) :
    1+independence G+maxEven G≤maxLeaves G+bipartiteNum G := by
  classical
  rw [←mx]
  by_contra! bad
  obtain ⟨f,child⟩ := private_choices G gc hn r rk bad A
  rcases private_conflict G gc hn r rk bad A ai am f child with pair|step
  · obtain ⟨q,qm,t,tm,edge⟩ := pair
    have qz := mem_singleton.mp (single qm)
    have tz := mem_singleton.mp (single tm)
    exact edge.ne (congrArg f (qz.trans tz.symm))
  · obtain ⟨q,qm,w,wm,_,depth⟩ := step
    have out := (child q qm).2.1
    have high := last w (mem_sdiff.mp wm).1
    have qz := mem_singleton.mp (single qm)
    rw [←qz] at high
    omega

#print axioms private_choices
#print axioms conjecture180_last_odd
end Minimal180.PortParity
