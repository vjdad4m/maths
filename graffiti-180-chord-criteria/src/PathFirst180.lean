import BranchFirst180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Both edges incident to each tip can coexist with the whole root star
when the root and its neighbors avoid the four path vertices other than the middle. -/
private theorem path_with_star (H : SimpleGraph V) (conn : H.Connected) (r a u w v b : V)
    (ab : a≠b) (au : H.Adj a u) (uw : H.Adj u w) (vw : H.Adj v w) (bv : H.Adj b v)
    (sep : ∀ x∈({a,b}:Finset V), x∉({u,v,w}:Finset V))
    (away : ∀ x∈({a,b,u,v}:Finset V), x≠r ∧ ¬H.Adj r x) :
    ∃ T≤H, T.IsTree ∧ T.Adj a u ∧ T.Adj u w ∧ T.Adj v w ∧ T.Adj b v ∧
      ∀ z, H.Adj r z → T.Adj r z := by
  classical
  have an := sep a (by simp)
  have bn := sep b (by simp)
  simp only [mem_insert,mem_singleton,not_or] at an bn
  let p (x:V) := if x=a then u else if x=b then v else if x=u ∨ x=v then w else r
  let d (x:V) := if x=r then 0 else if x=a ∨ x=b then 3 else if x=u ∨ x=v then 2 else 1
  have ar := (away a (by simp)).1
  have br := (away b (by simp)).1
  have ur := (away u (by simp)).1
  have vr := (away v (by simp)).1
  have down (x:V) (xr:x≠r) : d (p x)<d x := by
    by_cases xa : x=a
    · subst x; simp [p,d,ur,ar,Ne.symm an.1,Ne.symm bn.1]
    by_cases xb : x=b
    · subst x; simp [p,d,vr,br,Ne.symm an.2.1,Ne.symm bn.2.1,ab.symm]
    by_cases tip : x=u ∨ x=v
    · by_cases wr : w=r <;> simp [p,d,wr,xr,xa,xb,tip,Ne.symm an.2.2,Ne.symm bn.2.2,uw.ne.symm,vw.ne.symm]
    · simp [p,d,xr,xa,xb,tip]
  obtain ⟨K,kt,edges⟩ := virtual_tree r p d down
  obtain ⟨T,sub,tr,keep⟩ := keep_target H K conn kt
  refine ⟨T,sub,tr,keep ⟨au,by simpa [p] using edges a ar⟩,
    keep ⟨uw,by simpa [p,Ne.symm an.1,Ne.symm bn.1] using edges u ur⟩,
    keep ⟨vw,by simpa [p,Ne.symm an.2.1,Ne.symm bn.2.1] using edges v vr⟩,
    keep ⟨bv,by simpa [p,ab.symm] using edges b br⟩,?_⟩
  intro z rz
  have out : z∉({a,b,u,v}:Finset V) := fun h => (away z h).2 rz
  simp only [mem_insert,mem_singleton,not_or] at out
  exact keep ⟨rz,(show K.Adj z r by simpa [p,out.1,out.2.1,out.2.2.1,out.2.2.2] using edges z rz.ne.symm).symm⟩

private theorem two_deg (T : SimpleGraph V) [DecidableRel T.Adj] {x a b:V}
    (ea : T.Adj x a) (eb : T.Adj x b) (ab : a≠b) : 2≤T.degree x := by
  have h : ({a,b}:Finset V)⊆T.neighborFinset x := by
    intro z hz
    rcases (show z=a ∨ z=b by simpa using hz) with rfl|rfl
    · exact (T.mem_neighborFinset ..).mpr ea
    · exact (T.mem_neighborFinset ..).mpr eb
  simpa only [card_pair ab,card_neighborFinset_eq_degree] using card_le_card h

/-- A five-vertex alternating path through both tips forces a two-component
certificate under lower tightness when the root degree can pay the deficit.
The path and root hypotheses only involve old graph incidences. -/
theorem first_on_separated_path (J : SimpleGraph V) [DecidableRel J.Adj]
    (jc : J.Connected) (hn : 3<Fintype.card V) (r a u w v b : V) (odd : Bool) (A : Finset V)
    (ai : Indep J A) (ne : A≠parity J r odd) (uv : u≠v) (ab : a≠b) (old : ¬J.Adj u v)
    (au : (alternating J (parity J r odd)).Adj a u) (uw : (alternating J (parity J r odd)).Adj u w)
    (vw : (alternating J (parity J r odd)).Adj v w) (bv : (alternating J (parity J r odd)).Adj b v)
    (sep : ∀ x∈({a,b}:Finset V), x∉({u,v,w}:Finset V))
    (away : ∀ x∈({a,b,u,v}:Finset V), x≠r ∧ ¬J.Adj r x)
    (root : 2≤J.degree r) (wr : w≠r)
    (budget : Fintype.card V≤bipartiteNum J+1 ∨
      (r∈A∪parity J r odd ∧ Fintype.card V+1≤bipartiteNum J+J.degree r))
    (middle : w∈eligible A (parity J r odd) r ∨ (u∉A∩parity J r odd ∧ v∉A∩parity J r odd))
    (tight : weightedLeaves J (eligible A (parity J r odd) r)+bipartiteNum J=1+A.card+(parity J r odd).card) :
    FirstForm J (eligible A (parity J r odd) r) u v w := by
  classical
  let P := parity J r odd
  let H := alternating J P
  obtain ⟨conn,star⟩ := alternating_parity J jc r odd
  obtain ⟨T,sub,tr,ta,tu,tv,tb,keep⟩ := path_with_star H conn r a u w v b ab au uw vw bv sep
    (fun x h => ⟨(away x h).1,fun e => (away x h).2 e.1⟩)
  have count : J.degree r≤T.degree r := by
    rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
    exact card_le_card (fun x h => (T.mem_neighborFinset ..).mpr (keep x (star x ((J.mem_neighborFinset ..).mp h))))
  have an := sep a (by simp)
  have bn := sep b (by simp)
  simp only [mem_insert,mem_singleton,not_or] at an bn
  have tips (x : V) (h : x∈({u,v}:Finset V)) : 2≤T.degree x := by
    rcases (show x=u ∨ x=v by simpa using h) with rfl|rfl
    · exact two_deg T ta.symm tu an.2.2
    · exact two_deg T tb.symm tv bn.2.2
  have use (B : Finset V) (bx : B⊆A∪P) (wb : w∉B)
      (size : Fintype.card V+2*B.card≤bipartiteNum J+1+∑ x∈B,T.degree x) :
      FirstForm J (eligible A P r) u v w :=
    first_of_branch_forest J T jc hn r u v w uv old odd A B ai ne bx wb sub tr.IsAcyclic
      tu tv (root.trans count) (fun x h _ => tips x h) (middle.imp_right (fun h => ⟨wr,h⟩)) tight size
  rcases budget with low|⟨rm,high⟩
  · exact use ∅ (empty_subset _) (by simp) (by simpa using low)
  · apply use {r} (singleton_subset_iff.mpr rm) (by simpa using wr)
    simp only [card_singleton,Nat.mul_one,sum_singleton]
    omega

#print axioms first_on_separated_path
end Minimal180
