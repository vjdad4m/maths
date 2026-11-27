import OneHorizontal180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Transversals HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A horizontal edge outside both marks adds one to the full singly
marked layer bound, at every nonroot layer containing a double mark. -/
theorem layer_bonus (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (r a : V) (ar : a≠r) (p : Bool) (A : Finset V) (ai : Indep G A) (am : a∈A) (ap : a∈parity G r p)
    (u v : V) (ed : G.Adj u v) (uo : u∉A∪parity G r p) (vo : v∉A∪parity G r p) :
    (((A∪parity G r p)\(A∩parity G r p)).filter (fun x => G.dist x r=G.dist a r)).card+1≤
      allowance G r p A := by
  classical
  let P := parity G r p
  let X := A∪P
  let D := X\(A∩P)
  let d (x : V) := G.dist x r
  let C := D.filter (fun x => d x<d a)
  let Y := D.filter (fun x => d x=d a)
  have up : u∉P := fun m => uo (mem_union_right _ m)
  have vp : v∉P := fun m => vo (mem_union_right _ m)
  have deq : d u=d v := eq_dist G gc r u v p ed (iff_of_false up vp)
  have ur : u≠r := by
    intro eq;subst u
    have pos := gc.pos_dist_of_ne ed.ne.symm
    change G.dist r r=G.dist v r at deq;rw [dist_self] at deq;omega
  let par x := if h : x=r then r else (Graffiti169.exists_predecessor G gc r x h).choose
  have spec (x : V) (xr : x≠r) : G.Adj x (par x) ∧ d x=d (par x)+1 := by
    simpa [d,par,xr] using (Graffiti169.exists_predecessor G gc r x xr).choose_spec
  let q x := if x=u then v else par x
  let k x := 2*d x+(if x=u then 1 else 0)
  have step (x : V) (xr : x≠r) : G.Adj x (q x) ∧ k (q x)<k x ∧ d (q x)≤d x := by
    by_cases xu : x=u
    · subst x;simp [q,k,ed.ne.symm,deq,ed]
    · obtain ⟨ex,dx⟩ := spec x xr
      simp only [q,if_neg xu,k]
      refine ⟨ex,?_,by omega⟩
      split_ifs <;> omega
  have down (x : V) (xr : x≠r) := (step x xr).2.1
  obtain ⟨T,tree,take⟩ := virtual_tree r q k down
  have image := parent_image T tree r q k down take
  have orient {x y : V} (e : T.Adj x y) : ∃ z,z≠r ∧ s(z,q z)=s(x,y) := by
    have m : s(x,y)∈T.edgeFinset := mem_edgeFinset.mpr e
    rw [←image] at m
    obtain ⟨z,zm,eq⟩ := mem_image.mp m
    exact ⟨z,(mem_erase.mp zm).1,eq⟩
  have sub : T≤G := by
    intro x y e
    obtain ⟨z,zr,s⟩ := orient e
    have good := (step z zr).1
    rcases Sym2.eq_iff.mp s with ⟨h,j⟩|⟨h,j⟩
    · exact h ▸ j ▸ good
    · exact h ▸ j ▸ good.symm
  have cross {x y : V} (e : T.Adj x y) (ne : s(x,y)≠s(u,v)) : x∈P ↔ y∉P := by
    obtain ⟨z,zr,s⟩ := orient e
    have zu : z≠u := by intro eq;subst z;exact ne (by simpa [q] using s.symm)
    have dv := (spec z zr).2
    have qv : q z=par z := if_neg zu
    rw [←qv] at dv
    rcases Sym2.eq_iff.mp s with ⟨h,j⟩|⟨h,j⟩ <;> rw [j,h] at dv <;>
      simp only [P,mem_parity] <;> dsimp [d] at dv <;> cases p <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega
  have edge : T.Adj u v := by simpa [q] using take u ur
  have monot (x : V) (xd : x∈D) (xr : x≠r) : d x=d (q x)+1 := by
    have xu : x≠u := fun eq => uo (eq ▸ (mem_sdiff.mp xd).1)
    simpa [q,xu] using (spec x xr).2
  have escape (rc : r∈C) : ∃ z,z≠r ∧ z∉D ∧ q z∈C := by
    have rise (z : V) (zd : z∉D) (low : d z<d a) : ∃ w,w≠r ∧ w∉D ∧ q w∈C := by
      induction n : k z using Nat.strong_induction_on generalizing z with
      | h n ih =>
        have zr : z≠r := fun eq => zd (eq ▸ (mem_filter.mp rc).1)
        have less := (step z zr).2.2.trans_lt low
        by_cases pm : q z∈D
        · exact ⟨z,zr,zd,mem_filter.mpr ⟨pm,less⟩⟩
        · exact ih (k (q z)) (n ▸ down z zr) (q z) pm less rfl
    have au : a≠u := fun eq => up (eq ▸ ap)
    have da : d (q a)<d a := by have h := (spec a ar).2;rw [show q a=par a from if_neg au];omega
    by_cases pd : q a∈D
    · exact ⟨a,ar,fun m => (mem_sdiff.mp m).2 (mem_inter.mpr ⟨am,ap⟩),mem_filter.mpr ⟨pd,da⟩⟩
    · exact rise (q a) pd da
  obtain ⟨z⟩ := (leaf_core T T le_rfl tree hn (leaves T) Subset.rfl).1.nonempty
  have intZ : z.val∉leaves T := (mem_sdiff.mp z.property).2
  have tally := one_horizontal_defect T tree (by omega) z.val intZ A P
    (fun i im j jm ne e => ai i im j jm ne (sub e)) u v edge uo vo (fun e ne => cross e ne)
  have et : eligible A P z.val∩leaves T=X∩leaves T := by
    ext x;by_cases eq : x=z.val
    · subst x;simp [intZ]
    · simp [eligible_iff,X,eq]
  change Fintype.card V+(eligible A P z.val∩leaves T).card+(T.edgeFinset∩D.sym2).card=
    2+A.card+P.card+D.card+∑ v∈X,(T.degree v-2) at tally
  rw [et,trimmed_weight A P (leaves T) r] at tally
  have bound := forest_width T tree r q k d down take D (d a)
    (by simpa [d,dist_self] using gc.pos_dist_of_ne ar) monot escape
  change (T.edgeFinset∩D.sym2).card+Y.card+(if r∈D ∧ r∈leaves T then 1 else 0)≤
    D.card+∑ v∈C,(T.degree v-2) at bound
  change Fintype.card V+((eligible A P r∩leaves T).card+(if r∈D ∧ r∈leaves T then 1 else 0))+
    (T.edgeFinset∩D.sym2).card=2+A.card+P.card+D.card+∑ v∈X,(T.degree v-2) at tally
  have cc : C⊆X := (filter_subset ..).trans sdiff_subset
  have cost := sum_le_sum_of_subset_of_nonneg (f:=fun v => T.degree v-2) cc (fun _ _ _ => Nat.zero_le _)
  change (∑ v∈C,(T.degree v-2))≤∑ v∈X,(T.degree v-2) at cost
  have pay : (eligible A P r∩leaves T).card≤weightedLeaves G (eligible A P r) :=
    le_sup (f:=fun J => (eligible A P r∩leaves J).card) (mem_filter.mpr ⟨mem_univ _,sub,tree⟩)
  have budget := allowance_eq G gc (by omega) r p A ai
  change 1+A.card+P.card+allowance G r p A=weightedLeaves G (eligible A P r)+Fintype.card V at budget
  change Y.card+1≤allowance G r p A;omega

#print axioms layer_bonus
end Minimal180.OppositeGain
