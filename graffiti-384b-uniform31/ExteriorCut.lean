import JoiningTips
import ForkTip
namespace Graffiti384b.TenPins
open Finset SimpleGraph EarFrame33 EightPins ForkGuard34
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A triangle through two private exterior neighbors finishes the cut. At most
one vertex of a closed region can need help from w; orient its cut to supply it. -/
theorem exterior_cut (t : (types G).card=31) (q : (nonleaves G).card=31) (bad : bound G<gamma G)
    {e f w : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2) :
    let A := G.neighborFinset e∪G.neighborFinset f
    w∈A → (∀ z∈row G A w,nbr G z A=1) → (∀ z∈row G A w,nbr G z (row G A w)≤1) →
    (∀a∈A,a≠w → 10≤trianglesAt G a) → ∀i∈row G A w,∀j∈row G A w,¬G.Adj i j := by
  classical
  let A := G.neighborFinset e∪G.neighborFinset f
  let X := high G\A
  dsimp only
  intro wa priv matching gap i ir j jr ij
  have data := anchor_data G t q bad ef de df
  obtain ⟨P,Q,ap,eq,tip,free⟩ := fork_tip G data wa priv gap
  let T := X\(P∪Q)
  have sub (v : V) (vm : v∈row G A w) : v∈T := mem_sdiff.mpr ⟨(mem_filter.mp vm).1,fun h => disjoint_left.mp free vm h⟩
  have away : Disjoint T (P∪Q) := disjoint_left.mpr (fun _ h => (mem_sdiff.mp h).2)
  have inE {v : V} (dv : G.degree v=2) : v∈LowSample.twos G := mem_sdiff.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  have stop (res : ∃ L R,P⊆L ∧ Q⊆R ∧ Frame G L R) : False := by
    obtain ⟨L,R,_,qr,fr⟩ := res
    exact ef (Squares29.sparse G bad _ _ fr e (mem_union_right _ (qr (eq (inE de))))
      f (mem_union_right _ (qr (eq (inE df)))) de df)
  have wi := (mem_filter.mp ir).2
  rcases flexible_region G tip wi (mem_filter.mp jr).2 ij (sub i ir) (sub j jr) away with done|⟨C,ct,ic,_,fixed,closed⟩
  · exact stop done
  have cx : C⊆X := ct.trans sdiff_subset
  have rg {v : V} (vc : v∈C) (wv : G.Adj w v) : nbr G v (C.filter (G.Adj w))≤1 :=
    (card_le_card (filter_subset_filter _ (filter_subset_filter _ cx))).trans (matching v (mem_filter.mpr ⟨cx vc,wv⟩))
  obtain ⟨hs,_⟩ := TwoEars.profile G t q bad
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by rw [t,hs])
  have degree {v : V} (vc : v∈C) (few : nbr G v C≤2) :
      trianglesAt G v=2 ∧ G.Adj w v ∧ 0<nbr G v C := by
    have vx := cx vc; have vh := (mem_sdiff.mp vx).1; have va := (mem_sdiff.mp vx).2
    have cover (a z : V) (av : G.Adj v a) (vz : G.Adj v z) (az : G.Adj a z) : a∈insert w C := by
      have ag : a∈high G := by
        apply Classical.byContradiction
        intro notHigh
        have upper : G.degree a≤2 := Nat.le_of_not_gt (fun h => notHigh (mem_filter.mpr ⟨mem_univ _,h⟩))
        have inc : {v,z}⊆G.neighborFinset a := insert_subset ((G.mem_neighborFinset ..).mpr av.symm) (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr az))
        have size := card_le_card inc; rw [card_pair vz.ne,card_neighborFinset_eq_degree] at size
        exact va (data.ears a (inE (by omega)) ((G.mem_neighborFinset ..).mpr av.symm))
      by_cases am : a∈P∪Q
      · exact mem_insert.mpr (Or.inl (fixed v vc a am av))
      · have an : a∉A := fun h => am (mem_union_left _ (ap h))
        exact mem_insert_of_mem (closed v vc a (mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨ag,an⟩,am⟩) av)
    have cap := local_link G (rg vc) cover
    have c1 := Nat.choose_le_choose 2 few
    rw [show (2:ℕ).choose 2=1 by decide] at c1
    have lo := floor v vh
    by_cases wv : G.Adj w v
    · rw [if_pos wv] at cap
      refine ⟨by omega,wv,?_⟩
      by_contra! h; have zero : nbr G v C=0 := by omega
      rw [zero,show (0:ℕ).choose 2=0 by decide] at cap; omega
    · rw [if_neg wv] at cap; omega
  by_cases all : ∀v∈C,3≤nbr G v C
  · exact stop (join_tips G tip ic wi (away.mono_left ct) (by have h := all i ic; omega) (fun v vc _ => all v vc))
  push_neg at all
  obtain ⟨z,zc,few⟩ := all
  obtain ⟨score,wz,pos⟩ := degree zc (by omega)
  refine stop (join_tips G tip zc wz (away.mono_left ct) pos ?_)
  intro v vc vz; apply Nat.le_of_not_gt; intro low
  exact vz (inj (mem_sdiff.mp (cx vc)).1 (mem_sdiff.mp (cx zc)).1 ((degree vc (by omega)).1.trans score.symm))
end Graffiti384b.TenPins
#print axioms Graffiti384b.TenPins.exterior_cut
