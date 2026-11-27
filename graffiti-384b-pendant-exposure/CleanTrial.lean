import RootContact
import FourClasses

namespace Graffiti384b.PendantRank
open Finset SimpleGraph Donor
open private FiniteRange.bad from FiniteRange384b
open private CliqueChoice.degree_neighbor from CliqueChoice384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def active (X k : Finset V) := k.filter (fun x => trianglesAt G x=(G.degree x).choose 2 ∧ 2≤nbr G x (Xᶜ∪k))

/-- Remove the exterior ear and the sampled simplicial vertices with two
retained neighbors. Every previously deficient pool vertex keeps exactly the
same neighbors among the seeds, so it can still participate in a pair repair. -/
theorem clean (X k : Finset V) (sub : k⊆X) (inj : Set.InjOn (trianglesAt G) (X:Set V))
    {e : V} (ex : e∉X) (outside : ∀x∈X,¬G.Adj e x) (degree : 2≤G.degree e) :
    ∃s : Finset V,s=(Xᶜ∪k)\insert e (active G X k) ∧ s.card+X.card+(active G X k).card+1=Fintype.card V+k.card ∧
      deficient G s⊆FiniteRange.bad G X k ∧
      ∀z∈FiniteRange.bad G X k,z∉s ∧ nbr G z s=nbr G z (Xᶜ∪k) := by
  classical
  let A := active G X k
  let R := Xᶜ∪k
  let s := R\insert e A
  have ar : A⊆k := filter_subset ..
  have ea : e∉A := fun em => ex (sub (ar em))
  have rm : insert e A⊆R := insert_subset (mem_union_left _ (mem_compl.mpr ex)) (ar.trans subset_union_right)
  have ss : s⊆R := sdiff_subset
  have no {x y : V} (xm : x∈A) (ym : y∈A) : ¬G.Adj x y := by
    intro xy
    have sx := (mem_filter.mp xm).2.1
    have sy := (mem_filter.mp ym).2.1
    have eq := Nat.le_antisymm (CliqueChoice.degree_neighbor G (CliqueChoice.saturated_clique G sx) xy)
      (CliqueChoice.degree_neighbor G (CliqueChoice.saturated_clique G sy) xy.symm)
    exact xy.ne (inj (sub (ar xm)) (sub (ar ym)) (sx.trans ((congrArg (fun d : ℕ => d.choose 2) eq).trans sy.symm)))
  have keep {p y : V} (pm : p∈A) (py : G.Adj p y) (yr : y∈R) : y∈s :=
    mem_sdiff.mpr ⟨yr,fun m => (mem_insert.mp m).elim
      (fun eq => outside p (sub (ar pm)) (eq ▸ py.symm)) (fun ya => no pm ya py)⟩
  have rescue {p z : V} (pm : p∈A) (zs : z∉s) (near : z=p ∨ G.Adj p z) : 2≤nbr G z s := by
    apply (mem_filter.mp pm).2.2.trans (card_le_card ?_)
    intro y ym
    obtain ⟨yr,py⟩ := mem_filter.mp ym
    have ys := keep pm py yr
    apply mem_filter.mpr ⟨ys,?_⟩
    rcases near with rfl|pw
    · exact py
    · exact CliqueChoice.saturated_clique G (mem_filter.mp pm).2.1 _ _ pw py (fun eq => zs (eq ▸ ys))
  have edgeSame {z : V} (zx : z∈X) (clear : ∀p∈A,¬G.Adj p z) : nbr G z s=nbr G z R := by
    apply Nat.le_antisymm (card_le_card (filter_subset_filter _ ss)) (card_le_card ?_)
    intro y ym
    obtain ⟨yr,zy⟩ := mem_filter.mp ym
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨yr,fun m => (mem_insert.mp m).elim
      (fun eq => outside z zx (eq ▸ zy.symm)) (fun ya => clear y ya zy.symm)⟩,zy⟩
  have ekeep : 2≤nbr G e s := by
    have ns : G.neighborFinset e⊆s.filter (G.Adj e) := by
      intro y ym
      have ey := (G.mem_neighborFinset ..).mp ym
      have yx : y∉X := fun hm => outside y hm ey
      exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_union_left _ (mem_compl.mpr yx),by simp [ey.ne.symm,show y∉A from fun m => yx (sub (ar m))]⟩,ey⟩
    exact degree.trans (by simpa [nbr] using card_le_card ns)
  have safe : deficient G s⊆FiniteRange.bad G X k := by
    intro z zm
    obtain ⟨zs,low⟩ := (mem_filter.mp zm).2
    have za : z∉A := fun m => (Nat.not_le_of_lt low) (rescue m zs (Or.inl rfl))
    have ze : z≠e := fun eq => (Nat.not_le_of_lt low) (eq ▸ ekeep)
    have zr : z∉R := fun m => zs (mem_sdiff.mpr ⟨m,by simp [ze,za]⟩)
    have zx : z∈X := Classical.byContradiction (fun m => zr (mem_union_left _ (mem_compl.mpr m)))
    have eq := edgeSame zx (fun p pm edge => (Nat.not_le_of_lt low) (rescue pm zs (Or.inr edge)))
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨zx,fun zk => zr (mem_union_right _ zk)⟩,eq ▸ low⟩
  have part := card_sdiff_add_card_eq_card rm
  have sx := card_compl X
  have rr : R.card=Xᶜ.card+k.card := card_union_of_disjoint (disjoint_compl_left.mono_right sub)
  rw [card_insert_of_not_mem ea] at part
  have lim := card_le_univ X
  refine ⟨s,rfl,by change (R\insert e A).card+X.card+A.card+1=_; omega,safe,?_⟩
  intro z zm
  obtain ⟨out,low⟩ := mem_filter.mp zm
  obtain ⟨zx,zk⟩ := mem_sdiff.mp out
  have zr : z∉R := fun m => (mem_union.mp m).elim (fun o => mem_compl.mp o zx) zk
  have zs : z∉s := fun m => zr (ss m)
  refine ⟨zs,edgeSame zx (fun p pm near => ?_)⟩
  exact (Nat.not_le_of_lt low) ((rescue pm zs (Or.inr near)).trans (card_le_card (filter_subset_filter _ ss)))

/-- For a usable second edge the unit discount survives deletion of all
activated simplicial vertices. The zero flag gives the ordinary estimate. -/
theorem trial (X k : Finset V) (sub : k⊆X) (inj : Set.InjOn (trianglesAt G) (X:Set V))
    {e : V} (ex : e∉X) (outside : ∀x∈X,¬G.Adj e x) (degree : 2≤G.degree e) (flag : ℕ)
    (event : flag=0 ∨ flag=1 ∧ ∃x∈FiniteRange.bad G X k,∃y∈FiniteRange.bad G X k,
      G.Adj x y ∧ nbr G x (Xᶜ∪k)=1) :
    gamma G+X.card+(active G X k).card+1+flag≤Fintype.card V+k.card+(FiniteRange.bad G X k).card := by
  obtain ⟨s,_,sz,small,same⟩ := clean G X k sub inj ex outside degree
  have ct := card_le_card small
  rcases event with rfl|⟨rfl,x,xm,y,ym,edge,one⟩
  · have win := batch_repair_saves G s ∅ (empty_subset _) (by simp)
    change gamma G≤s.card+(deficient G s).card-(∅ : Finset V).card at win
    simp only [card_empty,Nat.sub_zero] at win
    omega
  · have low := (mem_filter.mp ym).2
    have ylow : nbr G y s<2 := (same y ym).2.trans_lt low
    have win := pair_repair_saves G s x y edge (same x xm).1 (same y ym).1 ((same x xm).2.trans one) ylow
    change gamma G≤s.card+(deficient G s).card-1 at win
    have pos : 0<(deficient G s).card := card_pos.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,(same y ym).1,ylow⟩⟩
    omega

end Graffiti384b.PendantRank
#print axioms Graffiti384b.PendantRank.clean
#print axioms Graffiti384b.PendantRank.trial
