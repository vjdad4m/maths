import UpperThirteen
namespace Graffiti384b.OddStars.ShoreDonors
open Finset SimpleGraph ShorePairs
open private Repair.nbr_mono from Repair384b
private def above {X Y : Type*} (t : Finset Y) (r : X→Y→Prop) [∀x y,Decidable (r x y)] (x : X) := t.filter (r x)
private def below {X Y : Type*} (s : Finset X) (r : X→Y→Prop) [∀x y,Decidable (r x y)] (y : Y) := s.filter (fun x => r x y)
private theorem double_count {X Y : Type*} {s : Finset X} {t : Finset Y}
    (r : X→Y→Prop) [∀x y,Decidable (r x y)] :
    (∑x∈s,(above t r x).card)=∑y∈t,(below s r y).card := by
  simp only [above,below,card_eq_sum_ones,sum_filter]
  exact sum_comm
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- With a common neighbor of the four ordinary vertices, delete two
nonadjacent ordinary vertices and replace them with one opposite vertex. -/
theorem exchange (A B C : Finset V) (ac : A.card=6) (bc : B.card=6)
    (dis : Disjoint A B) (ca : C⊆A) (cc : C.card=2)
    (cross : ∀c∈C,nbr G c B=2) (other : ∀b∈B,3≤nbr G b A)
    (sparse : (pairs G (A\C)).card≤1) (mates : ∀x∈A\C,∃y∈A,G.Adj x y)
    {b : V} (bm : b∈B) (all : ∀x∈A\C,G.Adj b x) (miss : ∀c∈C,¬G.Adj b c) :
    ∃D : Finset V,D⊆A∪B ∧ D.card=5 ∧ ∀v∈(A∪B)\D,2≤nbr G v D := by
  classical
  let U := A\C
  let T := B.erase b
  let P := U.powersetCard 2\pairs G U
  have uc : U.card=4 := by dsimp [U]; rw [card_sdiff ca,ac,cc]
  have tc : T.card=5 := by dsimp [T]; rw [card_erase_of_mem bm,bc]
  have pc : 5≤P.card := by
    dsimp only [P]; rw [card_sdiff (show pairs G U⊆U.powersetCard 2 from filter_subset ..),card_powersetCard,uc]
    change (pairs G U).card≤1 at sparse
    have k : Nat.choose 4 2=6 := by decide
    omega
  let R (p : Finset V) (y : V) := nbr G y A=3 ∧ ∀w∈p,G.Adj y w
  have credits : (∑ y∈T,nbr G y C)=4 := by
    have h := double_count (s:=T) (t:=C) G.Adj
    change (∑y∈T,nbr G y C)=_ at h
    rw [h]
    have point (c : V) (cm : c∈C) : (below T G.Adj c).card=2 := by
      have eq : below T G.Adj c=B.filter (G.Adj c) := by
        ext w; simp only [T,below,mem_filter,mem_erase,mem_filter]
        exact ⟨fun h => ⟨h.1.2,h.2.symm⟩,fun h => ⟨⟨fun e => miss c cm (e ▸ h.2.symm),h.1⟩,h.2.symm⟩⟩
      rw [eq]; exact cross c cm
    rw [sum_congr rfl point]; simp [cc]
  have row (y : V) (yt : y∈T) :
      2*(below P R y).card+3*nbr G y C≤6 := by
    have nc : nbr G y C≤2 := (card_filter_le ..).trans_eq cc
    by_cases three : nbr G y A=3
    · have part : nbr G y U+nbr G y C=3 := by
        have base : U∪C=A := sdiff_union_of_subset ca
        have d : Disjoint U C := sdiff_disjoint
        have e := congrArg card (filter_union (G.Adj y) U C)
        rw [base,card_union_of_disjoint (d.mono (filter_subset ..) (filter_subset ..))] at e
        exact e.symm.trans three
      have sub : below P R y⊆(U.filter (G.Adj y)).powersetCard 2 := by
        intro p pm
        obtain ⟨pp,_,sees⟩ := mem_filter.mp pm
        obtain ⟨pu,sz⟩ := mem_powersetCard.mp (mem_sdiff.mp pp).1
        exact mem_powersetCard.mpr ⟨fun w wm => mem_filter.mpr ⟨pu wm,sees _ wm⟩,sz⟩
      have h := card_le_card sub
      rw [card_powersetCard] at h
      change (below P R y).card≤(nbr G y U).choose 2 at h
      rcases (show nbr G y C=0 ∨ nbr G y C=1 ∨ nbr G y C=2 by omega) with e|e|e
      · have d : nbr G y U=3 := by omega
        rw [d] at h; simp [e,Nat.choose] at h ⊢; omega
      · have d : nbr G y U=2 := by omega
        rw [d] at h; simp [e] at h ⊢; omega
      · have d : nbr G y U=1 := by omega
        have n : Nat.choose 1 2=0 := by decide
        rw [d,n] at h; omega
    · have e : below P R y=∅ := eq_empty_iff_forall_not_mem.mpr
        (fun p h => three (mem_filter.mp h).2.1)
      rw [e,card_empty]; omega
  have mass := sum_le_sum row
  change (∑y∈T,(2*(below P R y).card+3*nbr G y C))≤∑_y∈T,6 at mass
  rw [sum_add_distrib,←mul_sum,←mul_sum,credits] at mass
  simp only [sum_const,Nat.nsmul_eq_mul,tc] at mass
  obtain ⟨p,pm,low⟩ : ∃p∈P,(above T R p).card≤1 := by
    apply Classical.byContradiction
    intro no
    push_neg at no
    have too := sum_le_sum (fun p (h : p∈P) => show 2≤(above T R p).card from no p h)
    rw [double_count R] at too
    simp only [sum_const,Nat.nsmul_eq_mul] at too
    omega
  obtain ⟨pU,p2⟩ := mem_powersetCard.mp (mem_sdiff.mp pm).1
  have pA : p⊆A := pU.trans sdiff_subset
  have stable {x y : V} (xm : x∈p) (ym : y∈p) : ¬G.Adj x y := by
    intro e
    have eq : ({x,y}:Finset V)=p := eq_of_subset_of_card_le
      (insert_subset xm (singleton_subset_iff.mpr ym)) (by rw [card_pair e.ne,p2])
    exact (mem_sdiff.mp pm).2 ((pair_mem G).mpr ⟨x,pU xm,y,pU ym,e,eq.symm⟩)
  obtain ⟨q,qb,fill,unique⟩ : ∃q∈B,(∀x∈p,G.Adj q x) ∧ ∀y∈B,R p y → y=q := by
    by_cases non : (above T R p).Nonempty
    · obtain ⟨q,qm⟩ := non
      obtain ⟨qt,qr⟩ := mem_filter.mp qm
      have nb : ¬R p b := by
        intro br
        have eq : nbr G b U=U.card := by unfold nbr; rw [filter_eq_self.mpr all]
        have bound := Repair.nbr_mono G b (show U⊆A from sdiff_subset)
        have three := br.1
        omega
      exact ⟨q,mem_of_mem_erase qt,qr.2,fun y ym yR =>
        card_le_one.mp low _ (mem_filter.mpr ⟨mem_erase.mpr ⟨fun e => nb (e ▸ yR),ym⟩,yR⟩) _ qm⟩
    · refine ⟨b,bm,fun x xm => all _ (pU xm),?_⟩
      intro y ym yr; apply Classical.byContradiction; intro yb
      exact non ⟨y,mem_filter.mpr ⟨mem_erase.mpr ⟨yb,ym⟩,yr⟩⟩
  let D := insert q (A\p)
  have qo : q∉A := fun qm => disjoint_left.mp dis qm qb
  have qoff : q∉A\p := fun h => qo (mem_sdiff.mp h).1
  refine ⟨D,insert_subset (mem_union_right _ qb) (sdiff_subset.trans subset_union_left),?_,?_⟩
  · dsimp [D]; rw [card_insert_of_not_mem qoff,card_sdiff pA,ac,p2]
  intro w wm
  obtain ⟨wu,wd⟩ := mem_sdiff.mp wm
  rcases mem_union.mp wu with wa|wb
  · have wp : w∈p := by apply Classical.byContradiction; intro missp; exact wd (mem_insert_of_mem (mem_sdiff.mpr ⟨wa,missp⟩))
    obtain ⟨f,fa,wf⟩ := mates _ (pU wp)
    have fd : f∈D := mem_insert_of_mem (mem_sdiff.mpr ⟨fa,fun fp => stable wp fp wf⟩)
    have sub : {q,f}⊆D.filter (G.Adj w) := insert_subset (mem_filter.mpr ⟨mem_insert_self ..,(fill _ wp).symm⟩)
      (singleton_subset_iff.mpr (mem_filter.mpr ⟨fd,wf⟩))
    have h := card_le_card sub
    rwa [card_pair (show q≠f from fun e => qo (e.symm ▸ fa))] at h
  · have enough : 2≤nbr G w (A\p) := by
      apply Nat.le_of_not_gt
      intro lo
      have split : nbr G w (A\p)+nbr G w p=nbr G w A := by
        have e := congrArg card (filter_union (G.Adj w) (A\p) p)
        rw [sdiff_union_of_subset pA,card_union_of_disjoint (sdiff_disjoint.mono (filter_subset ..) (filter_subset ..))] at e
        exact e.symm
      have big := other w wb
      have upper := (card_filter_le p (G.Adj w)).trans_eq p2
      change nbr G w p≤2 at upper
      have allp : p.filter (G.Adj w)=p := eq_of_subset_of_card_le (filter_subset ..) (by change p.card≤nbr G w p; omega)
      have eq := unique w wb ⟨by omega,fun x xm => (mem_filter.mp (allp.symm ▸ xm)).2⟩
      exact wd (eq ▸ mem_insert_self ..)
    exact enough.trans (Repair.nbr_mono G w (subset_insert ..))
end Graffiti384b.OddStars.ShoreDonors
#print axioms Graffiti384b.OddStars.ShoreDonors.exchange
