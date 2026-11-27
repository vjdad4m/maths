import JointEarRank
namespace Graffiti384b.Simplicial16
open Finset SimpleGraph Joint17 CliqueChoice
open private Joint17.eligible Joint17.poolNbr from JointEarSample
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private CliqueChoice.degree_neighbor from CliqueChoice384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def saturated (v : V) := trianglesAt G v=(G.degree v).choose 2
instance (v : V) : Decidable (saturated G v) := inferInstanceAs (Decidable (_=_))
def activated (X s : Finset V) := s.filter (fun v => saturated G v ∧ 2≤nbr G v (Xᶜ∪s))

/-- Remove all activated sampled simplicial vertices together. Their distinct
scores make them pairwise nonadjacent; every affected omitted neighbor sees
the same two surviving witnesses. -/
theorem trial (X E s : Finset V) (sep : Disjoint X E) (ind : ∀ u∈E,∀ v∈E,¬G.Adj u v)
    (two : ∀ v∈E,G.degree v=2) (sub : s⊆X) (highX : X⊆high G)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) :
    gamma G+(X\s).card+(Joint17.eligible G X E s).card+(activated G X s).card≤
      Fintype.card V+(FiniteRange.bad G X s).card := by
  classical
  let P := activated G X s
  let t := s\P
  have ps : P⊆s := filter_subset ..
  have ts : t⊆s := sdiff_subset
  have no {x y : V} (xp : x∈P) (yp : y∈P) : ¬G.Adj x y := by
    intro xy
    have sx := (mem_filter.mp xp).2.1
    have sy := (mem_filter.mp yp).2.1
    have d := Nat.le_antisymm (CliqueChoice.degree_neighbor G (saturated_clique G sx) xy)
      (CliqueChoice.degree_neighbor G (saturated_clique G sy) xy.symm)
    exact xy.ne (inj (sub (ps xp)) (sub (ps yp)) (sx.trans ((congrArg (fun j : ℕ => j.choose 2) d).trans sy.symm)))
  have keep {p y : V} (pp : p∈P) (py : G.Adj p y) (ym : y∈Xᶜ∪s) : y∈Xᶜ∪t := by
    rcases mem_union.mp ym with off|ys
    · exact mem_union_left _ off
    · exact mem_union_right _ (mem_sdiff.mpr ⟨ys,fun yp => no pp yp py⟩)
  have earKeep : Joint17.eligible G X E s⊆Joint17.eligible G X E t := by
    intro v vm
    obtain ⟨ve,hit⟩ := mem_filter.mp vm
    refine mem_filter.mpr ⟨ve,?_⟩
    intro y ym
    apply mem_sdiff.mpr; refine ⟨hit ym,?_⟩; intro yp
    have d := CliqueChoice.degree_neighbor G (saturated_clique G (mem_filter.mp yp).2.1) (mem_filter.mp ym).2.symm
    have hi : 3≤G.degree y := (mem_filter.mp (highX (sub (ps yp)))).2
    rw [two v ve] at d; omega
  have safe {p w : V} (pp : p∈P) (out : w∉Xᶜ∪t) (near : w=p ∨ G.Adj p w) : 2≤nbr G w (Xᶜ∪t) := by
    apply (mem_filter.mp pp).2.2.trans (card_le_card ?_)
    intro y ym
    obtain ⟨old,py⟩ := mem_filter.mp ym
    have kept := keep pp py old
    refine mem_filter.mpr ⟨kept,?_⟩
    rcases near with rfl|pw
    · exact py
    · exact saturated_clique G (mem_filter.mp pp).2.1 _ _ pw py (fun eq => out (eq ▸ kept))
  have bs : FiniteRange.bad G X t⊆FiniteRange.bad G X s := by
    intro w wm
    obtain ⟨xo,low⟩ := mem_filter.mp wm
    obtain ⟨wx,wt⟩ := mem_sdiff.mp xo
    have out : w∉Xᶜ∪t := fun h => (mem_union.mp h).elim (fun o => mem_compl.mp o wx) wt
    have wp : w∉P := fun m => (not_lt_of_ge (safe m out (Or.inl rfl))) low
    have edges {p} (pp : p∈P) : ¬G.Adj p w := fun pw => (not_lt_of_ge (safe pp out (Or.inr pw))) low
    have mono : nbr G w (Xᶜ∪s)≤nbr G w (Xᶜ∪t) := by
      apply card_le_card; intro y ym
      obtain ⟨old,wy⟩ := mem_filter.mp ym
      refine mem_filter.mpr ⟨?_,wy⟩
      exact (mem_union.mp old).elim (mem_union_left _)
        (fun ys => mem_union_right _ (mem_sdiff.mpr ⟨ys,fun yp => edges yp wy.symm⟩))
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨wx,fun ws => wt (mem_sdiff.mpr ⟨ws,wp⟩)⟩,mono.trans_lt low⟩
  have z := Joint17.trial G X E t sep ind two (ts.trans sub)
  rw [card_sdiff (ts.trans sub)] at z
  have tt : t.card+P.card=s.card := card_sdiff_add_card_eq_card ps
  have sx := card_le_card sub
  have ecard := card_le_card earKeep
  have bcard := card_le_card bs
  rw [card_sdiff sub]; change gamma G+_+_+P.card≤_
  omega

private def bonus (d : ℕ) := (26:ℕ).choose 8-FiniteRange.badCount 27 8 d

/-- Insertion into an eight-vertex sample activates a designated center
unless it has fewer than two retained neighbors. The old deficiency
fiber already bounds the number of these exceptions. -/
private theorem active_fiber (X : Finset V) (xs : X.card=27) {v : V} (vx : v∈X) (sat : saturated G v)
    (k d : ℕ) (di : d≤G.degree v) (dr : d<27) :
    (26:ℕ).choose k-FiniteRange.badCount 27 k d≤((X.powersetCard (k+1)).filter (fun s => v∈activated G X s)).card := by
  classical
  let K := (X.erase v).powersetCard k
  let ok := fun s : Finset V => 2≤nbr G v (Xᶜ∪s)
  have total := filter_card_add_filter_neg_card_eq_card (s:=K) ok
  have ks : K.card=(26:ℕ).choose k := by dsimp [K]; rw [card_powersetCard,card_erase_of_mem vx,xs]
  have fail : K.filter (fun s => ¬ok s)⊆(X.powersetCard k).filter (fun s => v∈FiniteRange.bad G X s) := by
    intro s sm
    obtain ⟨sk,no⟩ := mem_filter.mp sm
    obtain ⟨se,sc⟩ := mem_powersetCard.mp sk
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨se.trans (erase_subset ..),sc⟩,
      mem_filter.mpr ⟨mem_sdiff.mpr ⟨vx,fun vs => (mem_erase.mp (se vs)).1 rfl⟩,Nat.lt_of_not_ge no⟩⟩
  have bound := FiniteRange.count_bad G X k d v vx di (xs ▸ dr)
  rw [xs] at bound
  have small := (card_le_card fail).trans bound
  let good := K.filter ok
  have off {s : Finset V} (sm : s∈good) : v∉s := fun vs =>
    (mem_erase.mp ((mem_powersetCard.mp (mem_filter.mp sm).1).1 vs)).1 rfl
  have inj : Set.InjOn (insert v) (good:Set (Finset V)) := by
    intro s sm t tm eq
    simpa [erase_insert (off sm),erase_insert (off tm)] using congrArg (fun S : Finset V => S.erase v) eq
  have inc : good.image (insert v)⊆(X.powersetCard (k+1)).filter (fun s => v∈activated G X s) := by
    intro t tm
    obtain ⟨s,sm,rfl⟩ := mem_image.mp tm
    obtain ⟨ks',yes⟩ := mem_filter.mp sm
    obtain ⟨se,sc⟩ := mem_powersetCard.mp ks'
    have sub := insert_subset vx (se.trans (erase_subset ..))
    have ct := card_insert_of_not_mem (off sm)
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sub,by omega⟩,mem_filter.mpr ⟨mem_insert_self ..,sat,?_⟩⟩
    exact yes.trans (card_le_card (filter_subset_filter _ (union_subset_union Subset.rfl (subset_insert ..))))
  have count := card_le_card inc
  rw [card_image_of_injOn inj] at count
  change good.card+_=K.card at total
  omega

end Graffiti384b.Simplicial16
#print axioms Graffiti384b.Simplicial16.trial
