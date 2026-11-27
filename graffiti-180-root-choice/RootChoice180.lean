import MinimalVertex180
import MiddleCertificate180
import FirstForm180
import StarExchange180

set_option warningAsError true
namespace Minimal180.HigherRank
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- When the adjoined vertex is a leaf, its old neighbor x cannot be a
leaf. Removing the new leaf therefore transfers every counted old leaf
to the lower problem with x removed from the mark. -/
theorem leaf_attachment_upper (G : SimpleGraph V) (hn : 2<Fintype.card V) (N U : Finset V)
    (e : Bool) (T : SimpleGraph (V⊕Unit)) (sub : T≤ear G N) (tr : T.IsTree)
    (lf : Sum.inr ()∈leaves T) :
    ∃ x∈N,(lift U e∩leaves T).card≤weightedLeaves G (U.erase x)+e.toNat := by
  classical
  have high : 2<Fintype.card (V⊕Unit) := by simp [Fintype.card_sum]; omega
  obtain ⟨v,rv⟩ := exists_adj T tr.isConnected (by omega) (Sum.inr ())
  cases v with
  | inr u => exact (sub rv : False).elim
  | inl x =>
    have xn : x∈N := sub rv
    have only (b : V) (rb : T.Adj (.inr ()) (.inl b)) : b=x :=
      Sum.inl.inj (leaf_unique T lf rb rv)
    have low : squash T x≤G := by
      intro a b h
      rcases h with edge|⟨_,bx,rb⟩|⟨ax,_,ar⟩
      · exact sub edge
      · exact (bx (only b rb)).elim
      · exact (ax (only a ar.symm)).elim
    obtain ⟨S,sk,st⟩ := (squash_connected T tr.isConnected x).exists_isTree_le
    have old {a b : V} (ab : S.Adj a b) : T.Adj (.inl a) (.inl b) := by
      rcases sk ab with h|⟨_,ne,rb⟩|⟨ne,_,ar⟩
      · exact h
      · exact (ne (only b rb)).elim
      · exact (ne (only a ar.symm)).elim
    let W := lift U e∩leaves T
    let Z := (U.erase x)∩leaves S
    have inc : W⊆lift Z e := by
      rintro (a|u) h
      · obtain ⟨m,l⟩ := mem_inter.mp h
        have ax : a≠x := by
          rintro rfl; exact leaves_nonadjacent T tr high rv lf l
        apply (inl_lift Z e a).mpr
        refine mem_inter.mpr ⟨mem_erase.mpr ⟨ax,(inl_lift U e a).mp m⟩,?_⟩
        apply leaf_of_unique S st.isConnected (by omega)
        intro b c bnd cnd
        exact Sum.inl.inj (leaf_unique T l (old bnd) (old cnd))
      · exact (inr_lift Z e u).mpr ((inr_lift U e u).mp (mem_inter.mp h).1)
    have cnt := card_le_card inc
    rw [card_lift] at cnt
    have cap := score_of_tree G S (sk.trans low) st (U.erase x)
    exact ⟨x,xn,cnt.trans (Nat.add_le_add_right cap _)⟩

/-- Exact arbitrary-rank decomposition for all spanning trees of a
one-vertex extension. Either a tree containing the full new root star
meets the target, or a single lower weighted-leaf problem meets it.
Both alternatives use the original unrestricted leaf objective. -/
theorem star_or_deletion (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N U : Finset V) (nz : N.Nonempty) (e : Bool) (t : ℕ) :
    let H := ear G N
    let M := lift U e
    let r : V⊕Unit := .inr ()
    t≤weightedLeaves H M ↔
    (∃ T≤H,T.IsTree ∧ (∀ y,H.Adj r y → T.Adj r y) ∧ t≤(M∩leaves T).card) ∨
    ∃ x∈N,t≤weightedLeaves G (U.erase x)+e.toNat := by
  classical
  intro H M r
  have hc := ear_connected G gc N nz
  have high : 1<Fintype.card (V⊕Unit) := by simp [Fintype.card_sum]; omega
  constructor
  · intro goal
    obtain ⟨T,sub,tr,eq⟩ := tree_opt H hc M
    by_cases lf : r∈leaves T
    · obtain ⟨x,xn,bound⟩ := leaf_attachment_upper G hn N U e T sub tr lf
      exact Or.inr ⟨x,xn,(eq ▸ goal).trans bound⟩
    · obtain ⟨K,kg,kt,star,keep⟩ := full_star_exchange H T sub tr high r
      have inc : M∩leaves T⊆M∩leaves K := fun x hx => mem_inter.mpr
        ⟨(mem_inter.mp hx).1,keep x (fun same => lf (same ▸ (mem_inter.mp hx).2)) (mem_inter.mp hx).2⟩
      exact Or.inl ⟨K,kg,kt,star,(eq ▸ goal).trans (card_le_card inc)⟩
  · rintro (⟨T,sub,tr,_,paid⟩|⟨x,xn,paid⟩)
    · exact paid.trans (score_of_tree H T sub tr M)
    · exact paid.trans (attach G gc hn N U e x xn)

/-- A scalar recurrence separating the apex eligibility bonus from the
best old tree after excluding one attachment neighbor. -/
theorem apex_score (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N U : Finset V) (neighbors : 1<N.card) (e : Bool) :
    weightedLeaves (ear G N) (lift U e)=
      max (weightedLeaves (ear G N) (lift U false))
        (N.sup (fun x => weightedLeaves G (U.erase x))+e.toNat) := by
  classical
  let H := ear G N
  let F := fun x => weightedLeaves G (U.erase x)
  obtain ⟨a,an,b,bn,ab⟩ := one_lt_card.mp neighbors
  have nz : N.Nonempty := ⟨a,an⟩
  obtain ⟨w,wn,mx⟩ := exists_mem_eq_sup (s:=N) (f:=F) nz
  have mono : lift U false⊆lift U e := by
    rintro (x|u) hx
    · exact (inl_lift U e x).mpr ((inl_lift U false x).mp hx)
    · have f := (inr_lift U false u).mp hx; contradiction
  change weightedLeaves H (lift U e)=max (weightedLeaves H (lift U false)) (N.sup F+e.toNat)
  apply le_antisymm
  · rcases (star_or_deletion G gc hn N U nz e _).mp (le_refl (weightedLeaves H (lift U e))) with top|old
    · obtain ⟨T,sub,tr,star,paid⟩ := top
      have no : Sum.inr ()∉leaves T := fun lf => ab (Sum.inl.inj (leaf_unique T lf (star (.inl a) an) (star (.inl b) bn)))
      have same : lift U e∩leaves T=lift U false∩leaves T := by
        ext x
        cases x with
        | inl x => simp
        | inr u => cases u; simp [no]
      rw [same] at paid
      exact (paid.trans (score_of_tree H T sub tr (lift U false))).trans (le_max_left ..)
    · obtain ⟨x,xn,pay⟩ := old
      exact (pay.trans (Nat.add_le_add_right (le_sup (f:=F) xn) _)).trans (le_max_right ..)
  · apply max_le
    · exact eligible_mono H mono
    · rw [mx]
      exact attach G gc hn N U e w wn

/-- Marking the apex gives one additional eligible leaf precisely when
one deletion problem already attains the upper optimum with apex unmarked. -/
theorem apex_gain_iff (G : SimpleGraph V) (gc : G.Connected) (hn : 2<Fintype.card V)
    (N U : Finset V) (neighbors : 1<N.card) :
    let H := ear G N
    weightedLeaves H (lift U true)=weightedLeaves H (lift U false)+1 ↔
      ∃ x∈N,weightedLeaves G (U.erase x)=weightedLeaves H (lift U false) := by
  classical
  intro H
  obtain ⟨a,an,b,bn,_⟩ := one_lt_card.mp neighbors
  let F := fun x => weightedLeaves G (U.erase x)
  obtain ⟨w,wn,mx⟩ := exists_mem_eq_sup (s:=N) (f:=F) ⟨a,an⟩
  have low (x : V) (xn : x∈N) : F x≤weightedLeaves H (lift U false) := by
    simpa only [Bool.toNat_false,add_zero] using attach G gc hn N U false x xn
  have eq := apex_score G gc hn N U neighbors true
  change weightedLeaves H (lift U true)=max (weightedLeaves H (lift U false)) (N.sup F+1) at eq
  constructor
  · intro gain
    refine ⟨w,wn,?_⟩
    change F w=weightedLeaves H (lift U false)
    rw [mx] at eq
    have := low w wn
    omega
  · rintro ⟨x,xn,pay⟩
    change F x=weightedLeaves H (lift U false) at pay
    have u := le_sup (f:=F) xn
    have v := low w wn
    omega

#print axioms apex_score
#print axioms apex_gain_iff
#print axioms leaf_attachment_upper
#print axioms star_or_deletion
end Minimal180.HigherRank
