import RemoteSpacedPrismPotential
import RemoteSpacedPrismWidth
import PrismSpacedFinal

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteSpacedPrismObstruction
open RemoteSpacedPrismLayout
open RemoteSpacedPrismHandle (Port pole endThird embed)
open RemoteSpacedPrismOld (CoreSource source source_packing source_cover prior prior_packing oldEmb)
open RemoteVacancyReach (Packing Slides OneCleanup)
open RemoteT2CompletionTransfer (eraseEdge)
open SquareCap (HasFactor SmallTrivial ThreeConnected NontrivialSide boundary)
noncomputable section

abbrev H (k : Nat) := RemoteSpacedPrismHandle.Host (marks k)
abbrev HostV (k : Nat) := RemoteSpacedPrismHandle.V4 (Core k)

theorem host_cubic (k : Nat) : ∀ x,(H k).degree x=3 :=
  RemoteSpacedPrismHandle.cubic (marks k) (core_cube k)

theorem host_small (k : Nat) : SmallTrivial (H k) :=
  RemoteSpacedPrismHandle.small_trivial (marks k) (core_cube k) (core_cyclic_four k)

theorem core_order (k : Nat) : Fintype.card (Core k)=12*gap k := by
  simp only [Core,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,columns]
  omega

theorem core_three_connected (k : Nat) : ThreeConnected (core k) :=
  SquareCap.three_connected_of_small_trivial _ (core_cube k)
    (by rw [core_order]; have h := gap_pos k; omega) (core_cyclic_four k)

theorem host_order (k : Nat) : Fintype.card (HostV k)=Fintype.card (Core k)+8 :=
  RemoteSpacedPrismHandle.order_card

theorem host_three_connected (k : Nat) : ThreeConnected (H k) :=
  SquareCap.three_connected_of_small_trivial _ (host_cubic k)
    (by rw [host_order]; omega) (host_small k)

theorem exact_order (k : Nat) :
    Fintype.card (Core k)%6=0 ∧ Fintype.card (HostV k)%6=2 ∧
    Fintype.card (Core k)<Fintype.card (HostV k) := by
  rw [host_order,core_order]
  omega

theorem exact_remote (k : Nat) :
    (H k).Adj (pole false) (pole true) ∧
    (H k).Adj (endThird false) (endThird true) ∧
    RemoteT2Scope.Remote (H k) (pole false) (endThird false) (endThird true) :=
  ⟨RemoteSpacedPrismHandle.pole_join (marks k),RemoteSpacedPrismHandle.remote_edge (marks k),
    RemoteSpacedPrismHandle.remote (marks k)⟩

theorem exact_board (k : Nat) :
    Function.Injective (embed (V:=Core k)) ∧
    (∀ x : HostV k,x≠pole false∧x≠pole true ↔ ∃ y : Board k,embed y=x) ∧
    (∀ a b : Board k,(board k).Adj a b ↔
      (eraseEdge (H k) (endThird false) (endThird true)).Adj (embed a) (embed b)) :=
  ⟨RemoteSpacedPrismHandle.embed_injective,RemoteSpacedPrismHandle.embed_range,
    RemoteSpacedPrismHandle.exact_survivor (marks k)⟩

theorem wide (k : Nat) (c : Board k→Bool) (h : ∀ b,NontrivialSide c b) :
    3≤(boundary (board k) c).card :=
  RemoteSpacedPrismWidth.expanded_wide (marks k) (core_cube k) (core_cyclic_four k) c h

/-- Omitting only selected marked edges may add back any of the unused
marked rungs. The same hard starting factor is admissible for all choices. -/
def withOmissions (k : Nat) (J : Finset Port) : SimpleGraph (Core k) where
  Adj x y := (core k).Adj x y ∧ ¬∃ i∈J,(marks k).Pair i x y
  symm := by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    rintro ⟨i,im,p⟩
    exact h.2 ⟨i,im,(marks k).pair_symm p⟩
  loopless x h := (core k).loopless x h.1

theorem admissible_source (k : Nat) (J : Finset Port) :
    Packing (withOmissions k J) (source k) ∧ (source k).biUnion id=univ := by
  refine ⟨⟨?_,(source_packing k).2⟩,source_cover k⟩
  intro T tm
  obtain ⟨ct,c,cm,cent⟩ := (source_packing k).1 T tm
  refine ⟨ct,c,cm,?_⟩
  intro v vm vc
  obtain ⟨adj,all⟩ := (RemoteSpacedPrismOld.core_source_adj k c v).mp (cent v vm vc)
  refine ⟨adj,?_⟩
  rintro ⟨i,_,p⟩
  exact all ⟨i,p⟩

theorem dense_legal_board (k : Nat) : HasFactor (board k) :=
  PrismSpacedFinal.full_factor k

def Succeeds (k B : Nat) (P : Finset (Finset (Board k))) : Prop :=
  ∃ n≤B,∃ Q F,Slides n P Q ∧ OneCleanup Q F ∧
    Packing (board k) F ∧ F.biUnion id=univ

theorem fails_at_requested_bound (B : Nat) : ¬Succeeds (B+2) B (prior (B+2)) := by
  rintro ⟨n,nb,Q,F,s,c,hf,full⟩
  exact RemoteSpacedPrismPotential.no_short_route B hf full nb s c

/-- No numeric bound works uniformly over even the all-old canonical
rank outputs on the explicit family of genuine Remote T2 boards.
Every board in this family nonetheless has an explicit full factor. -/
theorem no_uniform_arbitrary_rank_bound :
    ¬∃ B, ∀ k,∀ R : Finset (Finset (Core k)),
      Packing (CoreSource k) R → R.biUnion id=univ →
      Succeeds k B (R.image (Finset.map (oldEmb k))) := by
  rintro ⟨B,h⟩
  exact fails_at_requested_bound B
    (h (B+2) (source (B+2)) (source_packing (B+2)) (source_cover (B+2)))

#print axioms host_three_connected
#print axioms exact_board
#print axioms exact_remote
#print axioms wide
#print axioms dense_legal_board
#print axioms no_uniform_arbitrary_rank_bound
end
end KelmansCactus.AtomicBridge.RemoteSpacedPrismObstruction
