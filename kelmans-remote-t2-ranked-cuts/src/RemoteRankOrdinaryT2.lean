import RemoteAvoid3RankTransfer
import RemoteT2ZeroShore
import RemoteT2AvoidThree

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteRankOrdinaryT2
open SquareCap (FactorOn HasFactor PairRest pairMinor omitEdge)
open RemoteT2Scope (Remote)
open RemoteT2AvoidThree (factor_image_injOn)
open RemoteT2ZeroShore (SmallerT2)
open RemoteAvoid3RankTransfer (SmallerRemoteT2)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In any cubic graph with at least eight vertices, a root's closed
neighborhood does not cover every edge. If it did, each exterior
vertex would have precisely the three neighbors of the root,
contradicting cubicity at a root-neighbor. -/
theorem cubic_has_remote_edge (cub : ∀ z,G.degree z=3) (big : 8≤Fintype.card V) (x : V) :
    ∃ u v : V,G.Adj u v ∧ Remote G x u v := by
  classical
  let N := G.neighborFinset x
  let S := insert x N
  let T := univ \ S
  have nc : N.card=3 := (card_neighborFinset_eq_degree G x).trans (cub x)
  have nself : x∉N := fun h=>G.loopless x ((mem_neighborFinset _ _ _).mp h)
  have sc : S.card=4 := by rw [show S=insert x N from rfl,card_insert_of_not_mem nself,nc]
  have tc : T.card+4=Fintype.card V := by
    have p := card_sdiff_add_card_eq_card (subset_univ S)
    rwa [sc,card_univ] at p
  have outside (z : V) : z∈T ↔ z≠x∧¬G.Adj x z := by
    simp [T,S,N,mem_neighborFinset]
  have ex : ∃ u v : V,u∈T∧v∈T∧G.Adj u v := by
    apply Classical.byContradiction
    intro no
    have collapse (u : V) (uu : u∈T) : G.neighborFinset u=N := by
      apply eq_of_subset_of_card_le
      · intro v vm
        have edge := (mem_neighborFinset _ _ _).mp vm
        have vi : v∉T := fun vt=>no ⟨u,v,uu,vt,edge⟩
        have si : v∈S := by
          by_cases si : v∈S
          · exact si
          · exact (vi $ mem_sdiff.mpr ⟨mem_univ _,si⟩).elim
        rcases mem_insert.mp si with rfl|e
        · exact (((outside u).mp uu).2 edge.symm).elim
        · exact e
      · rw [nc,card_neighborFinset_eq_degree,cub]
    obtain ⟨y,yn⟩ := (card_pos.mp (by omega : 0<N.card))
    have sub : T⊆G.neighborFinset y := by
      intro u uu
      have uy : y∈G.neighborFinset u := by rw [collapse u uu]; exact yn
      exact (mem_neighborFinset _ _ _).mpr ((mem_neighborFinset _ _ _).mp uy).symm
    have lb := card_le_card sub
    rw [card_neighborFinset_eq_degree,cub] at lb
    omega
  obtain ⟨u,v,ut,vt,uv⟩ := ex
  obtain ⟨ux,ra⟩ := (outside u).mp ut
  obtain ⟨vx,rb⟩ := (outside v).mp vt
  exact ⟨u,v,uv,ux,vx,ra,rb⟩

/-- There is no rank overhead in deriving smaller ordinary T2 from
smaller Remote T2: pick an actual remote edge on the same input,
factor after omitting it, then retain that factor in the pair minor. -/
theorem smaller_t2_of_remote (n : ℕ) (remote : SmallerRemoteT2.{u} n) : SmallerT2.{u} n := by
  classical
  intro W _ _ G _ less cub conn small rem r edge
  let x := r false
  let y := r true
  have sz := conn.1
  have big : 8≤Fintype.card W := by omega
  obtain ⟨u,v,uv,far⟩ := cubic_has_remote_edge G cub big x
  have uy : u≠y := fun e=>far.2.2.1 (e.symm ▸ edge)
  have f := remote W G less rem cub conn small x y u v edge uv far
  let S : Finset W := (univ.erase x).erase y
  let p0 : PairRest r := ⟨u,far.1,uy⟩
  let q : W→PairRest r := fun z=>if h : z≠x∧z≠y then ⟨z,h⟩ else p0
  have values (z : W) (h : z∈S) : (q z).val=z := by
    have d : z≠x∧z≠y := by simpa [S,and_comm] using h
    simp [q,d]
  have inj : Set.InjOn q (↑S : Set W) := by
    intro a ha b hb e
    exact (values a ha).symm.trans ((congrArg Subtype.val e).trans (values b hb))
  have mono : ∀ a∈S,∀ b∈S,(omitEdge G u v).Adj a b→(pairMinor G r).Adj (q a) (q b) := by
    intro a ha b hb ed
    change G.Adj (q a).val (q b).val
    rw [values a ha,values b hb]
    exact ed.1
  have cover : S.image q=univ := by
    apply eq_univ_of_forall
    intro z
    have hz : z.val∈S := mem_erase.mpr ⟨z.property.2,mem_erase.mpr ⟨z.property.1,mem_univ _⟩⟩
    exact mem_image.mpr ⟨z.val,hz,Subtype.ext (values z.val hz)⟩
  have t := factor_image_injOn q inj mono f
  rwa [cover] at t

#print axioms cubic_has_remote_edge
#print axioms smaller_t2_of_remote
end KelmansCactus.AtomicBridge.RemoteRankOrdinaryT2
