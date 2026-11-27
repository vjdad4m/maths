import FlexibleTip
namespace Graffiti384b.EightPins
open Finset SimpleGraph
open SparsePairs
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- With eight contacts, a two-element private row and the score gap, all
three other anchors have a shared exterior neighbor. The two ears and all
multiple contacts give the fixed opposite side of a cut. -/
theorem boundary {e f w : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2)
    (t : (types G).card=31) (q : (nonleaves G).card=31) (bad : bound G<gamma G)
    (A : Finset V) (ae : G.neighborFinset e∪G.neighborFinset f=A)
    (wa : w∈A) (ws : trianglesAt G w=2) (one : nbr G w A≤1)
    (k2 : nbr G w (high G\A)=2)
    (priv : ∀ z∈(high G\A).filter (G.Adj w),nbr G z A=1)
    (eight : ((high G\A).filter (fun z => 0<nbr G z A)).card=8) :
    let D := (high G\A).filter (fun z => 2≤nbr G z A)
    Tip G A (({e,f}:Finset V)∪D) w := by
  classical
  let X := high G\A; let E : Finset V := {e,f}
  let H := X.filter (fun z => 0<nbr G z A)
  let D := X.filter (fun z => 2≤nbr G z A)
  let row := fun a => X.filter (G.Adj a)
  obtain ⟨dis,ah,ac,_,_,_,_⟩ := AnchorPairs.four_anchor_frontier G t q bad ef de df
  rw [ae] at ah ac
  obtain ⟨_,es⟩ := TwoEars.profile G t q bad
  have inE {u : V} (du : G.degree u=2) : u∈LowSample.twos G := mem_sdiff.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  have ears : E=LowSample.twos G := eq_of_subset_of_card_le (insert_subset (inE de) (singleton_subset_iff.mpr (inE df)))
    (by rw [show E.card=2 from card_pair ef]; exact es.le)
  have ed (v : V) (m : v∈E) : G.degree v=2 := (mem_insert.mp m).elim (fun h => h ▸ de) (fun h => mem_singleton.mp h ▸ df)
  have below {z : V} (zm : z∈E) : z∉high G := by intro hi; have := (mem_filter.mp hi).2; rw [ed z zm] at this; omega
  have low (a : V) : nbr G a (LowSample.twos G)≤1 := by
    have avoid : ¬G.Adj a e ∨ ¬G.Adj a f := by
      by_cases ae' : G.Adj a e
      · exact Or.inr (fun af => disjoint_left.mp dis ((G.mem_neighborFinset ..).mpr ae'.symm) ((G.mem_neighborFinset ..).mpr af.symm))
      · exact Or.inl ae'
    rw [←ears]; rcases avoid with h|h <;> simp [nbr,E,filter_insert,filter_singleton,h,ef] <;> split <;> simp
  have large (a : V) (am : a∈A) (aw : a≠w) : 4≤(row a).card := by
    have score := SparsePairs.anchor_score_gap G t q bad ef de df (ae.symm ▸ wa) ws a (ae.symm ▸ am) aw
    have cap := SparsePairs.link_budget G A ac am wa one (low a) true false (by simp) (by simp)
    simp only [aw,if_false,if_true,Bool.false_eq_true] at cap
    have cut : A.filter (G.Adj a)⊆A.erase a := fun z zm => mem_erase.mpr ⟨(mem_filter.mp zm).2.ne.symm,(mem_filter.mp zm).1⟩
    have cu := card_le_card cut; rw [card_erase_of_mem am,ac] at cu
    change nbr G a A≤3 at cu
    by_contra! small
    have few : (row a).card≤3 := by omega
    have c2 := Nat.choose_le_choose 2 few
    have mul := Nat.mul_le_mul few cu
    change trianglesAt G a≤1+1+((row a).card).choose 2+(row a).card*nbr G a A at cap
    rw [show (3:ℕ).choose 2=3 by decide] at c2; omega
  have into (a : V) (am : a∈A) : row a⊆H := fun z zm => mem_filter.mpr ⟨(mem_filter.mp zm).1,
    card_pos.mpr ⟨a,mem_filter.mpr ⟨am,(mem_filter.mp zm).2.symm⟩⟩⟩
  have apart (a : V) (aa : a∈A) (aw : a≠w) : Disjoint (row a) (row w) := disjoint_left.mpr (by
    intro z zm zw; have lo := priv z zw
    have hi := PinnedColor34.two G aw (mem_filter.mp zm).2.symm (mem_filter.mp zw).2.symm aa wa; omega)
  have hit (a : V) (aa : a∈A) (aw : a≠w) : ∃ z∈D,G.Adj a z := by
    let T := (A.erase w).erase a
    have am : a∈A.erase w := mem_erase.mpr ⟨aw,aa⟩
    have ts : T.card=2 := by dsimp [T]; rw [card_erase_of_mem am,card_erase_of_mem wa,ac]
    obtain ⟨b,bm⟩ := card_pos.mp (show 0<T.card by omega)
    obtain ⟨ba,bm⟩ := mem_erase.mp bm
    obtain ⟨bw,bb⟩ := mem_erase.mp bm
    by_contra! no
    have sep : Disjoint (row a) (row b) := disjoint_left.mpr (by
      intro z za zb; have two := PinnedColor34.two G ba (mem_filter.mp zb).2.symm (mem_filter.mp za).2.symm bb aa
      exact no z (mem_filter.mpr ⟨(mem_filter.mp za).1,two⟩) (mem_filter.mp za).2)
    have ct := card_le_card (union_subset (union_subset (into a aa) (into b bb)) (into w wa))
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨apart a aa aw,apart b bb bw⟩),card_union_of_disjoint sep] at ct
    change (row a).card+(row b).card+(row w).card≤H.card at ct
    have ha := large a aa aw; have hb := large b bb bw
    change (row w).card=2 at k2; change H.card=8 at eight; omega
  have incident {a : V} (aa : a∈A) : ∃u∈E,G.Adj a u := by
    rw [←ae] at aa
    exact (mem_union.mp aa).elim (fun h => ⟨e,mem_insert_self ..,((G.mem_neighborFinset ..).mp h).symm⟩)
      (fun h => ⟨f,mem_insert_of_mem (mem_singleton_self _),((G.mem_neighborFinset ..).mp h).symm⟩)
  obtain ⟨u,ue,wu⟩ := incident wa
  refine ⟨disjoint_left.mpr ?_,wa,⟨u,mem_union_left _ ue,wu⟩,?_,?_⟩
  · intro z za zm; rcases mem_union.mp zm with m|m
    · exact below m (ah za)
    · exact (mem_sdiff.mp (mem_filter.mp m).1).2 za
  · intro a aa aw; obtain ⟨z,zm,az⟩ := hit a aa aw
    obtain ⟨v,vm,av⟩ := incident aa
    exact PinnedColor34.two G (fun (h:v=z) => below vm (h ▸ (mem_sdiff.mp (mem_filter.mp zm).1).1)) av az (mem_union_left _ vm) (mem_union_right _ zm)
  · intro a am; rcases mem_union.mp am with m|d
    · have sub : G.neighborFinset a⊆A := (mem_insert.mp m).elim
        (fun h => h ▸ ae ▸ subset_union_left) (fun h => mem_singleton.mp h ▸ ae ▸ subset_union_right)
      have inc : G.neighborFinset a⊆A.filter (G.Adj a) := fun z zm => mem_filter.mpr ⟨sub zm,(G.mem_neighborFinset ..).mp zm⟩
      have c := card_le_card inc; rwa [card_neighborFinset_eq_degree,ed a m] at c
    · exact (mem_filter.mp d).2
end Graffiti384b.EightPins
#print axioms Graffiti384b.EightPins.boundary
