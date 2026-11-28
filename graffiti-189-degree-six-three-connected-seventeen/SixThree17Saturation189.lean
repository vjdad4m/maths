import SixThree17Shape189

namespace Graffiti189LongestPath.SixThreeSeventeen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree rotate_start_first_edge endpoint_is_flank_implies_first_pin)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.card_pinVertices
  Graffiti189LongestPath.OneSlack.cardinal_flankVertices
  Graffiti189LongestPath.OneSlack.mem_omittedStar Graffiti189LongestPath.OneSlack.mem_external
  Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary
  Graffiti189LongestPath.OneSlack.exclusive_gap_pin from OneSlack189
open private Graffiti189LongestPath.PinRun.pins_count from PinRunSeparator189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem high_saturation (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤17) {a b : V} {p : G.Walk a b}
    (hp : IsLongest p) {x : V} (hx : x∉p.support) (dx : 6≤G.degree x) :
    (Pins p x).card=3 ∧ PairedPins p x=∅ ∧ DistanceTwo G x=FlankVertices p x := by
  classical
  obtain ⟨len,oc,xp,xAll⟩ := high_pin_shape hc conn cap degree ord hp hx dx
  obtain ⟨y,hy,xy,dy⟩ := other_high_omitted degree hx oc
  have adj := xAll y hy xy
  have yp := (high_pin_shape hc conn cap degree ord hp hy dy).2.2.1
  let E := (PairedPins p x).image p.getVert
  let F := PinVertices p y
  let B := External G (OmittedStar p x)
  have es : E⊆B := by
    intro w ww
    obtain ⟨j,jm,rfl⟩ := mem_image.mp ww
    exact Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary hx
      (mem_image.mpr ⟨j,(mem_filter.mp jm).1,rfl⟩)
  have fs : F⊆B := by
    intro w ww
    obtain ⟨j,jm,rfl⟩ := mem_image.mp ww
    exact Graffiti189LongestPath.OneSlack.mem_external.mpr ⟨fun h=>
      (Graffiti189LongestPath.OneSlack.mem_omittedStar.mp h).1 (p.getVert_mem_support j),
      y,Graffiti189LongestPath.OneSlack.mem_omittedStar.mpr ⟨hy,.inr adj⟩,
      (Graffiti189LongestPath.pin_data jm).2⟩
  have dis : Disjoint E F := by
    apply disjoint_left.mpr
    intro w we wf
    obtain ⟨i,im,ie⟩ := mem_image.mp we
    obtain ⟨j,jm,je⟩ := mem_image.mp wf
    have eq := hp.1.getVert_injOn
      (Graffiti189LongestPath.pin_data (mem_filter.mp im).1).1.le
      (Graffiti189LongestPath.pin_data jm).1.le (ie.trans je.symm)
    subst j
    exact Graffiti189LongestPath.OneSlack.exclusive_gap_pin hp hx hy adj im
      (Graffiti189LongestPath.pin_data jm).2
  have ec : E.card=(PairedPins p x).card := by
    apply card_image_iff.mpr
    intro i im j jm e
    exact hp.1.getVert_injOn
      (Graffiti189LongestPath.pin_data (mem_filter.mp im).1).1.le
      (Graffiti189LongestPath.pin_data (mem_filter.mp jm).1).1.le e
  have lower := card_le_card (union_subset es fs)
  rw [card_union_of_disjoint dis,ec] at lower
  change (PairedPins p x).card+(PinVertices p y).card≤B.card at lower
  rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp,yp] at lower
  have balance := boundary_flank_count hc hp hx
  rw [flank_count_exact hp hx] at balance
  change B.card+((Pins p x).card+(FirstPins p x).card)≤
    (DistanceTwo G x).card+(Pins p x).card at balance
  have upper := distanceTwo_le_of_even 6 x (cap x)
  have runs := Graffiti189LongestPath.PinRun.pins_count p x
  have both : PairedPins p x=∅ ∧ (FirstPins p x).card=(Pins p x).card := by
    refine runs.resolve_right (fun bad=>by omega)
  have sf : FlankVertices p x⊆DistanceTwo G x := fun _ m=>
    (mem_sdiff.mp (flanks_outside_boundary hc hp hx m)).1
  have fv := Graffiti189LongestPath.OneSlack.cardinal_flankVertices (x:=x) hp
  rw [flank_count_exact hp hx,both.2,xp] at fv
  exact ⟨xp,both.1,(eq_of_subset_of_card_le sf (by omega)).symm⟩

theorem high_pin_no_start_chord (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤17) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x∉p.support) (dx : 6≤G.degree x) {i : ℕ} (hi : i∈Pins p x) (imin : 2≤i) :
    ¬G.Adj a (p.getVert i) := by
  classical
  intro edge
  have il := (Graffiti189LongestPath.pin_data hi).1
  have sub : i-1+1=i := by omega
  obtain ⟨q,hq,same,first⟩ := rotate_start_first_edge hp (i-1) (by omega) (by omega)
    (by simpa only [sub] using edge)
  have hxo : x∉q.support := fun h=>hx ((same x).mpr h)
  have old : p.getVert (i-1)∈FlankVertices p x :=
    mem_image.mpr ⟨i-1,mem_union_left _ (mem_image.mpr ⟨i,hi,rfl⟩),rfl⟩
  have inD := (mem_sdiff.mp (flanks_outside_boundary hc hp hx old)).1
  have sat := (high_saturation hc conn cap degree ord hq hxo dx).2.2
  have np := endpoint_is_flank_implies_first_pin hq hxo (sat ▸ inD)
  have edge' := (Graffiti189LongestPath.pin_data np).2
  rw [first] at edge'
  have fi : i-1-1∈Pins p x := mem_filter.mpr ⟨mem_range.mpr (by omega),edge'⟩
  have eq : i-1-1+2=i := by omega
  have paired : i∈PairedPins p x := mem_filter.mpr ⟨hi,i-1-1,fi,.inl eq⟩
  simp [(high_saturation hc conn cap degree ord hp hx dx).2.1] at paired

#print axioms high_saturation
#print axioms high_pin_no_start_chord
end Graffiti189LongestPath.SixThreeSeventeen
