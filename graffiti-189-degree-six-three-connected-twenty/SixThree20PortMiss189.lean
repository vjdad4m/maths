import SixThree20ThirteenClose189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeEighteen (Omit mem_Omit)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem
  Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def PortSet {a b : V} (p : G.Walk a b) (H : Finset V) : Finset V := (Sites p H).image p.getVert

def Misses (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (v : V) : Finset V :=
  U.filter (fun u=>¬G.Adj v u)

theorem mem_portSet {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {H : Finset V} (off : ∀ x∈H,x∉p.support) {v : V} :
    v∈PortSet p H ↔ v∈p.support ∧ ∃ x∈H,G.Adj x v := by
  constructor
  · intro m
    obtain ⟨i,im,ie⟩ := mem_image.mp m
    obtain ⟨ir,x,xm,xi⟩ := mem_filter.mp im
    exact ⟨ie ▸ p.getVert_mem_support i,x,xm,ie ▸ xi⟩
  rintro ⟨on,x,xm,xv⟩
  obtain ⟨i,ip,ie⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp (off x xm) on xv
  exact mem_image.mpr ⟨i,mem_filter.mpr ⟨(mem_filter.mp ip).1,x,xm,(Graffiti189LongestPath.pin_data ip).2⟩,ie⟩

theorem port_set_nonempty_iff_sites {a b : V} {p : G.Walk a b} {H : Finset V} :
    (PortSet p H).Nonempty ↔ (Sites p H).Nonempty := by
  constructor
  · rintro ⟨v,vm⟩
    obtain ⟨i,im,_⟩ := mem_image.mp vm
    exact ⟨i,im⟩
  rintro ⟨i,im⟩
  exact ⟨p.getVert i,mem_image.mpr ⟨i,im,rfl⟩⟩

theorem same_support_omit {a b c d : V} {p : G.Walk a b} {q : G.Walk c d}
    (same : ∀ v,v∈p.support ↔ v∈q.support) : Omit p=Omit q := by
  ext v
  simp only [mem_Omit,same v]

theorem same_support_high_omit {a b c d : V} {p : G.Walk a b} {q : G.Walk c d}
    (same : ∀ v,v∈p.support ↔ v∈q.support) : HighOmit p=HighOmit q := by
  unfold HighOmit
  rw [same_support_omit same]

theorem same_support_port_set {a b c d : V} {p : G.Walk a b} {q : G.Walk c d}
    (hp : IsLongest p) (hq : IsLongest q) (same : ∀ v,v∈p.support ↔ v∈q.support)
    {H : Finset V} (off : ∀ x∈H,x∉p.support) : PortSet p H=PortSet q H := by
  ext v
  rw [mem_portSet hp off,mem_portSet hq (fun x xm h=>off x xm ((same x).mpr h)),same v]

theorem pin_vertices_sub_ports {a b : V} {p : G.Walk a b} {H : Finset V} {x : V}
    (xm : x∈H) : PinVertices p x⊆PortSet p H := by
  intro y ym
  obtain ⟨i,im,ie⟩ := mem_image.mp ym
  exact mem_image.mpr ⟨i,mem_filter.mpr ⟨(mem_filter.mp im).1,x,xm,(Graffiti189LongestPath.pin_data im).2⟩,ie⟩

theorem miss_budget_vertices {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : Finset V) (off : ∀ x∈H,x∉p.support) (non : (PortSet p H).Nonempty)
    (sep : ∀ i∈Sites p H,i+1∉Sites p H) :
    (Misses G (PortSet p H) a).card+(Misses G (PortSet p H) b).card+
      (G.degree a+G.degree b)≤p.length := by
  classical
  let I := Sites p H
  have mapCard (u : V) : (Misses G (PortSet p H) u).card=(I.filter (fun i=>¬G.Adj u (p.getVert i))).card := by
    have eq : Misses G (PortSet p H) u=(I.filter (fun i=>¬G.Adj u (p.getVert i))).image p.getVert := by
      ext v
      constructor
      · intro h
        obtain ⟨m,no⟩ := mem_filter.mp h
        obtain ⟨i,im,ie⟩ := mem_image.mp m
        exact mem_image.mpr ⟨i,mem_filter.mpr ⟨im,by simpa only [ie] using no⟩,ie⟩
      intro h
      obtain ⟨i,im,ie⟩ := mem_image.mp h
      exact mem_filter.mpr ⟨mem_image.mpr ⟨i,(mem_filter.mp im).1,ie⟩,ie ▸ (mem_filter.mp im).2⟩
    rw [eq]
    apply card_image_iff.mpr
    intro i ip j jp e
    exact hp.1.getVert_injOn (mem_range.mp (mem_filter.mp (mem_filter.mp ip).1).1).le
      (mem_range.mp (mem_filter.mp (mem_filter.mp jp).1).1).le e
  rw [mapCard a,mapCard b]
  exact two_end_miss_budget hp I (port_set_nonempty_iff_sites.mp non)
    (fun i im=>by
      obtain ⟨ir,x,xm,adj⟩ := mem_filter.mp im
      exact ⟨x,off x xm,mem_filter.mpr ⟨ir,adj⟩⟩) sep

theorem miss_card_positive_of_not_see {U : Finset V} {v u : V}
    (um : u∈U) (no : ¬G.Adj v u) : 1≤(Misses G U v).card :=
  card_pos.mpr ⟨u,mem_filter.mpr ⟨um,no⟩⟩

theorem sees_some_from_pin_miss_count {a b : V} {p : G.Walk a b} {U : Finset V} {x v : V}
    (sub : PinVertices p x⊆U) (more : (Misses G U v).card<(PinVertices p x).card) :
    Graffiti189LongestPath.SixThreeNineteen.SeesPort p x v := by
  classical
  by_contra no
  have mes : PinVertices p x⊆Misses G U v := by
    intro y ym
    apply mem_filter.mpr
    refine ⟨sub ym,?_⟩
    intro e
    obtain ⟨i,im,ie⟩ := mem_image.mp ym
    exact no ⟨y,ie ▸ p.getVert_mem_support i,ie ▸ (Graffiti189LongestPath.pin_data im).2,e⟩
  exact (Nat.not_le_of_lt more) (card_le_card mes)

#print axioms miss_budget_vertices
end Graffiti189LongestPath.SixThreeTwenty
