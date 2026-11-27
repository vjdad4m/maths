import PortChains180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals PairRepair
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A four-neighbor center with two mixed separated regions admits a
region indicator constant on every remainder edge, with exactly two
center neighbors of each value. -/
theorem two_port_regions (G : SimpleGraph V) (a b : V) (deg : G.degree a=4) (C D O : Finset V)
    (h : TwoRegions G a b C D O) (c : V→Bool) (lc : MixedAt G a C c) (rc : MixedAt G a D c) :
    ∃ s : V→Bool,(∀ x∈univ\({a,b}:Finset V),∀ y∈univ\({a,b}:Finset V),G.Adj x y → s x=s y) ∧
       ∀ t,(sideNeighbors G a s t).card=2 := by
  classical
  let s (v : V) := decide (v∈C)
  have closed {x y : V} (xc : x∈C) (yr : y∈univ\({a,b}:Finset V)) (ed : G.Adj x y) : y∈C := by
    rw [h.partition] at yr
    rcases mem_union.mp yr with cd|o
    · exact (mem_union.mp cd).resolve_right (fun yd => h.cross x xc y yd ed)
    · exact (h.out x (mem_union_left _ xc) y o ed).elim
  have mono (x : V) (xr : x∈univ\({a,b}:Finset V)) (y : V) (yr : y∈univ\({a,b}:Finset V))
      (e : G.Adj x y) : s x=s y := by
    exact decide_eq_decide.mpr ⟨fun xc => closed xc yr e,fun yc => closed yc xr e.symm⟩
  have two (S : Finset V) (t : Bool) (mixed : MixedAt G a S c) (val : ∀ w∈S,s w=t) :
      2≤(sideNeighbors G a s t).card := by
    obtain ⟨x,y,ax,ay,cx,cy,xm,ym,_⟩ := mixed
    have ne : x≠y := fun e => Bool.noConfusion (cx.symm.trans ((congrArg c e).trans cy))
    have sub : ({x,y}:Finset V)⊆sideNeighbors G a s t := insert_subset
      (mem_filter.mpr ⟨(G.mem_neighborFinset ..).mpr ax,val x xm⟩)
      (singleton_subset_iff.mpr (mem_filter.mpr ⟨(G.mem_neighborFinset ..).mpr ay,val y ym⟩))
    simpa only [card_pair ne] using card_le_card sub
  have l := two C true lc (fun x xm => by simp [s,xm])
  have d := two D false rc (fun x xm => by
    have no : x∉C := fun m => disjoint_left.mp h.apart m xm
    simp [s,no])
  have total := sides_sum G a s
  refine ⟨s,mono,fun t => ?_⟩;cases t <;> omega

/-- Three distinct neighbors cannot all belong to the same one of the
two regions, as witnessed by the common region indicator. -/
theorem no_three_ports (G : SimpleGraph V) (a : V) (s : V→Bool)
    (cap : ∀ t,(sideNeighbors G a s t).card=2) (u v w : V)
    (au : G.Adj a u) (av : G.Adj a v) (aw : G.Adj a w) (uv : u≠v) (uw : u≠w) (vw : v≠w)
    (suv : s u=s v) (svw : s v=s w) : False := by
  classical
  have ni : u∉({v,w}:Finset V) := by simp [uv,uw]
  have sub : ({u,v,w}:Finset V)⊆sideNeighbors G a s (s w) := insert_subset
    (mem_filter.mpr ⟨(G.mem_neighborFinset ..).mpr au,suv.trans svw⟩)
    (insert_subset (mem_filter.mpr ⟨(G.mem_neighborFinset ..).mpr av,svw⟩)
    (singleton_subset_iff.mpr (mem_filter.mpr ⟨(G.mem_neighborFinset ..).mpr aw,rfl⟩)))
  have h := card_le_card sub
  rw [card_insert_of_not_mem ni,card_pair vw,cap] at h;omega

#print axioms two_port_regions
#print axioms no_three_ports
end Minimal180.OppositeGain
