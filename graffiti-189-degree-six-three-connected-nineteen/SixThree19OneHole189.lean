import SixThree18Final189

namespace Graffiti189LongestPath.SixThreeNineteen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeSixteen (ConnThree)
open Graffiti189LongestPath.SixThreeEighteen (LM RM left_right_disjoint Omit mem_Omit omit_add_length high_filter_card)
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.pin_pos Graffiti189LongestPath.Rigidity.reverse_longest
  Graffiti189LongestPath.Rigidity.card_leftMarks Graffiti189LongestPath.Rigidity.card_rightMarks from Rigidity189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem Graffiti189LongestPath.OneSlack.card_pinVertices
  Graffiti189LongestPath.OneSlack.nonconsecutive_boundary
  Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def Holes {a b : V} (p : G.Walk a b) : Finset ℕ := range p.length \ (LM p∪RM p)

theorem holes_card_le_one {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length≤13)
    (da : 6≤G.degree a) (db : 6≤G.degree b) {x : V} (hx : x∉p.support)
    {i : ℕ} (ip : i∈Pins p x) : (Holes p).card≤1 := by
  have sub : LM p∪RM p⊆range p.length := union_subset (filter_subset ..) (filter_subset ..)
  unfold Holes
  rw [card_sdiff sub,card_union_of_disjoint (left_right_disjoint hp hx ip),card_range,
    Graffiti189LongestPath.Rigidity.card_leftMarks hp,Graffiti189LongestPath.Rigidity.card_rightMarks hp]
  omega

theorem missed_start_hole {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x∉p.support) {i : ℕ} (ip : i∈Pins p x)
    (no : ¬G.Adj a (p.getVert i)) : i-1∈Holes p := by
  have i0 := Graffiti189LongestPath.Rigidity.pin_pos hp hx ip
  have il := (Graffiti189LongestPath.pin_data ip).1
  refine mem_sdiff.mpr ⟨mem_range.mpr (by omega),?_⟩
  intro m
  rcases mem_union.mp m with l|r
  · have e := (mem_filter.mp l).2
    rw [show i-1+1=i by omega] at e
    exact no e
  exact end_not_adj_pin_predecessor hp hx ip (mem_filter.mp r).2

theorem missed_end_hole {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x∉p.support) {i : ℕ} (ip : i∈Pins p x)
    (no : ¬G.Adj b (p.getVert i)) : i∈Holes p := by
  refine mem_sdiff.mpr ⟨(mem_filter.mp ip).1,?_⟩
  intro m
  exact (mem_union.mp m).elim
    (fun l=>start_not_adj_pin_successor hp hx ip (mem_filter.mp l).2)
    (fun r=>no (mem_filter.mp r).2)

theorem pin_indices_not_consecutive {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x∉p.support) {i : ℕ} (ip : i∈Pins p x) :
    i+1∉Pins p x := by
  intro jp
  have bi := Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary hx (mem_image.mpr ⟨i,ip,rfl⟩)
  have bj := Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary hx (mem_image.mpr ⟨i+1,jp,rfl⟩)
  exact Graffiti189LongestPath.OneSlack.nonconsecutive_boundary hp hx
    (Graffiti189LongestPath.pin_data ip).1 bi bj

def SeesPort {a b : V} (p : G.Walk a b) (x z : V) : Prop :=
  ∃ w∈p.support,G.Adj x w ∧ G.Adj z w

def SeesEveryPort {a b : V} (p : G.Walk a b) (x z : V) : Prop :=
  ∀ w∈p.support,G.Adj x w → G.Adj z w

theorem two_pins_endpoint_routes {a b : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length≤13)
    (da : 6≤G.degree a) (db : 6≤G.degree b) {x : V} (hx : x∉p.support)
    (xp : 2≤(Pins p x).card) :
    SeesPort p x a ∧ SeesPort p x b ∧ (SeesEveryPort p x a ∨ SeesEveryPort p x b) := by
  classical
  obtain ⟨i,ip⟩ : (Pins p x).Nonempty := card_pos.mp (by omega)
  have small := holes_card_le_one hp len da db hx ip
  have someLeft : SeesPort p x a := by
    by_contra no
    have l (j : ℕ) (jp : j∈Pins p x) : j-1∈Holes p :=
      missed_start_hole hp hx jp (fun e=>no ⟨p.getVert j,p.getVert_mem_support j,
        (Graffiti189LongestPath.pin_data jp).2,e⟩)
    have pinSmall : (Pins p x).card≤1 := card_le_one.mpr (fun j jp k kp=>by
      have eq := card_le_one.mp small (j-1) (l j jp) (k-1) (l k kp)
      have j0 := Graffiti189LongestPath.Rigidity.pin_pos hp hx jp
      have k0 := Graffiti189LongestPath.Rigidity.pin_pos hp hx kp
      omega)
    omega
  have someRight : SeesPort p x b := by
    by_contra no
    have l (j : ℕ) (jp : j∈Pins p x) : j∈Holes p :=
      missed_end_hole hp hx jp (fun e=>no ⟨p.getVert j,p.getVert_mem_support j,
        (Graffiti189LongestPath.pin_data jp).2,e⟩)
    have pinSmall : (Pins p x).card≤1 := card_le_one.mpr
      (fun j jp k kp=>card_le_one.mp small j (l j jp) k (l k kp))
    omega
  refine ⟨someLeft,someRight,?_⟩
  by_cases l : SeesEveryPort p x a
  · exact .inl l
  right
  have missing : ∃ w∈p.support,G.Adj x w ∧ ¬G.Adj a w := by
    by_contra no
    apply l
    intro w wm xw
    apply Classical.byContradiction
    intro e
    exact no ⟨w,wm,xw,e⟩
  obtain ⟨w,wm,xw,aw⟩ := missing
  obtain ⟨j,jp,je⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hx wm xw
  intro z zm xz
  by_contra bz
  obtain ⟨k,kp,ke⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hx zm xz
  have mh := missed_start_hole hp hx jp (by simpa only [je] using aw)
  have nh := missed_end_hole hp hx kp (by simpa only [ke] using bz)
  have eq := card_le_one.mp small (j-1) mh k nh
  have j0 := Graffiti189LongestPath.Rigidity.pin_pos hp hx jp
  have e : k+1=j := by omega
  exact pin_indices_not_consecutive hp hx kp (e.symm ▸ jp)

theorem pin_card_same_support {a b c d : V} {p : G.Walk a b} {q : G.Walk c d}
    (hp : IsLongest p) (hq : IsLongest q) (same : ∀ v,v∈p.support ↔ v∈q.support)
    {x : V} (hx : x∉p.support) : (Pins p x).card=(Pins q x).card := by
  have xq : x∉q.support := fun h=>hx ((same x).mpr h)
  have eq : PinVertices p x=PinVertices q x := by
    ext v
    constructor
    · intro h
      obtain ⟨i,ip,iv⟩ := mem_image.mp h
      obtain ⟨j,jp,jv⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hq xq
        ((same v).mp (iv ▸ p.getVert_mem_support i)) (iv ▸ (Graffiti189LongestPath.pin_data ip).2)
      exact mem_image.mpr ⟨j,jp,jv⟩
    intro h
    obtain ⟨j,jp,jv⟩ := mem_image.mp h
    obtain ⟨i,ip,iv⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp hx
      ((same v).mpr (jv ▸ q.getVert_mem_support j)) (jv ▸ (Graffiti189LongestPath.pin_data jp).2)
    exact mem_image.mpr ⟨i,ip,iv⟩
  have n := congrArg Finset.card eq
  rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp,Graffiti189LongestPath.OneSlack.card_pinVertices hq] at n
  exact n

theorem left_candidate_sees_port {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length≤13) (db : 6≤G.degree b) {x : V} (hx : x∉p.support)
    (xp : 2≤(Pins p x).card) {j : ℕ} (jl : j∈LM p) (dj : 6≤G.degree (p.getVert j)) :
    SeesPort p x (p.getVert j) := by
  have n := mem_range.mp (mem_filter.mp jl).1
  obtain ⟨q,hq,same,ql,_,_⟩ := rotate_start hp j n (mem_filter.mp jl).2
  have xq : x∉q.support := fun h=>hx ((same x).mpr h)
  have qp := pin_card_same_support hp hq same hx
  obtain ⟨w,wm,xw,zw⟩ := (two_pins_endpoint_routes hq (ql ▸ len) dj db xq (qp ▸ xp)).1
  exact ⟨w,(same w).mpr wm,xw,zw⟩

theorem right_candidate_sees_port {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (len : p.length≤13) (da : 6≤G.degree a) {x : V} (hx : x∉p.support)
    (xp : 2≤(Pins p x).card) {j : ℕ} (jr : j∈RM p) (dj : 6≤G.degree (p.getVert (j+1))) :
    SeesPort p x (p.getVert (j+1)) := by
  have jl := mem_range.mp (mem_filter.mp jr).1
  let t := p.length-(j+1)
  have e : p.reverse.getVert t=p.getVert (j+1) := by rw [getVert_reverse]; congr 1; dsimp only [t]; omega
  have ej : p.reverse.getVert (t+1)=p.getVert j := by rw [getVert_reverse]; congr 1; dsimp only [t]; omega
  have rj : t∈LM p.reverse := mem_filter.mpr
    ⟨mem_range.mpr (by rw [length_reverse]; dsimp only [t]; omega),by rw [ej]; exact (mem_filter.mp jr).2⟩
  have same : ∀ v,v∈p.support ↔ v∈p.reverse.support := fun v=>by simp
  have hq := Graffiti189LongestPath.Rigidity.reverse_longest hp
  have qp := pin_card_same_support hp hq same hx
  obtain ⟨w,wm,xw,zw⟩ := left_candidate_sees_port hq (by simpa using len) da
    (by simpa using hx) (qp ▸ xp) rj (by rwa [e])
  exact ⟨w,(same w).mpr wm,xw,by simpa only [e] using zw⟩

#print axioms two_pins_endpoint_routes
#print axioms right_candidate_sees_port
end Graffiti189LongestPath.SixThreeNineteen
