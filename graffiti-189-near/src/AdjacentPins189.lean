import Rigidity189
import PinDistanceTwoGeneral189
import FatPorter189

namespace Graffiti189LongestPath.AdjacentPins
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
private theorem no_endpoints {x a b : V} {p : G.Walk a b}
    (hp : IsLongest p) (hx : x ∉ p.support) :
    ¬G.Adj x a ∧ ¬G.Adj x b := by
  constructor
  · intro h
    have hle := hp.2 x b (.cons h p) (hp.1.cons hx)
    simp at hle
  · intro h
    have hq : (Walk.cons h p.reverse).reverse.IsPath :=
      (hp.1.reverse.cons (by simpa using hx)).reverse
    have hle := hp.2 a x _ hq
    simp at hle

private theorem dist_two {a b c : V} (hconn : G.Connected)
    (hac : a ≠ c) (hna : ¬G.Adj a c) (hab : G.Adj a b) (hbc : G.Adj b c) :
    G.dist a c = 2 := by
  have hu := hconn.one_lt_dist_of_ne_of_not_adj hac hna
  have hl := G.dist_le (Walk.cons hab (Walk.cons hbc .nil))
  simp at hl
  omega



variable [Fintype V]
private theorem mem_distanceTwo {x y : V} :
    y ∈ DistanceTwo G x ↔ G.dist x y = 2 := by
  classical
  simp [DistanceTwo]



variable [DecidableEq V] [DecidableRel G.Adj]
omit [Fintype V] [DecidableEq V] in
private theorem pin_data {a b : V} {p : G.Walk a b} {x : V} {i : ℕ}
    (hi : i ∈ Pins p x) : i < p.length ∧ G.Adj x (p.getVert i) :=
  ⟨Finset.mem_range.mp (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

omit [Fintype V] [DecidableEq V] in
private theorem pin_of_neighbor_mem {a b x y : V} {p : G.Walk a b}
    (hp : IsLongest p) (hx : x ∉ p.support) (hy : y ∈ p.support) (e : G.Adj x y) :
    ∃ i ∈ Pins p x, p.getVert i = y := by
  obtain ⟨i,he,hile⟩ := mem_support_iff_exists_getVert.mp hy
  have hi : i < p.length := by
    by_contra! h
    have ee : i = p.length := by omega
    rw [ee,getVert_length] at he
    exact (no_endpoints hp hx).2 (he.symm ▸ e)
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,he.symm ▸ e⟩,he⟩


private lemma mem_omittedStar {a b x z : V} {p : G.Walk a b} :
    z ∈ OmittedStar p x ↔ z ∉ p.support ∧ (z = x ∨ G.Adj x z) := by simp [OmittedStar]

private lemma mem_external {A : Finset V} {z : V} :
    z ∈ External G A ↔ z ∉ A ∧ ∃ w ∈ A, G.Adj w z := by simp [External]

private theorem pin_neighbors_unique (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b x s t : V} {p : G.Walk a b} (hp : IsLongest p)
    (hx : x ∉ p.support) (hs : s ∈ p.support) (ht : t ∈ p.support)
    (as : G.Adj x s) (at' : G.Adj x t) : s=t := by
  obtain ⟨i,hi,ei⟩ := pin_of_neighbor_mem hp hx hs as
  obtain ⟨j,hj,ej⟩ := pin_of_neighbor_mem hp hx ht at'
  have eq := unique_omitted_pin_at_near_connectivity hc k bound conn degree hp hx i hi j hj
  subst j
  exact ei.symm.trans ej

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private lemma short_walk_cases {x y : V} (q : G.Walk x y) (len : q.length ≤ 3) :
    x=y ∨ G.Adj x y ∨ (∃ u, G.Adj x u ∧ G.Adj u y) ∨
      (∃ u v, G.Adj x u ∧ G.Adj u v ∧ G.Adj v y) := by
  match q with
  | .nil => exact Or.inl rfl
  | .cons e .nil => exact Or.inr (Or.inl e)
  | .cons (v:=u) e (.cons f .nil) => exact Or.inr (Or.inr (Or.inl ⟨u,e,f⟩))
  | .cons (v:=u) e (.cons (v:=v) f (.cons g .nil)) =>
    exact Or.inr (Or.inr (Or.inr ⟨u,v,e,f,g⟩))
  | .cons _ (.cons _ (.cons _ (.cons _ q))) => simp only [length_cons] at len; omega


variable {a b : V} {p : G.Walk a b}

/-- All vertices on the path with at least one omitted neighbor. -/
def PathPins {a b : V} (p : G.Walk a b) : Finset V :=
  p.support.toFinset.filter fun s => ∃ x ∉ p.support, G.Adj x s

private lemma mem_pathPins {s : V} :
    s ∈ PathPins p ↔ s ∈ p.support ∧ ∃ x ∉ p.support, G.Adj x s := by
  simp [PathPins]

private def AroundPins {a b : V} (p : G.Walk a b) : Finset ℕ :=
  (range p.length).filter fun j => p.getVert j ∈ PathPins p

private def FlanksOf {a b : V} (p : G.Walk a b) (i : ℕ) : Finset V :=
  {p.getVert (i-1), p.getVert (i+1)}

private lemma around_data {j : ℕ} (hj : j ∈ AroundPins p) :
    j < p.length ∧ p.getVert j ∈ PathPins p :=
  ⟨mem_range.mp (mem_filter.mp hj).1,(mem_filter.mp hj).2⟩

private lemma card_around (hp : IsLongest p) : (AroundPins p).card = (PathPins p).card := by
  have eq : (AroundPins p).image p.getVert = PathPins p := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
      exact (around_data hi).2
    · intro hz
      obtain ⟨zs,x,hx,e⟩ := mem_pathPins.mp hz
      obtain ⟨i,hi,ei⟩ := pin_of_neighbor_mem hp hx zs e
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨(mem_filter.mp hi).1,ei.symm ▸ hz⟩,ei⟩
  have cc : ((AroundPins p).image p.getVert).card = (AroundPins p).card := by
    apply card_image_iff.mpr
    intro i hi j hj eq
    exact hp.1.getVert_injOn (around_data hi).1.le (around_data hj).1.le eq
  rw [eq] at cc
  exact cc.symm

/-- Coverage by the pin set and both flanks for every pin. -/
private def PinPlusFlanks {a b : V} (p : G.Walk a b) : Finset V :=
  PathPins p ∪ (AroundPins p).biUnion (FlanksOf p)

private lemma cover_card (hp : IsLongest p) :
    (PinPlusFlanks p).card ≤ 3*(PathPins p).card := by
  have each (i : ℕ) (_h : i ∈ AroundPins p) : (FlanksOf p i).card ≤ 2 := by
    have c := card_insert_le (p.getVert (i-1)) ({p.getVert (i+1)} : Finset V)
    simpa [FlanksOf] using c
  have c₁ := card_union_le (PathPins p) ((AroundPins p).biUnion (FlanksOf p))
  have c₂ := card_biUnion_le_card_mul (AroundPins p) (FlanksOf p) 2 each
  rw [card_around hp] at c₂
  unfold PinPlusFlanks
  omega

private theorem omitted_actual_component (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p) {x : V} (hx : x ∉ p.support) :
    ∃ H : OmittedComponent p, ∀ y, y ∈ H.vertices ↔ y ∉ p.support := by
  classical
  let U : Set V := {z | z ∉ p.support}
  let Q := G.induce U
  have con : Q.Connected := omitted_complement_connected hc k k₂ bound conn degree hp hx
  let H := (univ : Finset V).filter fun y => y ∉ p.support
  have MH (y : V) : y ∈ H ↔ y ∉ p.support := by simp [H]
  have joined (y : V) (hy : y ∈ H) (z : V) (hz : z ∈ H) :
      ∃ q : G.Walk y z, q.IsPath ∧ ∀ w ∈ q.support, w ∈ H := by
    obtain ⟨q,qp⟩ := (con ⟨y,(MH y).mp hy⟩ ⟨z,(MH z).mp hz⟩).exists_isPath
    let f : Q →g G := ⟨Subtype.val,fun e => e⟩
    refine ⟨q.map f,map_isPath_of_injective Subtype.val_injective qp,?_⟩
    intro w hw
    rw [support_map] at hw
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hw
    exact (MH (f w)).mpr w.prop
  refine ⟨⟨H,⟨x,(MH x).mpr hx⟩,fun y hy => (MH y).mp hy,?_,joined⟩,MH⟩
  intro y hy z hz e
  by_contra h
  exact hz ((MH z).mpr h)

private theorem flank_disj_of_two (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p) {x y : V} (hx : x ∉ p.support) (hy : y ∉ p.support)
    {i j : ℕ} (hi : i ∈ Pins p x) (hj : j ∈ Pins p y) (ij : i ≠ j) :
    Disjoint (FlanksOf p i) (FlanksOf p j) := by
  classical
  obtain ⟨H,hH⟩ := omitted_actual_component hc k k₂ bound conn degree hp hx
  have xy : x ≠ y := by
    intro e
    subst y
    exact ij (unique_omitted_pin_at_near_connectivity hc k bound conn degree hp hx i hi j hj)
  have steps (x y : V) (hx : x∈H.vertices) (hy : y∈H.vertices) (xy : x≠y)
      (i j : ℕ) (hi : i∈Pins p x) (hj : j∈Pins p y) (ij : i<j) : i+3≤j := by
    obtain ⟨w,hwp,hs⟩ := H.joined x hx y hy
    have wp : 0<w.length := by cases w with
      | nil => exact (xy rfl).elim
      | cons e p => simp
    exact gap_three_of_linked_pins hp hi hj ij w hwp wp (fun z hz => H.off z (hs z hz))
  have gap : i+3≤j ∨ j+3≤i := by
    rcases lt_or_gt_of_ne ij with l|l
    · exact Or.inl (steps x y ((hH x).mpr hx) ((hH y).mpr hy) xy i j hi hj l)
    · exact Or.inr (steps y x ((hH y).mpr hy) ((hH x).mpr hx) xy.symm j i hj hi l)
  rw [disjoint_left]
  intro z hz hw
  have unpack {m : ℕ} (hz : z ∈ FlanksOf p m) :
      ∃ r, (r=m-1 ∨ r=m+1) ∧ z=p.getVert r := by
    rcases mem_insert.mp hz with e|e
    · exact ⟨_,Or.inl rfl,e⟩
    · exact ⟨_,Or.inr rfl,mem_singleton.mp e⟩
  obtain ⟨r,hr,er⟩ := unpack hz
  obtain ⟨s,hs,es⟩ := unpack hw
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  have eq := hp.1.getVert_injOn (show r ≤ p.length by omega) (show s ≤ p.length by omega) (er.symm.trans es)
  omega

#print axioms flank_disj_of_two

private theorem pin_not_flank_of_other (hp : IsLongest p) (H : OmittedComponent p)
    (hc : G.Connected) (k : ℕ) (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {x y : V} (hx : x ∈ H.vertices) (hy : y ∈ H.vertices)
    {i j : ℕ} (hi : i ∈ Pins p x) (hj : j ∈ Pins p y) (ij : i≠j) :
    p.getVert j ∉ FlanksOf p i := by
  have apart {x y : V} (hx : x∈H.vertices) (hy : y∈H.vertices) {i j : ℕ}
      (hi : i∈Pins p x) (hj : j∈Pins p y) (ij : i<j) : i+3≤j := by
    have xy : x ≠ y := by
      intro e
      subst y
      exact (Nat.ne_of_lt ij) (unique_omitted_pin_at_near_connectivity hc k bound conn degree
        hp (H.off x hx) i hi j hj)
    obtain ⟨q,hq,hs⟩ := H.joined x hx y hy
    have pos : 0<q.length := by cases q with
      | nil => exact (xy rfl).elim
      | cons e q => simp
    exact gap_three_of_linked_pins hp hi hj ij q hq pos (fun z hz => H.off z (hs z hz))
  have gap : i+3≤j ∨ j+3≤i := by
    rcases lt_or_gt_of_ne ij with l|l
    · exact Or.inl (apart hx hy hi hj l)
    · exact Or.inr (apart hy hx hj hi l)
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  have clash {n : ℕ} (hn : n=i-1 ∨ n=i+1) (eq : p.getVert j = p.getVert n) : False := by
    have e := hp.1.getVert_injOn jl.le (show n≤p.length by omega) eq
    omega
  intro h
  rcases mem_insert.mp h with e|e
  · exact clash (Or.inl rfl) e
  · exact clash (Or.inr rfl) (mem_singleton.mp e)

private theorem chord_lifts_or_flank (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p) {x z : V} (hx : x ∉ p.support) (zs : z ∈ p.support)
    {i : ℕ} (hi : i ∈ Pins p x) (edge : G.Adj (p.getVert i) z) :
    z ∈ FlanksOf p i ∨ ∃ y ∉ p.support, G.Adj x y ∧ G.Adj y z := by
  classical
  have nxz : ¬G.Adj x z := fun e =>
    edge.ne (pin_neighbors_unique hc k bound conn degree hp hx (p.getVert_mem_support i)
      zs (pin_data hi).2 e)
  have xz : x ≠ z := fun e => hx (e.symm ▸ zs)
  have d := mem_distanceTwo.mpr (dist_two hc xz nxz (pin_data hi).2 edge)
  let B := External G (OmittedStar p x)
  by_cases inB : z ∈ B
  · obtain ⟨_,y,hy,ey⟩ := mem_external.mp inB
    obtain ⟨yoff,eq|adj⟩ := mem_omittedStar.mp hy
    · exact (nxz (eq ▸ ey)).elim
    · exact Or.inr ⟨y,yoff,adj,ey⟩
  · have hf := rigid_flanks hc k bound conn degree hp hx hi
    left
    change z ∈ ({p.getVert (i-1),p.getVert (i+1)} : Finset V)
    rw [←hf]
    exact mem_sdiff.mpr ⟨d,inB⟩

private theorem chord_lifts (hc : G.Connected) (k : ℕ)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p) (H : OmittedComponent p) {x y : V}
    (hx : x ∈ H.vertices) (hy : y ∈ H.vertices) {i j : ℕ} (hi : i ∈ Pins p x) (hj : j ∈ Pins p y)
    (adj : G.Adj (p.getVert i) (p.getVert j)) :
    ∃ z ∉ p.support, G.Adj x z ∧ G.Adj z (p.getVert j) := by
  have ij : i ≠ j := fun e => adj.ne (congrArg p.getVert e)
  have h := chord_lifts_or_flank hc k bound conn degree hp (H.off x hx)
    (p.getVert_mem_support j) hi adj
  exact h.resolve_left (pin_not_flank_of_other hp H hc k bound conn degree hx hy hi hj ij)

/-- Starting at any active omitted vertex, every different pin can be
reached through one or two edges of the omitted graph, followed by a pin edge. -/
theorem reach_different_pin (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p) {x y : V} (hx : x ∉ p.support) (hy : y ∉ p.support)
    {i j : ℕ} (hi : i ∈ Pins p x) (hj : j ∈ Pins p y) (ij : i≠j) :
    (∃ u ∉ p.support, G.Adj x u ∧ G.Adj u (p.getVert j)) ∨
      (∃ u ∉ p.support, ∃ v ∉ p.support, G.Adj x u ∧ G.Adj u v ∧ G.Adj v (p.getVert j)) := by
  classical
  let s := p.getVert i
  let t := p.getVert j
  have ss : s ∈ p.support := p.getVert_mem_support _
  have ts : t ∈ p.support := p.getVert_mem_support _
  have st : s≠t := fun e => ij (hp.1.getVert_injOn (pin_data hi).1.le (pin_data hj).1.le e)
  have xs : G.Adj x s := (pin_data hi).2
  obtain ⟨H,hH⟩ := omitted_actual_component hc k k₂ bound conn degree hp hx
  have Hy := (hH y).mpr hy
  have dt := (omitted_attachment_saturates hc k bound conn hp hx ss xs).2 t
  obtain ⟨w,wl⟩ := hc.exists_walk_length_eq_dist x t
  have le₃ : w.length≤3 := by omega
  have unique {u v r : V} (hu : u ∉ p.support) (vs : v∈p.support) (rs : r∈p.support)
      (e : G.Adj u v) (f : G.Adj u r) : v=r :=
    pin_neighbors_unique hc k bound conn degree hp hu vs rs e f
  rcases short_walk_cases w le₃ with eq|e|⟨u,e,f⟩|⟨u,v,e,f,g⟩
  · exact (hx (eq.symm ▸ ts)).elim
  · exact (st (unique hx ss ts xs e)).elim
  · by_cases us : u∈p.support
    · have eq := unique hx ss us xs e
      have e' : G.Adj (p.getVert i) (p.getVert j) := by
        change G.Adj s t
        rw [eq]
        exact f
      exact Or.inl (chord_lifts hc k bound conn degree hp H ((hH x).mpr hx) Hy hi hj e')
    · exact Or.inl ⟨u,us,e,f⟩
  · by_cases us : u∈p.support <;> by_cases vs : v∈p.support
    · have eu := unique hx ss us xs e
      have sv : G.Adj (p.getVert i) v := by change G.Adj s v; rwa [eu]
      by_cases active : v ∈ PathPins p
      · obtain ⟨_,z,hz,zv⟩ := mem_pathPins.mp active
        obtain ⟨l,hl,lv⟩ := pin_of_neighbor_mem hp hz vs zv
        have first : G.Adj (p.getVert i) (p.getVert l) := by rwa [lv]
        obtain ⟨r,ro,xr,rl⟩ := chord_lifts hc k bound conn degree hp H
          ((hH x).mpr hx) ((hH z).mpr hz) hi hl first
        have second : G.Adj (p.getVert l) (p.getVert j) := by change G.Adj _ t; rwa [lv]
        have pinr : l ∈ Pins p r := mem_filter.mpr ⟨mem_range.mpr (pin_data hl).1,rl⟩
        obtain ⟨h,ho,rh,ht⟩ := chord_lifts hc k bound conn degree hp H
          ((hH r).mpr ro) Hy pinr hj second
        exact Or.inr ⟨r,ro,h,ho,xr,rh,ht⟩
      · have one : v ∈ FlanksOf p i := (chord_lifts_or_flank hc k bound conn degree hp hx vs hi sv).resolve_right
          (fun hv => active (mem_pathPins.mpr ⟨vs,by
            obtain ⟨w,wo,_,wv⟩ := hv
            exact ⟨w,wo,wv⟩⟩))
        have two : v ∈ FlanksOf p j := (chord_lifts_or_flank hc k bound conn degree hp hy vs hj g.symm).resolve_right
          (fun hv => active (mem_pathPins.mpr ⟨vs,by
            obtain ⟨w,wo,_,wv⟩ := hv
            exact ⟨w,wo,wv⟩⟩))
        exact (disjoint_left.mp (flank_disj_of_two hc k k₂ bound conn degree hp hx hy hi hj ij) one two).elim
    · exact (st ((unique hx ss us xs e).trans (unique vs us ts f.symm g))).elim
    · obtain ⟨l,hl,lv⟩ := pin_of_neighbor_mem hp us vs f
      have vq : G.Adj (p.getVert l) (p.getVert j) := by change G.Adj _ t; rwa [lv]
      obtain ⟨z,zo,uz,zq⟩ := chord_lifts hc k bound conn degree hp H
        ((hH u).mpr us) Hy hl hj vq
      exact Or.inr ⟨u,us,z,zo,e,uz,zq⟩
    · exact Or.inr ⟨u,us,v,vs,e,f,g⟩

#print axioms reach_different_pin

private theorem repr_for_pin (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p) (H : OmittedComponent p) (hH : ∀ y, y∈H.vertices ↔ y ∉ p.support)
    {x : V} (hx : x ∉ p.support) {i : ℕ} (hi : i∈Pins p x)
    {q : V} (hq : q∈(PathPins p).erase (p.getVert i)) :
    ∃ v ∈ DistanceTwo G x \ FlanksOf p i,
      (v∈p.support ∧ v=q) ∨ (v∉p.support ∧ G.Adj v q ∧
        ¬ (∃ u ∉ p.support, G.Adj x u ∧ G.Adj u q)) := by
  obtain ⟨nq,mq⟩ := mem_erase.mp hq
  obtain ⟨qs,y,hy,yq⟩ := mem_pathPins.mp mq
  obtain ⟨j,hj,jq⟩ := pin_of_neighbor_mem hp hy qs yq
  have ij : i≠j := fun e => nq ((congrArg p.getVert e).trans jq |>.symm)
  have xq : x≠q := fun e => hx (e.symm ▸ qs)
  have nxq : ¬G.Adj x q := fun e => nq (pin_neighbors_unique hc k bound conn degree hp hx
    qs (p.getVert_mem_support i) e (pin_data hi).2)
  by_cases near : ∃ u ∉ p.support, G.Adj x u ∧ G.Adj u q
  · obtain ⟨u,_,xu,uq⟩ := near
    have d := dist_two hc xq nxq xu uq
    have off : q ∉ FlanksOf p i := by
      have z := pin_not_flank_of_other hp H hc k bound conn degree ((hH x).mpr hx) ((hH y).mpr hy) hi hj ij
      rwa [jq] at z
    exact ⟨q,mem_sdiff.mpr ⟨mem_distanceTwo.mpr d,off⟩,Or.inl ⟨qs,rfl⟩⟩
  · have walks := reach_different_pin hc k k₂ bound conn degree hp hx hy hi hj ij
    rw [jq] at walks
    obtain ⟨u,uo,v,vo,xu,uv,vq⟩ := walks.resolve_left near
    have xv : x≠v := fun e => nxq (e.symm ▸ vq)
    have n : ¬G.Adj x v := fun e => near ⟨v,vo,e,vq⟩
    have d := dist_two hc xv n xu uv
    have vof : v ∉ FlanksOf p i := by
      intro hv
      rcases mem_insert.mp hv with e|e
      · exact vo (e.symm ▸ p.getVert_mem_support (i-1))
      · exact vo ((mem_singleton.mp e).symm ▸ p.getVert_mem_support (i+1))
    exact ⟨v,mem_sdiff.mpr ⟨mem_distanceTwo.mpr d,vof⟩,Or.inr ⟨vo,vq,near⟩⟩

/-- The omitted distance-two vertices are uniquely assigned to pins not
reached by an adjacent porter. The pin budget is tight. -/
theorem pin_representation_exhausts (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p) {x : V} (hx : x ∉ p.support) {i : ℕ} (hi : i ∈ Pins p x) :
    (PathPins p).card = k ∧
      ∀ v ∉ p.support, G.dist x v = 2 →
        ∃ q ∈ PathPins p, q ≠ p.getVert i ∧ G.Adj v q ∧
          (¬ ∃ u ∉ p.support, G.Adj x u ∧ G.Adj u q) ∧
          ∀ w ∉ p.support, G.dist x w = 2 → G.Adj w q → w=v := by
  classical
  obtain ⟨H,hH⟩ := omitted_actual_component hc k k₂ bound conn degree hp hx
  have eq : componentPins H = PathPins p := by
    ext q
    simp only [componentPins,PathPins,mem_filter,hH]
  have cnt := componentPins_card hp H k conn
  rw [eq] at cnt
  have his : p.getVert i ∈ PathPins p := mem_pathPins.mpr
    ⟨p.getVert_mem_support i,x,hx,(pin_data hi).2⟩
  let B := (PathPins p).erase (p.getVert i)
  let D := DistanceTwo G x \ FlanksOf p i
  have repr (q : B) := repr_for_pin hc k k₂ bound conn degree hp H hH hx hi q.prop
  let f (q : B) : D := ⟨Classical.choose (repr q),(Classical.choose_spec (repr q)).1⟩
  have marked (q : B) : ((f q : V) ∈ p.support ∧ (f q : V) = (q : V)) ∨
      ((f q : V) ∉ p.support ∧ G.Adj (f q : V) (q : V) ∧
        ¬ (∃ u ∉ p.support, G.Adj x u ∧ G.Adj u (q : V))) :=
    (Classical.choose_spec (repr q)).2
  have inj : Function.Injective f := by
    intro q r e
    apply Subtype.ext
    have ex : (f q : V)=(f r : V) := congrArg (fun v : D => (v : V)) e
    have qs : (q : V) ∈ p.support := (mem_pathPins.mp (mem_erase.mp q.prop).2).1
    have rs : (r : V) ∈ p.support := (mem_pathPins.mp (mem_erase.mp r.prop).2).1
    rcases marked q with ⟨s,eq⟩|⟨s,eq⟩ <;> rcases marked r with ⟨t,er⟩|⟨t,er⟩
    · exact eq.symm.trans (ex.trans er)
    · exact (t (ex ▸ s)).elim
    · exact (s (ex.symm ▸ t)).elim
    · exact pin_neighbors_unique hc k bound conn degree hp s qs rs eq.1 (ex.symm ▸ er.1)
  have inj_card : B.card ≤ D.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f inj
  have fb : FlanksOf p i ⊆ DistanceTwo G x := by
    intro w hw
    change w ∈ ({p.getVert (i-1),p.getVert (i+1)} : Finset V) at hw
    rw [←rigid_flanks hc k bound conn degree hp hx hi] at hw
    exact (mem_sdiff.mp hw).1
  have fb_size : (FlanksOf p i).card = 2 := by
    have il := (pin_data hi).1
    have ne : p.getVert (i-1) ≠ p.getVert (i+1) := by
      intro e
      have eq := hp.1.getVert_injOn (show i-1 ≤ p.length by omega) (show i+1 ≤ p.length by omega) e
      omega
    simp [FlanksOf,ne]
  have dsum : D.card + (FlanksOf p i).card = (DistanceTwo G x).card :=
    card_sdiff_add_card_eq_card fb
  have bsum : B.card+1 = (PathPins p).card := card_erase_add_one his
  have cap := distanceTwo_le_of_even (k+1) x (bound x)
  have fc : (PathPins p).card = k := by omega
  have fs : Function.Surjective f := (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨inj,by simp only [Fintype.card_coe]; omega⟩ |>.2
  have carried (v : V) (vo : v ∉ p.support) (dv : G.dist x v=2) :
      ∃ q : B, (f q : V)=v ∧ G.Adj v (q : V) ∧
        ¬ (∃ u ∉ p.support, G.Adj x u ∧ G.Adj u (q : V)) := by
    have vno : v ∉ FlanksOf p i := by
      intro h
      rcases mem_insert.mp h with e|e
      · exact vo (e.symm ▸ p.getVert_mem_support (i-1))
      · exact vo ((mem_singleton.mp e).symm ▸ p.getVert_mem_support (i+1))
    let w : D := ⟨v,mem_sdiff.mpr ⟨mem_distanceTwo.mpr dv,vno⟩⟩
    obtain ⟨q,e⟩ := fs w
    have eq : (f q : V)=v := congrArg (fun d : D => (d : V)) e
    rcases marked q with ⟨a,_⟩|⟨_,adj,n⟩
    · exact (vo (eq ▸ a)).elim
    · exact ⟨q,eq,eq ▸ adj,n⟩
  refine ⟨fc,?_⟩
  intro v vo vd
  obtain ⟨q,ev,hvq,qfar⟩ := carried v vo vd
  have qdata := mem_erase.mp q.prop
  refine ⟨q,qdata.2,qdata.1,hvq,qfar,?_⟩
  intro w wo dw hw
  obtain ⟨r,ew,hwr,_⟩ := carried w wo dw
  have qr : (r : V)=(q : V) := pin_neighbors_unique hc k bound conn degree hp wo
    (mem_pathPins.mp (mem_erase.mp r.prop).2).1 (mem_pathPins.mp qdata.2).1 hwr hw
  have e : r=q := Subtype.ext qr
  subst r
  exact ew.symm.trans ev

/-- Exactly k pins occur along any nonspanning longest path
in the saturated range k=d−1. -/
theorem path_pin_card_exact (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p) {z : V} (hz : z ∉ p.support) :
    (PathPins p).card = k := by
  classical
  obtain ⟨H,hH⟩ := omitted_actual_component hc k k₂ bound conn degree hp hz
  have eq : componentPins H = PathPins p := by
    ext q
    simp only [componentPins,PathPins,mem_filter,hH]
  have cnt := componentPins_card hp H k conn
  rw [eq] at cnt
  obtain ⟨s,hs⟩ := card_pos.mp (show 0 < (PathPins p).card by omega)
  obtain ⟨ss,x,hx,xs⟩ := mem_pathPins.mp hs
  obtain ⟨i,hi,_⟩ := pin_of_neighbor_mem hp hx ss xs
  exact (pin_representation_exhausts hc k k₂ bound conn degree hp hx hi).1

#print axioms pin_representation_exhausts
#print axioms path_pin_card_exact

/-- Every nonspanning longest path, chosen with high-degree endpoints, has
an edge between two omitted vertices whose path pins are distinct. -/
theorem adjacent_different_pins (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p) (ha : k+1≤G.degree a) (hb : k+1≤G.degree b)
    {z : V} (hz : z ∉ p.support) :
    ∃ x ∉ p.support, ∃ y ∉ p.support, G.Adj x y ∧
      ∃ i ∈ Pins p x, ∃ j ∈ Pins p y, i≠j := by
  classical
  by_contra none
  have same {x y s t : V} (hx : x ∉ p.support) (hy : y ∉ p.support)
      (xs : G.Adj x s) (yt : G.Adj y t) (ss : s∈p.support) (ts : t∈p.support) (xy : G.Adj x y) : s=t := by
    obtain ⟨i,hi,ei⟩ := pin_of_neighbor_mem hp hx ss xs
    obtain ⟨j,hj,ej⟩ := pin_of_neighbor_mem hp hy ts yt
    have eq : i=j := by
      by_contra ne
      exact none ⟨x,hx,y,hy,xy,i,hi,j,hj,ne⟩
    subst j
    exact ei.symm.trans ej
  have exactPins := path_pin_card_exact hc k k₂ bound conn degree hp hz
  obtain ⟨s,hs,t,ht,st⟩ := one_lt_card.mp (show 1 < (PathPins p).card by omega)
  obtain ⟨ss,x,hx,xs⟩ := mem_pathPins.mp hs
  obtain ⟨ts,y,hy,yt⟩ := mem_pathPins.mp ht
  obtain ⟨i,hi,ei⟩ := pin_of_neighbor_mem hp hx ss xs
  obtain ⟨j,hj,ej⟩ := pin_of_neighbor_mem hp hy ts yt
  have ij : i≠j := by
    intro h
    subst j
    exact st (ei.symm.trans ej)
  have route := reach_different_pin hc k k₂ bound conn degree hp hx hy hi hj ij
  rw [ej] at route
  have no_short : ¬ (∃ v ∉ p.support, G.Adj x v ∧ G.Adj v t) := by
    rintro ⟨v,hv,xv,vt⟩
    exact st (same hx hv xs vt ss ts xv)
  obtain ⟨u,uo,v,vo,xu,uv,vt⟩ := route.resolve_left no_short
  have inactive {w : V} (ws : w ∈ p.support) : ¬G.Adj u w := by
    intro uw
    have h₁ := same hx uo xs uw ss ws xu
    have h₂ := same uo vo uw vt ws ts uv
    exact st (h₁.trans h₂)
  have p2 (w : V) (ws : w∈p.support) {m : V} (um : G.Adj u m) (mw : G.Adj m w) : G.dist u w=2 :=
    dist_two hc (fun e => uo (e.symm ▸ ws)) (inactive ws) um mw
  have ds := p2 s ss xu.symm xs
  have dt := p2 t ts uv vt
  let B := p.support.toFinset \ PinPlusFlanks p
  have no_cover {w : V} (hw : w ∈ B) : G.dist u w=4 := by
    obtain ⟨hs,hc'⟩ := mem_sdiff.mp hw
    have ws := List.mem_toFinset.mp hs
    have notpin : w ∉ PathPins p := fun h => hc' (mem_union.mpr (Or.inl h))
    have low : 4≤G.dist u w := by
      by_contra! h
      obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist u w
      have short : q.length≤3 := by omega
      rcases short_walk_cases q short with he|he|⟨m,he,hf⟩|⟨m,n,he,hf,hg⟩
      · exact uo (he.symm ▸ ws)
      · exact inactive ws he
      · have mo : m ∉ p.support := fun h => inactive h he
        exact notpin (mem_pathPins.mpr ⟨ws,m,mo,hf⟩)
      · have mo : m ∉ p.support := fun h => inactive h he
        by_cases ns : n ∈ p.support
        · obtain ⟨l,hl,el⟩ := pin_of_neighbor_mem hp mo ns hf
          have edge : G.Adj (p.getVert l) w := by rwa [el]
          rcases chord_lifts_or_flank hc k bound conn degree hp mo ws hl edge with fl|⟨n,no,nm,nw⟩
          · have hnp : p.getVert l∈PathPins p := mem_pathPins.mpr
              ⟨p.getVert_mem_support l,m,mo,(pin_data hl).2⟩
            have hb : l∈AroundPins p := mem_filter.mpr ⟨mem_range.mpr (pin_data hl).1,hnp⟩
            exact hc' (mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨l,hb,fl⟩)))
          · exact notpin (mem_pathPins.mpr ⟨ws,n,no,nw⟩)
        · exact notpin (mem_pathPins.mpr ⟨ws,n,ns,hg⟩)
    have cap := (omitted_attachment_saturates hc k bound conn hp hx ss xs).2 w
    have plus := hc.dist_triangle (u:=u) (v:=x) (w:=w)
    have one := dist_eq_one_iff_adj.mpr xu.symm
    omega
  have tB : t ∉ B := fun e => (mem_sdiff.mp e).2 (mem_union.mpr (Or.inl ht))
  have sB : s ∉ B := fun e => (mem_sdiff.mp e).2 (mem_union.mpr (Or.inl hs))
  have uB : u ∉ B := fun e => uo (List.mem_toFinset.mp (mem_sdiff.mp e).1)
  have ssmall : s ∉ insert t B := fun h => (mem_insert.mp h).elim st sB
  have usmall : u ∉ insert s (insert t B) := by
    intro e
    rcases mem_insert.mp e with h|h
    · exact uo (h.symm ▸ ss)
    · rcases mem_insert.mp h with h|h
      · exact uo (h.symm ▸ ts)
      · exact uB h
  have capset : insert u (insert s (insert t B)) ⊆ EvenFrom G u := by
    intro w hw
    rcases mem_insert.mp hw with rfl|hw
    · simp [EvenFrom,SimpleGraph.dist_self]
    · rcases mem_insert.mp hw with rfl|hw
      · simp [EvenFrom,ds,even_two]
      · rcases mem_insert.mp hw with rfl|hw
        · simp [EvenFrom,dt,even_two]
        · simp only [EvenFrom,mem_filter,mem_univ,true_and,no_cover hw]
          decide
  have cap := card_le_card capset
  rw [card_insert_of_not_mem usmall,card_insert_of_not_mem ssmall,card_insert_of_not_mem tB] at cap
  have cardS := cover_card hp
  have cover : p.support.toFinset ⊆ (PinPlusFlanks p) ∪ B := by
    intro w hw
    by_cases hh : w∈PinPlusFlanks p
    · exact mem_union.mpr (Or.inl hh)
    · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨hw,hh⟩))
  have ca := card_le_card cover
  have cb := card_union_le (PinPlusFlanks p) B
  rw [List.toFinset_card_of_nodup hp.1.support_nodup,length_support] at ca
  obtain ⟨H,hH⟩ := omitted_actual_component hc k k₂ bound conn degree hp hz
  have lb := (component_and_length_bound hc k k₂ bound conn degree hp
    H.vertices H.nonempty H.off H.closed H.joined).2
  have be := bound u
  omega

#print axioms adjacent_different_pins


/-- Inactive omitted vertices cannot be adjacent to a porter once both
longest-path endpoints have high degree. -/
theorem no_inactive_neighbor (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p) (ha : k+1≤G.degree a) (hb : k+1≤G.degree b)
    {u x s : V} (uo : u ∉ p.support) (hx : x ∉ p.support) (ss : s ∈ p.support)
    (xs : G.Adj x s) (xu : G.Adj x u)
    (inactive : ∀ {w : V}, w∈p.support → ¬G.Adj u w) : False := by
  classical
  have exactPins := path_pin_card_exact hc k k₂ bound conn degree hp uo
  have hs : s ∈ PathPins p := mem_pathPins.mpr ⟨ss,x,hx,xs⟩
  have ds : G.dist u s=2 := dist_two hc (fun e => uo (e.symm ▸ ss)) (inactive ss) xu.symm xs
  let B := p.support.toFinset \ PinPlusFlanks p
  have no_cover {w : V} (hw : w ∈ B) : G.dist u w=4 := by
    obtain ⟨hs,hc'⟩ := mem_sdiff.mp hw
    have ws := List.mem_toFinset.mp hs
    have notpin : w ∉ PathPins p := fun h => hc' (mem_union.mpr (Or.inl h))
    have low : 4≤G.dist u w := by
      by_contra! h
      obtain ⟨q,ql⟩ := hc.exists_walk_length_eq_dist u w
      have short : q.length≤3 := by omega
      rcases short_walk_cases q short with he|he|⟨m,he,hf⟩|⟨m,n,he,hf,hg⟩
      · exact uo (he.symm ▸ ws)
      · exact inactive ws he
      · have mo : m ∉ p.support := fun h => inactive h he
        exact notpin (mem_pathPins.mpr ⟨ws,m,mo,hf⟩)
      · have mo : m ∉ p.support := fun h => inactive h he
        by_cases ns : n ∈ p.support
        · obtain ⟨l,hl,el⟩ := pin_of_neighbor_mem hp mo ns hf
          have edge : G.Adj (p.getVert l) w := by rwa [el]
          rcases chord_lifts_or_flank hc k bound conn degree hp mo ws hl edge with fl|⟨n,no,nm,nw⟩
          · have hnp : p.getVert l∈PathPins p := mem_pathPins.mpr
              ⟨p.getVert_mem_support l,m,mo,(pin_data hl).2⟩
            have hb : l∈AroundPins p := mem_filter.mpr ⟨mem_range.mpr (pin_data hl).1,hnp⟩
            exact hc' (mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨l,hb,fl⟩)))
          · exact notpin (mem_pathPins.mpr ⟨ws,n,no,nw⟩)
        · exact notpin (mem_pathPins.mpr ⟨ws,n,ns,hg⟩)
    have cap := (omitted_attachment_saturates hc k bound conn hp hx ss xs).2 w
    have plus := hc.dist_triangle (u:=u) (v:=x) (w:=w)
    have one := dist_eq_one_iff_adj.mpr xu.symm
    omega

  have sB : s ∉ B := fun e => (mem_sdiff.mp e).2 (mem_union.mpr (Or.inl hs))
  have uB : u ∉ B := fun e => uo (List.mem_toFinset.mp (mem_sdiff.mp e).1)
  have usmall : u ∉ insert s B := by
    intro e
    rcases mem_insert.mp e with h|h
    · exact uo (h.symm ▸ ss)
    · exact uB h
  have capset : insert u (insert s B) ⊆ EvenFrom G u := by
    intro w hw
    rcases mem_insert.mp hw with rfl|hw
    · simp [EvenFrom,SimpleGraph.dist_self]
    · rcases mem_insert.mp hw with rfl|hw
      · simp [EvenFrom,ds,even_two]
      · simp only [EvenFrom,mem_filter,mem_univ,true_and,no_cover hw]
        decide
  have cap := card_le_card capset
  rw [card_insert_of_not_mem usmall,card_insert_of_not_mem sB] at cap
  have cardS := cover_card hp
  have cover : p.support.toFinset ⊆ (PinPlusFlanks p) ∪ B := by
    intro w hw
    by_cases hh : w∈PinPlusFlanks p
    · exact mem_union.mpr (Or.inl hh)
    · exact mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨hw,hh⟩))
  have ca := card_le_card cover
  have cb := card_union_le (PinPlusFlanks p) B
  rw [List.toFinset_card_of_nodup hp.1.support_nodup,length_support] at ca
  obtain ⟨H,hH⟩ := omitted_actual_component hc k k₂ bound conn degree hp uo
  have lb := (component_and_length_bound hc k k₂ bound conn degree hp
    H.vertices H.nonempty H.off H.closed H.joined).2
  have be := bound u
  omega

/-- Every omitted vertex is a porter. -/
theorem all_omitted_active (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p) (ha : k+1≤G.degree a) (hb : k+1≤G.degree b)
    {z : V} (hz : z ∉ p.support) :
    ∃ s ∈ PathPins p, G.Adj z s := by
  classical
  let Active (v : V) := ∃ s∈p.support, G.Adj v s
  have cnt := path_pin_card_exact hc k k₂ bound conn degree hp hz
  obtain ⟨s,hs⟩ := card_pos.mp (show 0 < (PathPins p).card by omega)
  obtain ⟨ss,x,hx,xs⟩ := mem_pathPins.mp hs
  obtain ⟨H,hH⟩ := omitted_actual_component hc k k₂ bound conn degree hp hz
  obtain ⟨q,_,hsq⟩ := H.joined x ((hH x).mpr hx) z ((hH z).mpr hz)
  have propagate {u v : V} (q : G.Walk u v) (hq : ∀ w ∈ q.support,w ∉ p.support)
      (hu : Active u) : Active v := by
    induction q with
    | nil => exact hu
    | @cons u w v e q ih =>
      apply ih (fun z hz => hq z (by simp [hz]))
      obtain ⟨s,ss,us⟩ := hu
      by_contra! h
      exact no_inactive_neighbor hc k k₂ bound conn degree hp ha hb
        (hq w (by simp)) (hq u (by simp)) ss us e (fun {t} ht wt => h ⟨t,ht,wt⟩)
  obtain ⟨t,ts,zt⟩ := propagate q (fun v hv => H.off v (hsq v hv)) ⟨s,ss,xs⟩
  exact ⟨t,mem_pathPins.mpr ⟨ts,z,hz,zt⟩,zt⟩

#print axioms no_inactive_neighbor
#print axioms all_omitted_active

/-- Each pin class is a clique in the omitted graph. -/
theorem porter_class_clique (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p) {x y s : V} (hx : x ∉ p.support) (hy : y ∉ p.support)
    (ss : s ∈ p.support) (xs : G.Adj x s) (ys : G.Adj y s) (xy : x≠y) :
    G.Adj x y := by
  by_contra n
  obtain ⟨i,hi,is⟩ := pin_of_neighbor_mem hp hx ss xs
  have dy := dist_two hc xy n xs ys.symm
  obtain ⟨q,hq,nq,yq,_,_⟩ := (pin_representation_exhausts hc k k₂ bound conn degree hp hx hi).2 y hy dy
  have eq : q=s := pin_neighbors_unique hc k bound conn degree hp hy (mem_pathPins.mp hq).1 ss yq ys
  exact nq (eq.trans is.symm)

/-- A porter adjacent to one member of a different pin class is adjacent
to every member of that class. -/
theorem porter_adjacent_all_of_class (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p) {x y z s t : V}
    (hx : x ∉ p.support) (hy : y ∉ p.support) (hz : z ∉ p.support)
    (ss : s∈p.support) (ts : t∈p.support) (st : s≠t)
    (xs : G.Adj x s) (yt : G.Adj y t) (zt : G.Adj z t) (xy : G.Adj x y) : G.Adj x z := by
  by_cases e : y=z
  · exact e ▸ xy
  by_contra nn
  have yz := porter_class_clique hc k k₂ bound conn degree hp hy hz ts yt zt e
  have xz : x≠z := by
    intro h
    subst z
    exact st (pin_neighbors_unique hc k bound conn degree hp hx ss ts xs zt)
  have dz := dist_two hc xz nn xy yz
  obtain ⟨i,hi,_⟩ := pin_of_neighbor_mem hp hx ss xs
  obtain ⟨q,hq,_,zq,nq,_⟩ := (pin_representation_exhausts hc k k₂ bound conn degree hp hx hi).2 z hz dz
  have eq := pin_neighbors_unique hc k bound conn degree hp hz (mem_pathPins.mp hq).1 ts zq zt
  exact nq ⟨y,hy,xy,eq.symm ▸ yt⟩

/-- If all omitted vertices are active, any pin class with two members is
universal in the omitted graph. -/
theorem fat_class_universal (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p)
    (active : ∀ z ∉ p.support, ∃ s ∈ PathPins p, G.Adj z s)
    {s : V} (ss : s∈p.support)
    {x₀ y₀ : V} (hx₀ : x₀ ∉ p.support) (hy₀ : y₀ ∉ p.support)
    (xys : x₀≠y₀) (xs₀ : G.Adj x₀ s) (ys₀ : G.Adj y₀ s)
    {x w : V} (hx : x ∉ p.support) (hw : w ∉ p.support)
    (xs : G.Adj x s) (xw : x≠w) : G.Adj x w := by
  obtain ⟨t,mt,wt⟩ := active w hw
  have ts := (mem_pathPins.mp mt).1
  by_cases e : s=t
  · exact porter_class_clique hc k k₂ bound conn degree hp hx hw ss xs (e.symm ▸ wt) xw
  by_contra bad
  have not_near : ¬ (∃ v ∉ p.support, G.Adj w v ∧ G.Adj v s) := by
    rintro ⟨v,hv,wv,vs⟩
    exact bad (porter_adjacent_all_of_class hc k k₂ bound conn degree hp hw hv hx
      ts ss (fun eq => e eq.symm) wt vs xs wv).symm
  obtain ⟨i,hi,it⟩ := pin_of_neighbor_mem hp hw ts wt
  obtain ⟨j,hj,js⟩ := pin_of_neighbor_mem hp hx ss xs
  have ij : i≠j := by
    intro eq
    subst j
    exact e (js.symm.trans it)
  have route := reach_different_pin hc k k₂ bound conn degree hp hw hx hi hj ij
  rw [js] at route
  obtain ⟨u,hu,v,hv,wu,uv,vs⟩ := route.resolve_left not_near
  obtain ⟨r,mr,ur⟩ := active u hu
  have rs := (mem_pathPins.mp mr).1
  have neq : r≠s := fun e => not_near ⟨u,hu,wu,e ▸ ur⟩
  have ux₀ := porter_adjacent_all_of_class hc k k₂ bound conn degree hp hu hv hx₀
    rs ss neq ur vs xs₀ uv
  have uy₀ := porter_adjacent_all_of_class hc k k₂ bound conn degree hp hu hv hy₀
    rs ss neq ur vs ys₀ uv
  have nox₀ : ¬G.Adj w x₀ := fun a => not_near ⟨x₀,hx₀,a,xs₀⟩
  have noy₀ : ¬G.Adj w y₀ := fun a => not_near ⟨y₀,hy₀,a,ys₀⟩
  have nx₀ : w≠x₀ := by
    intro a
    subst x₀
    exact e (pin_neighbors_unique hc k bound conn degree hp hw ss ts xs₀ wt)
  have ny₀ : w≠y₀ := by
    intro a
    subst y₀
    exact e (pin_neighbors_unique hc k bound conn degree hp hw ss ts ys₀ wt)
  have dx₀ := dist_two hc nx₀ nox₀ wu ux₀
  have dy₀ := dist_two hc ny₀ noy₀ wu uy₀
  obtain ⟨q,hq,_,xq,_,oned⟩ := (pin_representation_exhausts hc k k₂ bound conn degree hp hw hi).2 x₀ hx₀ dx₀
  have eq := pin_neighbors_unique hc k bound conn degree hp hx₀ (mem_pathPins.mp hq).1 ss xq xs₀
  exact xys (oned y₀ hy₀ dy₀ (eq.symm ▸ ys₀)).symm

/-- Every pin has two distance-two vertices on the path. -/
theorem all_pin_two_on_path (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    (hp : IsLongest p) (ha : k+1≤G.degree a) (hb : k+1≤G.degree b)
    {s : V} (hs : s ∈ PathPins p) :
    2 ≤ ((DistanceTwo G s).filter (· ∈ p.support)).card := by
  obtain ⟨ss,x,hx,xs⟩ := mem_pathPins.mp hs
  obtain ⟨i,hi,is⟩ := pin_of_neighbor_mem hp hx ss xs
  rw [←is]
  apply pin_has_two_on_path_general hc k bound conn degree hp (by omega) (by omega) hx hi
  intro j jl edge
  rcases chord_lifts_or_flank hc k bound conn degree hp hx (p.getVert_mem_support j) hi edge with fl|⟨y,hy,xy,yj⟩
  · rcases mem_insert.mp fl with e|e
    · exact Or.inl (hp.1.getVert_injOn jl (show i-1≤p.length by have := (pin_data hi).1; omega) e)
    · exact Or.inr (Or.inl (hp.1.getVert_injOn jl (show i+1≤p.length by have := (pin_data hi).1; omega)
        (mem_singleton.mp e)))
  · have jlt : j<p.length := by
      by_contra! jj
      have eq : j=p.length := by omega
      rw [eq,getVert_length] at yj
      exact (no_endpoints hp hy).2 yj
    have hj : j∈Pins p y := mem_filter.mpr ⟨mem_range.mpr jlt,yj⟩
    have ij : i≠j := fun e => edge.ne (congrArg p.getVert e)
    obtain ⟨H,hH⟩ := omitted_actual_component hc k k₂ bound conn degree hp hx
    have apart {u v : V} (hu : u∈H.vertices) (hv : v∈H.vertices) {i j : ℕ}
        (pi : i∈Pins p u) (pj : j∈Pins p v) (lt : i<j) : i+3≤j := by
      have une : u≠v := by
        intro h
        subst v
        exact (Nat.ne_of_lt lt)
          (unique_omitted_pin_at_near_connectivity hc k bound conn degree hp (H.off u hu) i pi j pj)
      obtain ⟨q,hq,hqs⟩ := H.joined u hu v hv
      have qpos : 0<q.length := by cases q with
        | nil => exact (une rfl).elim
        | cons e p => simp
      exact gap_three_of_linked_pins hp pi pj lt q hq qpos (fun z hz => H.off z (hqs z hz))
    have gap : i+3≤j ∨ j+3≤i := by
      rcases lt_or_gt_of_ne ij with l|l
      · exact Or.inl (apart ((hH x).mpr hx) ((hH y).mpr hy) hi hj l)
      · exact Or.inr (apart ((hH y).mpr hy) ((hH x).mpr hx) hj hi l)
    exact Or.inr (Or.inr ⟨y,hy,hj,gap⟩)

#print axioms porter_class_clique
#print axioms porter_adjacent_all_of_class
#print axioms fat_class_universal
#print axioms all_pin_two_on_path

/-- Written on the Wall II #189 with second-smallest degree d at least
three and vertex connectivity at least d−1. Here d=k+1. -/
theorem traceable_near_connectivity (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v, v ∈ p.support := by
  classical
  obtain ⟨a,b,p,hp⟩ := exists_longest hc
  by_cases yes : ∀ x, x ∈ p.support
  · exact ⟨a,b,p,hp.1,yes⟩
  · obtain ⟨x,hx⟩ := not_forall.mp yes
    obtain ⟨u,v,q,hq,same,hu,hv⟩ := rotate_to_two_high_endpoints hc k k₂ conn degree hp hx
    have xoff : x ∉ q.support := fun e => hx ((same x).mpr e)
    obtain ⟨H,hH⟩ := omitted_actual_component hc k k₂ bound conn degree hq xoff
    have Hsize := (component_and_length_bound hc k k₂ bound conn degree hq H.vertices H.nonempty
      H.off H.closed H.joined).1
    have Fsize := path_pin_card_exact hc k k₂ bound conn degree hq xoff
    have act : ∀ z ∉ q.support, ∃ s ∈ PathPins q, G.Adj z s :=
      fun _ hz => all_omitted_active hc k k₂ bound conn degree hq hu hv hz
    have unique : ∀ z∈H.vertices, ∀ s∈PathPins q, ∀ t∈PathPins q, G.Adj z s → G.Adj z t → s=t := by
      intro z hz s hs t ht e f
      exact pin_neighbors_unique hc k bound conn degree hq (H.off z hz)
        (mem_pathPins.mp hs).1 (mem_pathPins.mp ht).1 e f
    have fat : ∀ s∈PathPins q, (∃ x∈H.vertices, ∃ y∈H.vertices, x≠y ∧ G.Adj x s ∧ G.Adj y s) →
        ∀ z∈H.vertices, G.Adj z s → ∀ w∈H.vertices, z≠w → G.Adj z w := by
      intro s hs h z hz zs w hw zw
      obtain ⟨x,hx,y,hy,ne,xs,ys⟩ := h
      exact fat_class_universal hc k k₂ bound conn degree hq act (mem_pathPins.mp hs).1
        (H.off x hx) (H.off y hy) ne xs ys (H.off z hz) (H.off w hw) zs zw
    exact (close_from_fat_porter hc k k₂ bound degree q (PathPins q) H.vertices Fsize Hsize
      (fun _ => mem_pathPins) hH unique (fun z hz => act z (H.off z hz)) fat
      (fun s hs => all_pin_two_on_path hc k k₂ bound conn degree hq hu hv hs)).elim

#print axioms traceable_near_connectivity
end Graffiti189LongestPath.AdjacentPins
