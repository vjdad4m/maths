import Rigidity189
import PinDistanceTwo189

namespace Graffiti189LongestPath.D3
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity
set_option maxHeartbeats 2500000
variable {V : Type*} {G : SimpleGraph V}
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


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private lemma lengths_take_drop {x y : V} (p : G.Walk x y) (n : ℕ) (hn : n ≤ p.length) :
    (p.take n).length = n ∧ (p.drop n).length = p.length - n := by
  induction p generalizing n with
  | nil =>
    have : n=0 := by simpa using hn
    subst n
    exact ⟨rfl,rfl⟩
  | @cons a b c h p ih =>
    cases n with
    | zero => simp [Walk.take,Walk.drop]
    | succ n =>
      have hh : n ≤ p.length := by
        simp only [length_cons] at hn
        omega
      obtain ⟨h₁,h₂⟩ := ih n hh
      simp [Walk.take,Walk.drop,h₁,h₂,Nat.add_sub_add_right]



omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private lemma distance_on_geodesic (hc : G.Connected) {x y : V} (p : G.Walk x y)
    (hp : p.length = G.dist x y) (i : ℕ) (hi : i ≤ p.length) :
    G.dist x (p.getVert i) = i := by
  obtain ⟨h₁,h₂⟩ := lengths_take_drop p i hi
  have upper := G.dist_le (p.take i)
  have lower := hc.dist_triangle (u:=x) (v:=p.getVert i) (w:=y)
  have suffix := G.dist_le (p.drop i)
  omega


structure Hyp (G : SimpleGraph V) [DecidableRel G.Adj] where
  con : G.Connected
  even : ∀ x, (EvenFrom G x).card ≤ 4
  conn : ∀ S : Finset V, S.card < 2 → (G.induce ((↑S : Set V)ᶜ)).Connected
  deg : ∀ u v, u ≠ v → 3 ≤ G.degree u ∨ 3 ≤ G.degree v

variable (h : Hyp G)
variable {a b : V} {p : G.Walk a b}

abbrev Outside (p : G.Walk a b) := {x : V // x ∉ p.support}
abbrev OGraph (p : G.Walk a b) := G.induce {x | x ∉ p.support}

private def Active (p : G.Walk a b) (x : Outside p) := (Pins p (x : V)).Nonempty

private def Flanks (p : G.Walk a b) (i : ℕ) : Finset V :=
  {p.getVert (i-1),p.getVert (i+1)}

def TwoOnPath (p : G.Walk a b) (z : V) : Prop :=
  2 ≤ ((DistanceTwo G z).filter (· ∈ p.support)).card

include h
set_option linter.unusedSectionVars false

private lemma pin_injective (hp : IsLongest p) {x : Outside p} {i j : ℕ}
    (hi : i ∈ Pins p (x : V)) (hj : j ∈ Pins p (x : V)) : i=j :=
  unique_omitted_pin_at_near_connectivity h.con 2 h.even h.conn h.deg hp x.prop i hi j hj

private lemma pin_vertex (hp : IsLongest p) {x : Outside p} {i : ℕ}
    (hi : i ∈ Pins p (x : V)) {z : V} (zs : z ∈ p.support) (e : G.Adj ↑x z) :
    p.getVert i = z := by
  obtain ⟨j,hj,ej⟩ := pin_of_neighbor_mem hp x.prop zs e
  rw [pin_injective h hp hi hj]
  exact ej

private lemma dist_cap (x : V) : (DistanceTwo G x).card ≤ 3 :=
  distanceTwo_le_of_even 3 x (h.even x)

private lemma ecc_active (hp : IsLongest p) {x : Outside p} {i : ℕ}
    (hi : i ∈ Pins p (x : V)) : ∀ z, G.dist ↑x z ≤ 3 :=
  (omitted_attachment_saturates h.con 2 h.even h.conn hp x.prop
    (p.getVert_mem_support i) (pin_data hi).2).2

private lemma subset_flanks (hp : IsLongest p) {x : Outside p} {i : ℕ}
    (hi : i ∈ Pins p (x : V)) : Flanks p i ⊆ DistanceTwo G (x : V) := by
  intro v hv
  change v ∈ ({p.getVert (i-1),p.getVert (i+1)} : Finset V) at hv
  rw [←rigid_flanks h.con 2 h.even h.conn h.deg hp x.prop hi] at hv
  exact (mem_sdiff.mp hv).1

omit h in
private lemma flank_support {i : ℕ} {z : V} (hz : z ∈ Flanks p i) : z ∈ p.support := by
  rcases mem_insert.mp hz with e|e
  · exact e.symm ▸ p.getVert_mem_support (i-1)
  · exact (mem_singleton.mp e).symm ▸ p.getVert_mem_support (i+1)

omit h in
private lemma flank_card (hp : IsLongest p) {x : Outside p} {i : ℕ}
    (hi : i ∈ Pins p (x : V)) : (Flanks p i).card = 2 := by
  have il := (pin_data hi).1
  have ne : p.getVert (i-1) ≠ p.getVert (i+1) := by
    intro e
    have e' := hp.1.getVert_injOn (show i-1 ≤ p.length by omega) (show i+1 ≤ p.length by omega) e
    omega
  simp [Flanks,ne]

private lemma third_unique (hp : IsLongest p) {x : Outside p} {i : ℕ}
    (hi : i ∈ Pins p (x : V)) {y z : V} (hd : G.dist ↑x y=2) (he : G.dist ↑x z=2)
    (hy : y ∉ Flanks p i) (hz : z ∉ Flanks p i) : y=z := by
  let U := DistanceTwo G (x : V) \ Flanks p i
  have cu := card_sdiff_add_card_eq_card (subset_flanks h hp hi)
  have cf := flank_card hp hi
  have cap := dist_cap h (x : V)
  change U.card + (Flanks p i).card = (DistanceTwo G (x : V)).card at cu
  have su : U.card ≤ 1 := by omega
  exact card_le_one.mp su y (mem_sdiff.mpr ⟨mem_distanceTwo.mpr hd,hy⟩)
    z (mem_sdiff.mpr ⟨mem_distanceTwo.mpr he,hz⟩)

/-- If an active outside vertex has a distance-two witness off the path,
its pin has no chords at all within the path. -/
private lemma flank_only (hp : IsLongest p) {x : Outside p} {i : ℕ}
    (hi : i ∈ Pins p (x : V)) {w : V} (wo : w ∉ p.support) (d : G.dist ↑x w=2)
    {z : V} (zs : z ∈ p.support) (adj : G.Adj (p.getVert i) z) : z ∈ Flanks p i := by
  by_contra hz
  have nxz : ¬G.Adj (x : V) z := by
    intro e
    have eq := pin_vertex h hp hi zs e
    exact adj.ne eq
  have xz : (x : V) ≠ z := fun e => x.prop (e.symm ▸ zs)
  have d' := dist_two h.con xz nxz (pin_data hi).2 adj
  have eq := third_unique h hp hi d d' (fun hw => wo (flank_support hw)) hz
  exact wo (eq.symm ▸ zs)

private lemma distinct_pins_gap (hp : IsLongest p) (con : (OGraph p).Connected)
    {x y : Outside p} {i j : ℕ} (hi : i ∈ Pins p (x : V)) (hj : j ∈ Pins p (y : V))
    (lt : i<j) : i+3≤j := by
  have xy : x ≠ y := by
    intro e
    subst y
    exact (Nat.ne_of_lt lt) (pin_injective h hp hi hj)
  obtain ⟨q,hq⟩ := (con x y).exists_isPath
  let f : OGraph p →g G := ⟨Subtype.val,fun e => e⟩
  have qpos : 0<q.length := by cases q with
    | nil => contradiction
    | cons e q => simp
  have qp : 0<(q.map f).length := by simpa using qpos
  exact gap_three_of_linked_pins hp hi hj lt (q.map f)
    (map_isPath_of_injective Subtype.val_injective hq) qp (by
      intro v hv
      rw [support_map] at hv
      obtain ⟨z,_,rfl⟩ := List.mem_map.mp hv
      exact z.prop)

private lemma pin_flank_disjoint (hp : IsLongest p) (con : (OGraph p).Connected)
    {x y : Outside p} {i j : ℕ} (hi : i ∈ Pins p (x : V)) (hj : j ∈ Pins p (y : V))
    (ne : i ≠ j) : Disjoint (Flanks p i) (Flanks p j) := by
  have gap : i+3≤j ∨ j+3≤i := by
    rcases lt_or_gt_of_ne ne with l|l
    · exact Or.inl (distinct_pins_gap h hp con hi hj l)
    · exact Or.inr (distinct_pins_gap h hp con hj hi l)
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  rw [disjoint_left]
  intro z hz hw
  have unpack {u : ℕ} (h : z ∈ Flanks p u) :
      ∃ m, (m=u-1 ∨ m=u+1) ∧ z=p.getVert m := by
    rcases mem_insert.mp h with hh|hh
    · exact ⟨_,Or.inl rfl,hh⟩
    · exact ⟨_,Or.inr rfl,mem_singleton.mp hh⟩
  obtain ⟨m,hm,em⟩ := unpack hz
  obtain ⟨n,hn,en⟩ := unpack hw
  have ee := hp.1.getVert_injOn (show m≤p.length by omega) (show n≤p.length by omega) (em.symm.trans en)
  omega

private lemma pin_not_flank (hp : IsLongest p) (con : (OGraph p).Connected)
    {x y : Outside p} {i j : ℕ} (hi : i ∈ Pins p (x : V)) (hj : j ∈ Pins p (y : V))
    (ne : i ≠ j) : p.getVert j ∉ Flanks p i := by
  have gap : i+3≤j ∨ j+3≤i := by
    rcases lt_or_gt_of_ne ne with l|l
    · exact Or.inl (distinct_pins_gap h hp con hi hj l)
    · exact Or.inr (distinct_pins_gap h hp con hj hi l)
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  intro hz
  have bad {m : ℕ} (hm : m=i-1 ∨ m=i+1) (e : p.getVert j = p.getVert m) : False := by
    have eq := hp.1.getVert_injOn jl.le (show m ≤ p.length by omega) e
    omega
  rcases mem_insert.mp hz with e|e
  · exact bad (Or.inl rfl) e
  · exact bad (Or.inr rfl) (mem_singleton.mp e)

#print axioms pin_flank_disjoint

private theorem off_dist_two (con : (OGraph p).Connected)
    {x y : Outside p} (d : (OGraph p).dist x y = 2) :
    G.dist (x : V) (y : V) = 2 := by
  obtain ⟨q,ql⟩ := con.exists_walk_length_eq_dist x y
  have len : q.length=2 := ql.trans d
  have ex : (OGraph p).Adj x (q.getVert 1) := by
    simpa using q.adj_getVert_succ (i:=0) (by omega)
  have ey : (OGraph p).Adj (q.getVert 1) y := by
    have e := q.adj_getVert_succ (i:=1) (by omega)
    have eq : q.getVert 2 = y := by rw [←len,getVert_length]
    simpa only [eq] using e
  have nxy : ¬G.Adj (x : V) (y : V) := by
    intro e
    have dis := dist_eq_one_iff_adj.mpr (show (OGraph p).Adj x y from e)
    omega
  have xy : (x : V) ≠ (y : V) := by
    intro e
    have eq : x=y := Subtype.ext e
    rw [eq,SimpleGraph.dist_self] at d
    omega
  exact dist_two h.con xy nxy ex ey

private theorem off_dist_two_witness (con : (OGraph p).Connected)
    {x y : Outside p} (far : 2 ≤ (OGraph p).dist x y) :
    ∃ z : Outside p, (OGraph p).dist x z = 2 ∧ G.dist (x : V) (z : V) = 2 := by
  obtain ⟨q,ql⟩ := con.exists_walk_length_eq_dist x y
  have d := distance_on_geodesic con q ql 2 (by omega)
  exact ⟨q.getVert 2,d,off_dist_two h con d⟩

omit h [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
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

private theorem no_short_to_flank_pin (hp : IsLongest p) (con : (OGraph p).Connected)
    {x y : Outside p} {i j : ℕ} (hi : i ∈ Pins p (x : V)) (hj : j ∈ Pins p (y : V))
    (ne : i ≠ j)
    (w r : Outside p) (dw : G.dist (x : V) (w : V) = 2) (dr : G.dist (y : V) (r : V) = 2)
    (no_fast : ∀ {v : Outside p}, G.Adj (v : V) (p.getVert j) →
       (OGraph p).dist x v ≤ 2 → False) : False := by
  let s := p.getVert i
  let t := p.getVert j
  have ss : s ∈ p.support := p.getVert_mem_support _
  have ts : t ∈ p.support := p.getVert_mem_support _
  have st : s ≠ t := fun e =>
    ne (hp.1.getVert_injOn (pin_data hi).1.le (pin_data hj).1.le e)
  have SNC : ¬G.Adj s t := fun e =>
    pin_not_flank h hp con hi hj ne (flank_only h hp hi w.prop dw ts e)
  have other_pins_not_chord {u : Outside p} {v : V} (vs : v ∈ p.support)
      (uv : G.Adj (u : V) v) : ¬G.Adj t v := by
    intro e
    obtain ⟨l,hl,le⟩ := pin_of_neighbor_mem hp u.prop vs uv
    have hn : j ≠ l := fun eql => e.ne ((congrArg p.getVert eql).trans le)
    have m := flank_only h hp hj r.prop dr vs e
    exact pin_not_flank h hp con hj hl hn (le.symm ▸ m)
  have dcap := ecc_active h hp hi t
  obtain ⟨q,ql⟩ := h.con.exists_walk_length_eq_dist (x : V) t
  have len : q.length ≤ 3 := by omega
  have xt : (x : V) ≠ t := fun e => x.prop (e.symm ▸ ts)
  have xnt : ¬G.Adj (x : V) t := fun e => st (pin_vertex h hp hi ts e)
  rcases short_walk_cases q len with hl|hl|⟨u,e,f⟩|⟨u,v,e,f,g⟩
  · exact xt hl
  · exact xnt hl
  ·
    by_cases us : u ∈ p.support
    · have eq := pin_vertex h hp hi us e
      exact SNC (show G.Adj (p.getVert i) (p.getVert j) from by rw [eq]; exact f)
    · let u' : Outside p := ⟨u,us⟩
      have eu : (OGraph p).Adj x u' := e
      exact no_fast (v:=u') f ((OGraph p).dist_le eu.toWalk |>.trans (by simp))
  ·
    by_cases us : u ∈ p.support <;> by_cases vs : v ∈ p.support
    · have eq := pin_vertex h hp hi us e
      have a : v ∈ Flanks p i := flank_only h hp hi w.prop dw vs (eq.symm ▸ f)
      have b : v ∈ Flanks p j := flank_only h hp hj r.prop dr vs g.symm
      exact disjoint_left.mp (pin_flank_disjoint h hp con hi hj ne) a b
    · let v' : Outside p := ⟨v,vs⟩
      have eq₁ := pin_vertex h hp hi us e
      have eq₃ : t=u := by
        have a := pin_of_neighbor_mem hp v'.prop ts g
        obtain ⟨l,hl,eq⟩ := a
        have m := pin_vertex h hp hl us f.symm
        exact eq.symm.trans m
      exact st (eq₁.trans eq₃.symm)
    · let u' : Outside p := ⟨u,us⟩
      exact other_pins_not_chord (u:=u') vs f g.symm
    · let u' : Outside p := ⟨u,us⟩
      let v' : Outside p := ⟨v,vs⟩
      have e' : (OGraph p).Adj x u' := e
      have f' : (OGraph p).Adj u' v' := f
      have dd := (OGraph p).dist_le (.cons e' f'.toWalk)
      exact no_fast (v:=v') g (by simpa using dd)


/-- A differently pinned pair cannot minimize omitted distance at any
distance at least three. -/
theorem minimum_pair_at_most_two (hp : IsLongest p) (con : (OGraph p).Connected)
    {x y : Outside p} {i j : ℕ} (hi : i ∈ Pins p (x : V)) (hj : j ∈ Pins p (y : V))
    (ne : i ≠ j)
    (mn : ∀ (u v : Outside p) (r s : ℕ), r ∈ Pins p (u : V) → s ∈ Pins p (v : V) → r ≠ s →
      (OGraph p).dist x y ≤ (OGraph p).dist u v) :
    (OGraph p).dist x y ≤ 2 := by
  by_contra! large
  obtain ⟨w,_,dw⟩ := off_dist_two_witness h con (show 2 ≤ (OGraph p).dist x y by omega)
  have rfar : 2 ≤ (OGraph p).dist y x := by
    rw [dist_comm]
    omega
  obtain ⟨r,_,dr⟩ := off_dist_two_witness h con rfar
  apply no_short_to_flank_pin h hp con hi hj ne w r dw dr
  intro v vt dl
  have hjv : j ∈ Pins p (v : V) := mem_filter.mpr ⟨mem_range.mpr (pin_data hj).1,vt⟩
  have hh := mn x v i j hi hjv ne
  omega

#print axioms minimum_pair_at_most_two

private lemma only_one_off_dist_two {z u v : V} (hz : TwoOnPath p z)
    (hu : u ∉ p.support) (hv : v ∉ p.support)
    (du : G.dist z u = 2) (dv : G.dist z v = 2) : u=v := by
  let A := (DistanceTwo G z).filter (· ∈ p.support)
  let B := DistanceTwo G z \ A
  have sub : A ⊆ DistanceTwo G z := filter_subset _ _
  have count := card_sdiff_add_card_eq_card sub
  change B.card + A.card = (DistanceTwo G z).card at count
  have cap := dist_cap h z
  have la : 2 ≤ A.card := hz
  have cb : B.card ≤ 1 := by omega
  exact card_le_one.mp cb u (mem_sdiff.mpr ⟨mem_distanceTwo.mpr du,fun e => hu (mem_filter.mp e).2⟩)
    v (mem_sdiff.mpr ⟨mem_distanceTwo.mpr dv,fun e => hv (mem_filter.mp e).2⟩)

private lemma off_two_unique (hp : IsLongest p) (con : (OGraph p).Connected)
    {x y : Outside p} {i : ℕ} (hi : i ∈ Pins p (x : V)) (d : (OGraph p).dist x y = 2) :
    ∀ z : Outside p, (OGraph p).dist x z=2 → z=y := by
  intro z dz
  apply Subtype.ext
  exact third_unique h hp hi (off_dist_two h con dz) (off_dist_two h con d)
    (fun e => z.prop (flank_support e)) (fun e => y.prop (flank_support e))

omit h [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private lemma cover_of_unique_two (con : (OGraph p).Connected)
    {x y : Outside p} (d : (OGraph p).dist x y=2)
    (ux : ∀ z : Outside p, (OGraph p).dist x z=2 → z=y)
    (uy : ∀ z : Outside p, (OGraph p).dist y z=2 → z=x) :
    ∀ z : Outside p, z=x ∨ z=y ∨ (OGraph p).Adj x z ∨ (OGraph p).Adj y z := by
  intro z
  by_contra! h
  obtain ⟨zne_x,zne_y,nxz,nyz⟩ := h
  have dxz := con.one_lt_dist_of_ne_of_not_adj zne_x.symm nxz
  obtain ⟨q,ql⟩ := con.exists_walk_length_eq_dist x z
  have at2 := distance_on_geodesic con q ql 2 (by omega : 2 ≤ q.length)
  have eq2 := ux _ at2
  have long : 4 ≤ q.length := by
    by_contra! hs
    have alt : q.length=2 ∨ q.length=3 := by omega
    rcases alt with e|e
    · have endp : q.getVert 2=z := by rw [←e,getVert_length]
      exact zne_y (endp.symm.trans eq2)
    · have endp : q.getVert 3=z := by rw [←e,getVert_length]
      have ed := q.adj_getVert_succ (i:=2) (by omega)
      exact nyz (by simpa only [eq2,endp] using ed)
  have at4 := distance_on_geodesic con q ql 4 long
  have e₁ := q.adj_getVert_succ (i:=2) (by omega)
  have e₂ := q.adj_getVert_succ (i:=3) (by omega)
  have mid : (OGraph p).Adj y (q.getVert 3) := eq2 ▸ e₁
  have low := con.dist_triangle (u:=x) (v:=y) (w:=q.getVert 4)
  have high : (OGraph p).dist y (q.getVert 4) ≤ 2 := by
    simpa using (OGraph p).dist_le (.cons mid e₂.toWalk)
  have dd : (OGraph p).dist y (q.getVert 4)=2 := by
    omega
  have eq4 := uy _ dd
  rw [eq4,SimpleGraph.dist_self] at at4
  contradiction

private theorem no_exclusive_neighbor (hp : IsLongest p) (con : (OGraph p).Connected)
    {x y : Outside p} {i j : ℕ} (hi : i ∈ Pins p (x : V)) (hj : j ∈ Pins p (y : V))
    (ne : i ≠ j) (d : (OGraph p).dist x y=2)
    (mn : ∀ (u v : Outside p) (r s : ℕ), r ∈ Pins p (u : V) → s ∈ Pins p (v : V) → r ≠ s →
      2 ≤ (OGraph p).dist u v)
    (two : TwoOnPath p (p.getVert i)) :
    ∀ z : Outside p, (OGraph p).Adj x z → (OGraph p).Adj y z := by
  let s := p.getVert i
  let t := p.getVert j
  have d' : (OGraph p).dist y x=2 := by rwa [dist_comm]
  have ux := off_two_unique h hp con hi d
  have uy := off_two_unique h hp con hj d'
  have cover := cover_of_unique_two con d ux uy
  have min_adj {u v : Outside p} {i j : ℕ} (hi : i ∈ Pins p (u : V))
      (hj : j ∈ Pins p (v : V)) (a : (OGraph p).Adj u v) : i=j := by
    by_contra hn
    have big := mn u v i j hi hj hn
    rw [dist_eq_one_iff_adj.mpr a] at big
    omega
  have nxy : ¬(OGraph p).Adj x y := fun e => ne (min_adj hi hj e)
  have ss : s ∈ p.support := p.getVert_mem_support _
  have ts : t ∈ p.support := p.getVert_mem_support _
  have sh : G.Adj (x : V) s := (pin_data hi).2
  obtain ⟨wq,wl⟩ := con.exists_walk_length_eq_dist x y
  have wlen : wq.length=2 := wl.trans d
  let w := wq.getVert 1
  have xw : (OGraph p).Adj x w := by simpa using wq.adj_getVert_succ (i:=0) (by omega)
  have yw : (OGraph p).Adj y w := by
    have e := wq.adj_getVert_succ (i:=1) (by omega)
    have eq : wq.getVert 2=y := by rw [←wlen,getVert_length]
    exact (show (OGraph p).Adj w y from by simpa only [eq] using e).symm
  have common_na {v : Outside p} (ex : (OGraph p).Adj x v) (ey : (OGraph p).Adj y v) :
      ¬G.Adj (v : V) s := by
    intro e
    have iv : i ∈ Pins p (v : V) := mem_filter.mpr ⟨mem_range.mpr (pin_data hi).1,e⟩
    exact ne (min_adj hj iv ey).symm
  have dsw : G.dist s (w : V)=2 := dist_two h.con (fun e => w.prop (e ▸ ss))
    (fun e => common_na xw yw e.symm) sh.symm xw
  intro z xz
  by_contra nyz
  have zne_y : z ≠ y := fun e => nxy (e ▸ xz)
  have zne_x : z ≠ x := xz.ne.symm
  have z_s : G.Adj (z : V) s := by
    by_contra e
    have dsz : G.dist s (z : V)=2 := dist_two h.con (fun e => z.prop (e ▸ ss))
      (fun e' => e e'.symm) sh.symm xz
    have eq := only_one_off_dist_two h two z.prop w.prop dsz dsw
    exact nyz ((Subtype.ext eq).symm ▸ yw)
  have zi : i ∈ Pins p (z : V) := mem_filter.mpr ⟨mem_range.mpr (pin_data hi).1,z_s⟩
  have z_far : 3 ≤ (OGraph p).dist z y := by
    have low := con.one_lt_dist_of_ne_of_not_adj zne_y (fun e => nyz e.symm)
    by_contra! hsmall
    have de : (OGraph p).dist y z=2 := by rw [dist_comm]; omega
    exact zne_x (uy z de)
  obtain ⟨z₂,_,dz₂⟩ := off_dist_two_witness h con (show 2 ≤ (OGraph p).dist z y by omega)
  have dyx := off_dist_two h con d'
  apply no_short_to_flank_pin h hp con zi hj ne z₂ x dz₂ dyx
  intro v vt fast
  have vj : j ∈ Pins p (v : V) := mem_filter.mpr ⟨mem_range.mpr (pin_data hj).1,vt⟩
  have near_y : v = y ∨ (OGraph p).Adj y v := by
    rcases cover v with e|e|e|e
    · subst v
      exact (ne (pin_injective h hp hi vj)).elim
    · exact Or.inl e
    · exact (ne (min_adj hi vj e)).elim
    · exact Or.inr e
  have avoid {u : Outside p} (e : (OGraph p).Adj z u) : u ≠ y ∧ ¬(OGraph p).Adj y u := by
    constructor
    · intro eq
      exact nyz (eq ▸ e.symm)
    · intro hyu
      have d_ := dist_two con zne_y.symm nyz hyu e.symm
      exact zne_x (uy z d_)
  obtain ⟨q,ql⟩ := con.exists_walk_length_eq_dist z v
  have qlen : q.length ≤ 2 := by omega
  match q with
  | .nil => exact ne (pin_injective h hp zi vj)
  | .cons e .nil =>
    rcases near_y with hv|hv
    · exact (avoid e).1 hv
    · exact (avoid e).2 hv
  | .cons (v:=u) e (.cons f .nil) =>
    have bad := avoid e
    rcases near_y with hv|hv
    · exact bad.2 (hv ▸ f.symm)
    · have du := dist_two con bad.1.symm bad.2 hv f.symm
      have eq := uy u du
      exact ne (min_adj hi vj (eq ▸ f))
  | .cons _ (.cons _ (.cons _ q)) => simp only [length_cons] at qlen; omega

#print axioms no_exclusive_neighbor

/-- The distance-two branch cannot satisfy the even-count and degree premises. -/
theorem minimum_pair_two_impossible (hp : IsLongest p) (con : (OGraph p).Connected)
    {x y : Outside p} {i j : ℕ} (hi : i ∈ Pins p (x : V)) (hj : j ∈ Pins p (y : V))
    (ne : i ≠ j) (d : (OGraph p).dist x y=2)
    (mn : ∀ (u v : Outside p) (r s : ℕ), r ∈ Pins p (u : V) → s ∈ Pins p (v : V) → r ≠ s →
      2 ≤ (OGraph p).dist u v)
    (twoL : TwoOnPath p (p.getVert i)) (twoR : TwoOnPath p (p.getVert j)) : False := by
  let s := p.getVert i
  let t := p.getVert j
  have both_x := no_exclusive_neighbor h hp con hi hj ne d mn twoL
  have both_y := no_exclusive_neighbor h hp con hj hi ne.symm (by rwa [dist_comm]) mn twoR
  obtain ⟨q,ql⟩ := con.exists_walk_length_eq_dist x y
  have qlen : q.length=2 := ql.trans d
  let w := q.getVert 1
  have xw : (OGraph p).Adj x w := by simpa using q.adj_getVert_succ (i:=0) (by omega)
  have yw : (OGraph p).Adj y w := by
    have e := q.adj_getVert_succ (i:=1) (by omega)
    have eq : q.getVert 2=y := by rw [←qlen,getVert_length]
    exact (show (OGraph p).Adj w y from by simpa only [eq] using e).symm
  have common_dist {v : Outside p} (ex : (OGraph p).Adj x v) (ey : (OGraph p).Adj y v) :
      G.dist s (v : V)=2 := by
    have kn : s ≠ (v : V) := fun e => v.prop (e ▸ p.getVert_mem_support i)
    apply dist_two h.con kn ?_ (pin_data hi).2.symm ex
    intro e
    have vf : i ∈ Pins p (v : V) := mem_filter.mpr ⟨mem_range.mpr (pin_data hi).1,e.symm⟩
    have big := mn v y i j vf hj ne
    rw [dist_eq_one_iff_adj.mpr ey.symm] at big
    omega
  have common {v : Outside p} (ex : (OGraph p).Adj x v) (ey : (OGraph p).Adj y v) :
      (v : V) = w :=
    only_one_off_dist_two h twoL v.prop w.prop (common_dist ex ey) (common_dist xw yw)
  have degree_le {z : Outside p} {l : ℕ} (hl : l ∈ Pins p (z : V))
      (nn : ∀ v : Outside p, (OGraph p).Adj z v → (v : V) = w) :
      G.degree (z : V) ≤ 2 := by
    classical
    have cnt : G.neighborFinset (z : V) ⊆ {p.getVert l,(w : V)} := by
      intro v hv
      have e := (G.mem_neighborFinset _ _).mp hv
      by_cases vp : v ∈ p.support
      · exact mem_insert.mpr (Or.inl (pin_vertex h hp hl vp e).symm)
      · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (nn ⟨v,vp⟩ e)))
    rw [← G.card_neighborFinset_eq_degree]
    exact (card_le_card cnt).trans (by
      have a := card_insert_le (p.getVert l) ({(w : V)} : Finset V)
      simpa only [card_singleton] using a)
  have dx := degree_le hi (fun v e => common e (both_x v e))
  have dy := degree_le hj (fun v e => common (both_y v e) e)
  have xy : (x:V) ≠ (y:V) := by
    intro e
    have ee : y=x := Subtype.ext e.symm
    rw [ee,SimpleGraph.dist_self] at d
    omega
  rcases h.deg _ _ xy with b|b <;> omega

/-- If a differently pinned pair is adjacent, its active endpoints are
universal in the omitted graph, and each pin misses at most one omitted
vertex. The omitted graph has order at most two. -/
theorem adjacent_pair_impossible (hp : IsLongest p) (con : (OGraph p).Connected)
    {x y : Outside p} {i j : ℕ} (hi : i ∈ Pins p (x : V)) (hj : j ∈ Pins p (y : V))
    (ne : i ≠ j) (xy : (OGraph p).Adj x y)
    (twoL : TwoOnPath p (p.getVert i)) (twoR : TwoOnPath p (p.getVert j))
    (many : 3 ≤ Fintype.card (Outside p)) : False := by
  let s := p.getVert i
  let t := p.getVert j
  have st : s ≠ t := fun e => ne (hp.1.getVert_injOn (pin_data hi).1.le (pin_data hj).1.le e)
  have xnt : ¬G.Adj (x : V) t := fun e => st (pin_vertex h hp hi (p.getVert_mem_support j) e)
  have yns : ¬G.Adj (y : V) s := fun e => st (pin_vertex h hp hj (p.getVert_mem_support i) e).symm
  have dxt : G.dist (x : V) t=2 := dist_two h.con
    (fun e => x.prop (e.symm ▸ p.getVert_mem_support j)) xnt xy (pin_data hj).2
  have dys : G.dist (y : V) s=2 := dist_two h.con
    (fun e => y.prop (e.symm ▸ p.getVert_mem_support i)) yns xy.symm (pin_data hi).2
  have univ_x (z : Outside p) (hz : x ≠ z) : (OGraph p).Adj x z := by
    by_contra he
    have lb := con.one_lt_dist_of_ne_of_not_adj hz he
    obtain ⟨w,_,dw⟩ := off_dist_two_witness h con (show 2 ≤ (OGraph p).dist x z by omega)
    have e := third_unique h hp hi dw dxt (fun w' => w.prop (flank_support w'))
      (pin_not_flank h hp con hi hj ne)
    exact w.prop (e.symm ▸ p.getVert_mem_support j)
  have univ_y (z : Outside p) (hz : y ≠ z) : (OGraph p).Adj y z := by
    by_contra he
    have lb := con.one_lt_dist_of_ne_of_not_adj hz he
    obtain ⟨w,_,dw⟩ := off_dist_two_witness h con (show 2 ≤ (OGraph p).dist y z by omega)
    have e := third_unique h hp hj dw dys (fun w' => w.prop (flank_support w'))
      (pin_not_flank h hp con hj hi ne.symm)
    exact w.prop (e.symm ▸ p.getVert_mem_support i)
  classical
  let SL := (univ : Finset (Outside p)).filter fun z : Outside p => ¬G.Adj (z : V) s
  let SR := (univ : Finset (Outside p)).filter fun z : Outside p => ¬G.Adj (z : V) t
  have misses_le (x : Outside p) (z : V) (zs : z ∈ p.support) (two : TwoOnPath p z) (xz : G.Adj (x : V) z)
      (near : ∀ v : Outside p, x ≠ v → (OGraph p).Adj x v) :
      ((univ : Finset (Outside p)).filter fun v : Outside p => ¬G.Adj (v : V) z).card ≤ 1 := by
    apply card_le_one.mpr
    intro u hu v hv
    have miss (v : Outside p) (missed : ¬G.Adj (v : V) z) : G.dist z (v : V) = 2 := by
      have ne : x ≠ v := fun e => missed (e ▸ xz)
      have zn : z ≠ (v : V) := fun e => v.prop (e ▸ zs)
      exact dist_two h.con zn (fun e => missed e.symm) xz.symm (near v ne)
    have m₁ := (mem_filter.mp hu).2
    have m₂ := (mem_filter.mp hv).2
    exact Subtype.ext (only_one_off_dist_two h two u.prop v.prop (miss u m₁) (miss v m₂))
  have cl : SL.card ≤ 1 := misses_le x s (p.getVert_mem_support i) twoL (pin_data hi).2 univ_x
  have cr : SR.card ≤ 1 := misses_le y t (p.getVert_mem_support j) twoR (pin_data hj).2 univ_y
  have cover : (univ : Finset (Outside p)) ⊆ SL ∪ SR := by
    intro v hv
    by_cases e : G.Adj (v : V) s
    · have vi : i ∈ Pins p (v : V) := mem_filter.mpr ⟨mem_range.mpr (pin_data hi).1,e⟩
      have miss : ¬G.Adj (v : V) t := fun f => st (pin_vertex h hp vi (p.getVert_mem_support j) f)
      exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hv,miss⟩))
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hv,e⟩))
  have a := card_le_card cover
  have b := card_union_le SL SR
  rw [card_univ] at a
  omega

#print axioms minimum_pair_two_impossible
#print axioms adjacent_pair_impossible

private theorem two_on_path_of_extra (hp : IsLongest p) (con : (OGraph p).Connected)
    (ha : 3 ≤ G.degree a) (hb : 3 ≤ G.degree b)
    {x y : Outside p} {i j : ℕ} (hi : i ∈ Pins p (x : V)) (hj : j ∈ Pins p (y : V))
    (ij : i ≠ j) (z : V) (dz : G.dist (x : V) z=2)
    (shape : z ∉ p.support ∨ z = p.getVert j) :
    TwoOnPath p (p.getVert i) := by
  apply pin_has_two_on_path h.con h.even h.conn h.deg hp ha hb x.prop hi
  intro l ll edge
  by_cases e₁ : l=i-1
  · exact Or.inl e₁
  by_cases e₂ : l=i+1
  · exact Or.inr (Or.inl e₂)
  have off_flank : p.getVert l ∉ Flanks p i := by
    intro hl
    rcases mem_insert.mp hl with eq|eq
    · exact e₁ (hp.1.getVert_injOn ll (show i-1 ≤ p.length by have := (pin_data hi).1; omega) eq)
    · exact e₂ (hp.1.getVert_injOn ll (show i+1 ≤ p.length by have := (pin_data hi).1; omega) (mem_singleton.mp eq))
  rcases shape with out|in'
  · exact (off_flank (flank_only h hp hi out dz (p.getVert_mem_support l) edge)).elim
  · subst z
    have d_l : G.dist (x : V) (p.getVert l)=2 := by
      have n : (x : V) ≠ p.getVert l := fun e => x.prop (e ▸ p.getVert_mem_support l)
      have na : ¬G.Adj (x : V) (p.getVert l) := fun e =>
        edge.ne (pin_vertex h hp hi (p.getVert_mem_support l) e)
      exact dist_two h.con n na (pin_data hi).2 edge
    have eq := third_unique h hp hi dz d_l (pin_not_flank h hp con hi hj ij) off_flank
    have eqi := hp.1.getVert_injOn (pin_data hj).1.le ll eq
    subst l
    have gap : i+3≤j ∨ j+3≤i := by
      rcases lt_or_gt_of_ne ij with l|l
      · exact Or.inl (distinct_pins_gap h hp con hi hj l)
      · exact Or.inr (distinct_pins_gap h hp con hj hi l)
    exact Or.inr (Or.inr ⟨(y : V),y.prop,hj,gap⟩)

private theorem against_omitted (hp : IsLongest p) (ha : 3 ≤ G.degree a) (hb : 3 ≤ G.degree b)
    {x₀ : V} (h₀ : x₀ ∉ p.support) : False := by
  classical
  have con := omitted_complement_connected h.con 2 (by decide) h.even h.conn h.deg hp h₀
  obtain ⟨H,_,Hn,Ho,Hc,Hj⟩ := exists_omitted_component h₀
  let C : OmittedComponent p := ⟨H,Hn,Ho,Hc,Hj⟩
  have hH := (component_and_length_bound h.con 2 (by decide) h.even h.conn h.deg hp H Hn Ho Hc Hj).1
  let embed (x : H) : Outside p := ⟨x,Ho x x.prop⟩
  have em : Function.Injective embed := fun _ _ eq => Subtype.ext (congrArg (fun z : Outside p => (z : V)) eq)
  have many : 3 ≤ Fintype.card (Outside p) := hH.trans (by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective embed em)
  have pcard := componentPins_card hp C 2 h.conn
  obtain ⟨u,hu,v,hv,uv⟩ := one_lt_card.mp (show 1 < (componentPins C).card by omega)
  obtain ⟨us,s,ss,sa⟩ := mem_filter.mp hu
  obtain ⟨vs,t,ts,ta⟩ := mem_filter.mp hv
  let s' : Outside p := ⟨s,Ho s ss⟩
  let t' : Outside p := ⟨t,Ho t ts⟩
  obtain ⟨i,hi,ei⟩ := pin_of_neighbor_mem hp s'.prop (List.mem_toFinset.mp us) sa
  obtain ⟨j,hj,ej⟩ := pin_of_neighbor_mem hp t'.prop (List.mem_toFinset.mp vs) ta
  have ij : i ≠ j := by
    intro e
    subst j
    exact uv (ei.symm.trans ej)
  let candidates (n : ℕ) :=
    ∃ (x y : Outside p) (i j : ℕ), i ∈ Pins p (x : V) ∧ j ∈ Pins p (y : V) ∧
      i ≠ j ∧ (OGraph p).dist x y=n
  have none : ∃ n, candidates n := ⟨_,s',t',i,j,hi,hj,ij,rfl⟩
  obtain ⟨x,y,l,r,hl,hr,lr,hdr⟩ := Nat.find_spec none
  have mn (u v : Outside p) (i j : ℕ) (hi : i∈Pins p (u : V)) (hj : j∈Pins p (v : V))
      (ne : i ≠ j) : (OGraph p).dist x y ≤ (OGraph p).dist u v := by
    rw [hdr]
    exact Nat.find_min' none (show candidates ((OGraph p).dist u v) from ⟨u,v,i,j,hi,hj,ne,rfl⟩)
  have xy : x ≠ y := by
    intro hh
    subst y
    exact lr (pin_injective h hp hl hr)
  have positive : 1 ≤ (OGraph p).dist x y := con.pos_dist_of_ne xy
  have short : (OGraph p).dist x y ≤ 2 := minimum_pair_at_most_two h hp con hl hr lr mn
  have alt : (OGraph p).dist x y=1 ∨ (OGraph p).dist x y=2 := by
    by_cases b₁ : (OGraph p).dist x y=1
    · exact Or.inl b₁
    · exact Or.inr (le_antisymm short (lt_of_le_of_ne positive (fun e => b₁ e.symm)))
  rcases alt with one|two
  · have e := dist_eq_one_iff_adj.mp one
    have a₀ : ¬ G.Adj (x : V) (p.getVert r) := by
      intro e'
      have pin := pin_vertex h hp hl (p.getVert_mem_support r) e'
      exact lr (hp.1.getVert_injOn (pin_data hl).1.le (pin_data hr).1.le pin)
    have b₀ : ¬ G.Adj (y : V) (p.getVert l) := by
      intro e'
      have pin := pin_vertex h hp hr (p.getVert_mem_support l) e'
      exact lr.symm (hp.1.getVert_injOn (pin_data hr).1.le (pin_data hl).1.le pin)
    have dx := dist_two h.con (show (x : V) ≠ p.getVert r from fun eq =>
      x.prop (eq ▸ p.getVert_mem_support r)) a₀ (show G.Adj (x : V) (y : V) from e) (pin_data hr).2
    have dy := dist_two h.con (show (y : V) ≠ p.getVert l from fun eq =>
      y.prop (eq ▸ p.getVert_mem_support l)) b₀ (show G.Adj (y : V) (x : V) from e.symm) (pin_data hl).2
    exact adjacent_pair_impossible h hp con hl hr lr e
      (two_on_path_of_extra h hp con ha hb hl hr lr _ dx (Or.inr rfl))
      (two_on_path_of_extra h hp con ha hb hr hl lr.symm _ dy (Or.inr rfl)) many
  · have dxy := off_dist_two h con two
    have dyx := off_dist_two h con (show (OGraph p).dist y x=2 by rw [dist_comm,two])
    exact minimum_pair_two_impossible h hp con hl hr lr two
      (fun u v i j hi hj ne => two ▸ mn u v i j hi hj ne)
      (two_on_path_of_extra h hp con ha hb hl hr lr _ dxy (Or.inl y.prop))
      (two_on_path_of_extra h hp con ha hb hr hl lr.symm _ dyx (Or.inl x.prop))

/-- Written on the Wall II #189 when the second-smallest degree is three
and vertex connectivity is at least two. No finite search is used. -/
theorem traceable_d3_two_connected :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ ∀ v, v ∈ p.support := by
  classical
  obtain ⟨a,b,p,hp⟩ := exists_longest h.con
  by_cases hs : ∀ v, v ∈ p.support
  · exact ⟨a,b,p,hp.1,hs⟩
  · obtain ⟨x,hx⟩ := not_forall.mp hs
    obtain ⟨u,v,q,hq,qs,du,dv⟩ := rotate_to_two_high_endpoints h.con 2 (by decide) h.conn h.deg hp hx
    exact (against_omitted h hq du dv (fun hh => hx ((qs x).mpr hh))).elim

#print axioms traceable_d3_two_connected
end Graffiti189LongestPath.D3
