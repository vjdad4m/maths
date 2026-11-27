import OneSlack189
import Order189

namespace Graffiti189LongestPath.SharpThree
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2500000
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
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem boundary_card_of_connectivity (k : ℕ)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    {x a : V} {A B : Finset V} (hxa : x ∈ A) (haa : a ∉ A) (hab : a ∉ B)
    (hdis : Disjoint A B) (hbound : ∀ y ∈ A, ∀ z ∉ A, G.Adj y z → z ∈ B) :
    k ≤ B.card := by
  by_contra! hsmall
  let W : Set V := (↑B : Set V)ᶜ
  let u : W := ⟨x,fun hb => Finset.disjoint_left.mp hdis hxa hb⟩
  let v : W := ⟨a,hab⟩
  have walk_closed {s t : W} (q : (G.induce W).Walk s t) (hs : (s : V) ∈ A) : (t : V) ∈ A := by
    induction q with
    | nil => exact hs
    | @cons a' b' c' e q ih =>
      apply ih
      by_contra h
      exact b'.prop (hbound a' hs b' h e)
  obtain ⟨q⟩ := (conn B hsmall) u v
  exact haa (walk_closed q hxa)

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

omit [Fintype V] [DecidableEq V] in
private lemma pin_pos {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x ∉ p.support)
    {i : ℕ} (hi : i ∈ Pins p x) : 0 < i := by
  by_contra h
  have e : i=0 := Nat.eq_zero_of_not_pos h
  exact (no_endpoints hp hx).1 (by simpa only [e,getVert_zero] using (pin_data hi).2)


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



variable {a b : V} {p : G.Walk a b} {x : V}
private theorem boundary_lower (k : ℕ) (hp : IsLongest p) (hx : x ∉ p.support)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected) :
    k ≤ (External G (OmittedStar p x)).card := by
  let A := OmittedStar p x
  let B := External G A
  have hxA : x∈A := mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have aA : a∉A := fun e => (mem_omittedStar.mp e).1 p.start_mem_support
  have aB : a∉B := by
    intro e
    obtain ⟨_,z,hz,za⟩ := mem_external.mp e
    exact (no_endpoints hp (mem_omittedStar.mp hz).1).1 za
  have hd : Disjoint A B := by
    rw [disjoint_left]
    exact fun _ h h' => (mem_external.mp h').1 h
  exact boundary_card_of_connectivity k conn hxA aA aB hd
    (fun y hy z hz e => mem_external.mpr ⟨hz,y,hy,e⟩)

private theorem first_pins_nonempty {x : V} (h : (Pins p x).Nonempty) :
    (FirstPins p x).Nonempty := by
  let I := Pins p x
  let m := I.min' h
  have hm : m∈I := I.min'_mem h
  refine ⟨m,mem_filter.mpr ⟨hm,?_⟩⟩
  intro j hj eq
  have le : m≤j := I.min'_le j hj
  omega


/-- The graph assumptions plus reusable D2-only API lemmas. The final
wrapper supplies these fields as theorems, not as axioms. -/
structure Hyp (G : SimpleGraph V) [DecidableRel G.Adj] where
  con : G.Connected
  even : ∀ x, (EvenFrom G x).card≤5
  d2 : ∀ x, (DistanceTwo G x).card≤3
  conn : ∀ S : Finset V, S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected
  degree : ∀ u v : V, u≠v → 4≤G.degree u ∨ 4≤G.degree v
  pin_unique : ∀ {a b x : V} {p : G.Walk a b}, IsLongest p → x∉p.support →
    ∀ i∈Pins p x, ∀ j∈Pins p x, i=j
  rigid : ∀ {a b x : V} {p : G.Walk a b}, IsLongest p → x∉p.support →
    ∀ i∈Pins p x, DistanceTwo G x \ External G (OmittedStar p x) =
      {p.getVert (i-1),p.getVert (i+1)}
  left_chord : ∀ {a b x : V} {p : G.Walk a b}, IsLongest p → x∉p.support →
    ∀ i∈Pins p x, 2≤i → ¬G.Adj a (p.getVert i)
  right_chord : ∀ {a b x : V} {p : G.Walk a b}, IsLongest p → x∉p.support →
    ∀ i∈Pins p x, i+2≤p.length → ¬G.Adj b (p.getVert i)

def Flanks {a b : V} (p : G.Walk a b) (i : ℕ) : Finset V :=
  {p.getVert (i-1),p.getVert (i+1)}

variable (h : Hyp G)
include h

theorem unique_path_neighbor (hp : IsLongest p) (hx : x∉p.support)
    {s t : V} (sp : s∈p.support) (tp : t∈p.support) (xs : G.Adj x s) (xt : G.Adj x t) : s=t := by
  obtain ⟨i,hi,eq⟩ := pin_of_neighbor_mem hp hx sp xs
  obtain ⟨j,hj,eq'⟩ := pin_of_neighbor_mem hp hx tp xt
  have ne := h.pin_unique hp hx i hi j hj
  subst j
  exact eq.symm.trans eq'

omit h in
theorem flank_support {i : ℕ} {z : V} (hz : z∈Flanks p i) : z∈p.support := by
  rcases mem_insert.mp hz with e|e
  · exact e.symm ▸ p.getVert_mem_support (i-1)
  · exact (mem_singleton.mp e).symm ▸ p.getVert_mem_support (i+1)

omit h in
theorem flank_card (hp : IsLongest p) {i : ℕ} (hi : i∈Pins p x) :
    (Flanks p i).card=2 := by
  have il := (pin_data hi).1
  have ne : p.getVert (i-1)≠p.getVert (i+1) := by
    intro e
    have eq := hp.1.getVert_injOn (show i-1≤p.length by omega) (show i+1≤p.length by omega) e
    omega
  simp [Flanks,ne]

/-- Each porter has precisely three distance-two vertices, eccentricity
at most four, and at most one distance-four vertex. -/
theorem active_one_antipode (hp : IsLongest p) (hx : x∉p.support)
    {i : ℕ} (hi : i∈Pins p x) :
    (DistanceTwo G x).card=3 ∧ (∀ v, G.dist x v≤4) ∧ (Shell G x 4).card≤1 := by
  have sz : (Pins p x).card=1 := by
    have up : (Pins p x).card≤1 := card_le_one.mpr (h.pin_unique hp hx)
    have lo : 0<(Pins p x).card := card_pos.mpr ⟨i,hi⟩
    omega
  have f := boundary_flank_count h.con hp hx
  rw [flank_count_exact hp hx,sz] at f
  have b := boundary_lower 2 hp hx h.conn
  have ff := card_pos.mpr (first_pins_nonempty ⟨i,hi⟩)
  have cap := h.d2 x
  have d : (DistanceTwo G x).card=3 := by omega
  refine ⟨d,?_,?_⟩
  · intro v
    by_cases g : G.dist x v≤4
    · exact g
    · exfalso
      have q := twoEvenLayers_of_radius_five h.con 2 h.conn (show 5≤G.dist x v from Nat.lt_of_not_ge g)
      have bound := h.even x
      omega
  · have count := shell_two_four_le_of_even (x:=x) (d:=4) (h.even x)
    rw [shell_two] at count
    omega

theorem at_most_one_far (hp : IsLongest p) (hx : x∉p.support)
    {i : ℕ} (hi : i∈Pins p x) {u v : V} (hu : ¬G.dist x u≤3) (hv : ¬G.dist x v≤3) : u=v := by
  have ⟨_,ecc,cap⟩ := active_one_antipode h hp hx hi
  have a := ecc u
  have b := ecc v
  exact card_le_one.mp cap u (mem_shell.mpr (by omega)) v (mem_shell.mpr (by omega))

theorem third_unique (hp : IsLongest p) (hx : x∉p.support) {i : ℕ}
    (hi : i∈Pins p x) {y z : V}
    (dy : G.dist x y=2) (dz : G.dist x z=2)
    (yf : y∉Flanks p i) (zf : z∉Flanks p i) : y=z := by
  let D := DistanceTwo G x
  let S := Flanks p i
  have sub : S⊆D := by
    intro y hy
    change y∈({p.getVert (i-1),p.getVert (i+1)}:Finset V) at hy
    rw [←h.rigid hp hx i hi] at hy
    exact (mem_sdiff.mp hy).1
  have cnt := card_sdiff_add_card_eq_card sub
  have sz : S.card=2 := flank_card hp hi
  have cp : D.card≤3 := h.d2 x
  have sd : (D \ S).card≤1 := by omega
  exact card_le_one.mp sd y (mem_sdiff.mpr ⟨mem_distanceTwo.mpr dy,yf⟩)
    z (mem_sdiff.mpr ⟨mem_distanceTwo.mpr dz,zf⟩)

theorem pin_gap_of_component (hp : IsLongest p) (H : OmittedComponent p)
    {x y : V} (hx : x∈H.vertices) (hy : y∈H.vertices)
    {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p y) (lt : i<j) : i+3≤j := by
  have nx : x≠y := by
    intro eq
    subst y
    exact (Nat.ne_of_lt lt) (h.pin_unique hp (H.off x hx) i hi j hj)
  obtain ⟨q,hq,hs⟩ := H.joined x hx y hy
  have pos : 0<q.length := by cases q with
    | nil => exact (nx rfl).elim
    | cons adj q => simp
  exact gap_three_of_linked_pins hp hi hj lt q hq pos (fun z hz => H.off z (hs z hz))

theorem flank_sets_disjoint (hp : IsLongest p) (H : OmittedComponent p)
    {x y : V} (hx : x∈H.vertices) (hy : y∈H.vertices)
    {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p y) (ne : i≠j) :
    Disjoint (Flanks p i) (Flanks p j) := by
  have gap : i+3≤j ∨ j+3≤i := by
    rcases lt_or_gt_of_ne ne with l|l
    · exact Or.inl (pin_gap_of_component h hp H hx hy hi hj l)
    · exact Or.inr (pin_gap_of_component h hp H hy hx hj hi l)
  rw [disjoint_left]
  intro z iz jz
  have coords {i : ℕ} (h : z∈Flanks p i) : ∃ l, (l=i-1 ∨ l=i+1) ∧ z=p.getVert l := by
    rcases mem_insert.mp h with e|e
    · exact ⟨_,Or.inl rfl,e⟩
    · exact ⟨_,Or.inr rfl,mem_singleton.mp e⟩
  obtain ⟨r,hr,er⟩ := coords iz
  obtain ⟨s,hs,es⟩ := coords jz
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  have eq := hp.1.getVert_injOn (show r≤p.length by omega) (show s≤p.length by omega) (er.symm.trans es)
  omega

theorem pin_not_other_flank (hp : IsLongest p) (H : OmittedComponent p)
    {x y : V} (hx : x∈H.vertices) (hy : y∈H.vertices)
    {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p y) (ne : i≠j) :
    p.getVert j∉Flanks p i := by
  have gap : i+3≤j ∨ j+3≤i := by
    rcases lt_or_gt_of_ne ne with l|l
    · exact Or.inl (pin_gap_of_component h hp H hx hy hi hj l)
    · exact Or.inr (pin_gap_of_component h hp H hy hx hj hi l)
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  intro hz
  rcases mem_insert.mp hz with e|e
  · have ee := hp.1.getVert_injOn jl.le (show i-1≤p.length by omega) e
    omega
  · have ee := hp.1.getVert_injOn jl.le (show i+1≤p.length by omega) (mem_singleton.mp e)
    omega

#print axioms active_one_antipode

theorem two_porters_of_component (hp : IsLongest p) (H : OmittedComponent p) :
    ∃ x∈H.vertices, ∃ y∈H.vertices, ∃ i∈Pins p x, ∃ j∈Pins p y, i≠j := by
  have hpins := componentPins_card hp H 2 h.conn
  obtain ⟨s,hs,t,ht,ne⟩ := one_lt_card.mp (show 1<(componentPins H).card by omega)
  obtain ⟨ss,x,xH,xs⟩ := mem_filter.mp hs
  obtain ⟨ts,y,yH,yt⟩ := mem_filter.mp ht
  obtain ⟨i,hi,ei⟩ := pin_of_neighbor_mem hp (H.off x xH) (List.mem_toFinset.mp ss) xs
  obtain ⟨j,hj,ej⟩ := pin_of_neighbor_mem hp (H.off y yH) (List.mem_toFinset.mp ts) yt
  refine ⟨x,xH,y,yH,i,hi,j,hj,?_⟩
  intro e
  subst j
  exact ne (ei.symm.trans ej)

private theorem cross_near_flank (hp : IsLongest p) (H K : OmittedComponent p)
    (disj : Disjoint H.vertices K.vertices)
    {x z : V} (hx : x∈H.vertices) (hz : z∈K.vertices) {i : ℕ} (hi : i∈Pins p x)
    (near : G.dist x z≤3) :
    ∃ j∈Pins p z, p.getVert j∈Flanks p i := by
  have no_cross {x y : V} (hx : x∈H.vertices) (hy : y∈K.vertices) : ¬G.Adj x y :=
    fun e => K.off _ hy (H.closed _ hx _ (fun h => disjoint_left.mp disj h hy) e)
  have star_sub {x : V} (hx : x∈H.vertices) : OmittedStar p x⊆H.vertices := by
    intro w hw
    obtain ⟨wo,eq|e⟩ := mem_omittedStar.mp hw
    · exact eq.symm ▸ hx
    · by_cases m : w∈H.vertices
      · exact m
      · exact (wo (H.closed x hx w m e)).elim
  have no_shared {x y v : V} (hx : x∈H.vertices) (hy : y∈K.vertices)
      (vp : v∈p.support) (xv : G.Adj x v) (yv : G.Adj y v) : False := by
    obtain ⟨i,hi,_⟩ := pin_of_neighbor_mem hp (H.off x hx) vp xv
    have ne : x≠y := fun e => disjoint_left.mp disj (e ▸ hx) hy
    have d := mem_distanceTwo.mpr (dist_two h.con ne (no_cross hx hy) xv yv.symm)
    have nb : y∉External G (OmittedStar p x) := by
      intro yb
      obtain ⟨_,w,wA,wy⟩ := mem_external.mp yb
      exact no_cross (star_sub hx wA) hy wy
    have hf := h.rigid hp (H.off x hx) i hi
    have fm := mem_sdiff.mpr ⟨d,nb⟩
    rw [hf] at fm
    exact K.off y hy (flank_support (show y∈Flanks p i from fm))
  have Hstep {u v : V} (uh : u∈H.vertices) (vo : v∉p.support) (e : G.Adj u v) : v∈H.vertices := by
    by_cases HV : v∈H.vertices
    · exact HV
    · exact (vo (H.closed u uh v HV e)).elim
  have Kstep {u v : V} (uk : u∈K.vertices) (vo : v∉p.support) (e : G.Adj u v) : v∈K.vertices := by
    by_cases KV : v∈K.vertices
    · exact KV
    · exact (vo (K.closed u uk v KV e)).elim
  obtain ⟨q,ql⟩ := h.con.exists_walk_length_eq_dist x z
  have len : q.length≤3 := by omega
  rcases short_walk_cases q len with e|e|⟨u,xu,uz⟩|⟨u,v,xu,uv,vz⟩
  · exact (disjoint_left.mp disj (e ▸ hx) hz).elim
  · exact (no_cross hx hz e).elim
  · by_cases up : u∈p.support
    · exact (no_shared hx hz up xu uz.symm).elim
    · exact (no_cross (Hstep hx up xu) hz uz).elim
  · by_cases up : u∈p.support <;> by_cases vp : v∈p.support
    · obtain ⟨j,hj,e⟩ := pin_of_neighbor_mem hp (K.off z hz) vp vz.symm
      have e₀ := unique_path_neighbor h hp (H.off x hx) (p.getVert_mem_support i) up (pin_data hi).2 xu
      have nxv : ¬G.Adj x v := fun g => no_shared hx hz vp g vz.symm
      have xnv : x≠v := fun e => H.off x hx (e.symm ▸ vp)
      have dv := mem_distanceTwo.mpr (dist_two h.con xnv nxv xu uv)
      have vb : v∉External G (OmittedStar p x) := by
        intro vb
        obtain ⟨_,w,wA,wv⟩ := mem_external.mp vb
        exact no_shared (star_sub hx wA) hz vp wv vz.symm
      have hf := h.rigid hp (H.off x hx) i hi
      have vfl : v∈DistanceTwo G x \ External G (OmittedStar p x) := mem_sdiff.mpr ⟨dv,vb⟩
      rw [hf] at vfl
      exact ⟨j,hj,e.symm ▸ vfl⟩
    · have vk := Kstep hz vp vz.symm
      exact (no_shared hx vk up xu uv.symm).elim
    · have uh := Hstep hx up xu
      exact (no_shared uh hz vp uv vz.symm).elim
    · exact (no_cross (Hstep hx up xu) (Kstep hz vp vz.symm) uv).elim

private theorem not_two_foreign_pin_reaches (hp : IsLongest p) (H K : OmittedComponent p)
    (disj : Disjoint H.vertices K.vertices)
    {x y z : V} (hx : x∈H.vertices) (hy : y∈K.vertices) (hz : z∈K.vertices)
    {i j k : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p y) (hk : k∈Pins p z) (ne : j≠k)
    (xy : G.dist x y≤3) (xz : G.dist x z≤3) : False := by
  obtain ⟨j',hj',fj⟩ := cross_near_flank h hp H K disj hx hy hi xy
  obtain ⟨k',hk',fk⟩ := cross_near_flank h hp H K disj hx hz hi xz
  have ej := h.pin_unique hp (K.off y hy) j hj j' hj'
  have ek := h.pin_unique hp (K.off z hz) k hk k' hk'
  subst j'
  subst k'
  have gap : j+3≤k ∨ k+3≤j := by
    rcases lt_or_gt_of_ne ne with l|l
    · exact Or.inl (pin_gap_of_component h hp K hy hz hj hk l)
    · exact Or.inr (pin_gap_of_component h hp K hz hy hk hj l)
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  have kl := (pin_data hk).1
  have idx (r : ℕ) (hr : r≤p.length) (hh : p.getVert r∈Flanks p i) :
      r=i-1 ∨ r=i+1 := by
    rcases mem_insert.mp hh with e|e
    · exact Or.inl (hp.1.getVert_injOn hr (show i-1≤p.length by omega) e)
    · exact Or.inr (hp.1.getVert_injOn hr (show i+1≤p.length by omega) (mem_singleton.mp e))
  have e₁ := idx j jl.le fj
  have e₂ := idx k kl.le fk
  omega

/-- Under the one-antipode condition, two omitted components are still
impossible: their two far vertices must be different singletons, and
every remaining vertex would need to live in both disjoint flank sets. -/
theorem no_disjoint_components (hp : IsLongest p) (H K : OmittedComponent p)
    (disj : Disjoint H.vertices K.vertices) : False := by
  classical
  obtain ⟨x,xh,u,uh,i,hi,j,hj,ij⟩ := two_porters_of_component h hp H
  obtain ⟨y,yk,z,zk,r,hr,s,hs,rs⟩ := two_porters_of_component h hp K
  have fs := flank_sets_disjoint h hp H xh uh hi hj ij
  have yz : y≠z := by
    intro e
    subst z
    exact rs (h.pin_unique hp (K.off y yk) r hr s hs)
  have fallback {y z : V} (yk : y∈K.vertices) (zk : z∈K.vertices)
      {r s : ℕ} (hr : r∈Pins p y) (hs : s∈Pins p z) (rs : r≠s) (xy : G.dist x y≤3) :
      K.vertices ⊆ {y,z} := by
    have xz : ¬G.dist x z≤3 :=
      not_two_foreign_pin_reaches h hp H K disj xh yk zk hi hr hs rs xy
    obtain ⟨r',hr',yf⟩ := cross_near_flank h hp H K disj xh yk hi xy
    have er := h.pin_unique hp (K.off y yk) r hr r' hr'
    subst r'
    have uy : ¬G.dist u y≤3 := by
      intro uy
      obtain ⟨r',hr',yf'⟩ := cross_near_flank h hp H K disj uh yk hj uy
      have er := h.pin_unique hp (K.off y yk) r hr r' hr'
      subst r'
      exact disjoint_left.mp fs yf yf'
    intro w wk
    by_cases wy : w=y
    · exact mem_insert.mpr (Or.inl wy)
    by_cases wz : w=z
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr wz))
    have xw : G.dist x w≤3 := by
      by_cases ht : G.dist x w≤3
      · exact ht
      · exact (wz (at_most_one_far h hp (H.off x xh) hi ht xz)).elim
    have uw : G.dist u w≤3 := by
      by_cases ht : G.dist u w≤3
      · exact ht
      · exact (wy (at_most_one_far h hp (H.off u uh) hj ht uy)).elim
    obtain ⟨k,hk,wf⟩ := cross_near_flank h hp H K disj xh wk hi xw
    obtain ⟨l,hl,wg⟩ := cross_near_flank h hp H K disj uh wk hj uw
    have eq := h.pin_unique hp (K.off w wk) k hk l hl
    subst l
    exact (disjoint_left.mp fs wf wg).elim
  have small : K.vertices.card≤2 := by
    by_cases xy : G.dist x y≤3
    · exact (card_le_card (fallback yk zk hr hs rs xy)).trans
        (by simpa only [card_singleton] using card_insert_le y ({z}:Finset V))
    · have xz : G.dist x z≤3 := by
        by_cases f : G.dist x z≤3
        · exact f
        · exact (yz (at_most_one_far h hp (H.off x xh) hi xy f)).elim
      exact (card_le_card (fallback zk yk hs hr rs.symm xz)).trans
        (by simpa only [card_singleton] using card_insert_le z ({y}:Finset V))
  have low (v : V) (vk : v∈K.vertices) : G.degree v≤2 := by
    let E := (G.neighborFinset v).filter (·∉K.vertices)
    have ecard : E.card≤1 := by
      apply card_le_one.mpr
      intro s hs t ht
      have ⟨n₁,h₁⟩ := mem_filter.mp hs
      have ⟨n₂,h₂⟩ := mem_filter.mp ht
      have ae := (G.mem_neighborFinset _ _).mp n₁
      have be := (G.mem_neighborFinset _ _).mp n₂
      exact unique_path_neighbor h hp (K.off v vk)
        (K.closed v vk s h₁ ae) (K.closed v vk t h₂ be) ae be
    have sub : G.neighborFinset v ⊆ K.vertices.erase v ∪ E := by
      intro u uu
      by_cases h : u∈K.vertices
      · exact mem_union.mpr (Or.inl (mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp uu).ne.symm,h⟩))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨uu,h⟩))
    have c := card_le_card sub
    rw [G.card_neighborFinset_eq_degree] at c
    have c' := card_union_le (K.vertices.erase v) E
    have e := card_erase_add_one vk
    omega
  have yo := low y yk
  have zo := low z zk
  rcases h.degree y z yz with e|e <;> omega

#print axioms no_disjoint_components

/-- The omitted vertices form a single component. -/
theorem actual_omitted_component (hp : IsLongest p) (hx : x∉p.support) :
    ∃ H : OmittedComponent p, ∀ z, z∈H.vertices ↔ z∉p.support := by
  classical
  obtain ⟨A,xA,An,Ao,Ac,Aj⟩ := exists_omitted_component hx
  let H : OmittedComponent p := ⟨A,An,Ao,Ac,Aj⟩
  refine ⟨H,?_⟩
  intro z
  constructor
  · exact Ao z
  intro zo
  by_cases n : z∈A
  · exact n
  · obtain ⟨B,zB,Bn,Bo,Bc,Bj⟩ := exists_omitted_component zo
    let K : OmittedComponent p := ⟨B,Bn,Bo,Bc,Bj⟩
    exfalso
    apply no_disjoint_components h hp H K
    rw [disjoint_left]
    intro w wa wb
    obtain ⟨q,_,hs⟩ := Bj w wb z zB
    have follow {s t : V} (r : G.Walk s t) (hs : ∀ w∈r.support,w∈B)
        (sa : s∈A) : t∈A := by
      induction r with
      | nil => exact sa
      | @cons u v e h' q ih =>
        have vb : v∈B := hs v (by simp)
        have va : v∈A := by
          by_cases b : v∈A
          · exact b
          · exact (Bo v vb (Ac u sa v b h')).elim
        exact ih (fun v hv => hs v (by simp [hv])) va
    exact n (follow q hs wa)

#print axioms actual_omitted_component
end Graffiti189LongestPath.SharpThree
