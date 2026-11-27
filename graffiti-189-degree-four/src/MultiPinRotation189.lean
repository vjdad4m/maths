import OneSlack189

namespace Graffiti189LongestPath.OneSlack.MultiRotation
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2200000
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




variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
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



variable {a b : V} {p : G.Walk a b} {x : V}
private lemma mem_distanceTwo {x y : V} : y∈DistanceTwo G x ↔ G.dist x y=2 := by
  classical
  simp [DistanceTwo]

private theorem card_pinVertices (hp : IsLongest p) :
    (PinVertices p x).card = (Pins p x).card := by
  apply card_image_iff.mpr
  intro i hi j hj e
  exact hp.1.getVert_injOn (pin_data hi).1.le (pin_data hj).1.le e

private theorem cardinal_flankVertices (hp : IsLongest p) :
    (FlankVertices p x).card = (FlankIndices p x).card := by
  have upper (i : ℕ) (hi : i∈FlankIndices p x) : i≤p.length := by
    rcases mem_union.mp hi with hi|hi
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      have := (pin_data hj).1
      change j-1≤p.length
      omega
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      have := (pin_data hj).1
      change j+1≤p.length
      omega
  apply card_image_iff.mpr
  intro i hi j hj e
  exact hp.1.getVert_injOn (upper i hi) (upper j hj) e

private theorem pin_vertices_subset_boundary (hx : x ∉ p.support) :
    PinVertices p x ⊆ External G (OmittedStar p x) := by
  intro z hz
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
  exact mem_external.mpr
    ⟨fun e => (mem_omittedStar.mp e).1 (p.getVert_mem_support i),x,mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩,(pin_data hi).2⟩

private theorem boundary_except_pins_two (hc : G.Connected) (hp : IsLongest p)
    (hx : x ∉ p.support) : External G (OmittedStar p x) \ PinVertices p x ⊆ DistanceTwo G x := by
  intro v hv
  obtain ⟨vb,nvp⟩ := mem_sdiff.mp hv
  obtain ⟨nva,z,za,zv⟩ := mem_external.mp vb
  have star : x∈OmittedStar p x := mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
  have xv : x≠v := fun e => nva (e ▸ star)
  have nxv : ¬G.Adj x v := by
    intro e
    by_cases vp : v∈p.support
    · obtain ⟨i,hi,iv⟩ := pin_of_neighbor_mem hp hx vp e
      exact nvp (mem_image.mpr ⟨i,hi,iv⟩)
    · exact nva (mem_omittedStar.mpr ⟨vp,Or.inr e⟩)
  obtain ⟨_,eq|xz⟩ := mem_omittedStar.mp za
  · exact (nxv (eq ▸ zv)).elim
  · exact mem_distanceTwo.mpr (dist_two hc xv nxv xz zv)

private theorem first_pins_nonempty {x : V} (h : (Pins p x).Nonempty) :
    (FirstPins p x).Nonempty := by
  let I := Pins p x
  let m := I.min' h
  have hm : m∈I := I.min'_mem h
  refine ⟨m,mem_filter.mpr ⟨hm,?_⟩⟩
  intro j hj eq
  have le : m≤j := I.min'_le j hj
  omega

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
private lemma split_path_edge {a b : V} (p : G.Walk a b) (j : ℕ) (hj : j < p.length) :
    (p.take j).append (.cons (p.adj_getVert_succ hj) (p.drop (j+1))) = p := by
  induction p generalizing j with
  | nil => simp at hj
  | @cons a u b edge p ih =>
    cases j with
    | zero =>
      have h : HEq (p.drop 0) p := by cases p <;> rfl
      simpa [Walk.take,Walk.drop] using h
    | succ j =>
      have hj' : j < p.length := by simpa using hj
      exact congrArg (Walk.cons edge) (ih j hj')


private lemma pin_mem_iff (hp : IsLongest p) (hx : x∉p.support) {z : V} :
    z∈PinVertices p x ↔ z∈p.support ∧ G.Adj x z := by
  constructor
  · intro hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    exact ⟨p.getVert_mem_support i,(pin_data hi).2⟩
  · rintro ⟨zs,e⟩
    obtain ⟨i,hi,ei⟩ := pin_of_neighbor_mem hp hx zs e
    exact mem_image.mpr ⟨i,hi,ei⟩

private lemma rigidity_of_tight (hc : G.Connected) (hp : IsLongest p) (hx : x∉p.support)
    (tight : (External G (OmittedStar p x)).card + (FlankVertices p x).card =
       (DistanceTwo G x).card + (PinVertices p x).card) :
    DistanceTwo G x \ External G (OmittedStar p x) = FlankVertices p x := by
  let B := External G (OmittedStar p x)
  let F := PinVertices p x
  let T := DistanceTwo G x \ B
  have sub : FlankVertices p x⊆T := flanks_outside_boundary hc hp hx
  have out : B \ F ⊆ DistanceTwo G x := boundary_except_pins_two hc hp hx
  have dis : Disjoint T (B \ F) := by
    rw [disjoint_left]
    exact fun _ h h' => (mem_sdiff.mp h).2 (mem_sdiff.mp h').1
  have su : T ∪ (B \ F) ⊆ DistanceTwo G x :=
    union_subset (fun _ h => (mem_sdiff.mp h).1) out
  have c := card_le_card su
  rw [card_union_of_disjoint dis] at c
  have s := card_sdiff_add_card_eq_card (pin_vertices_subset_boundary hx)
  change (B \ F).card+F.card=B.card at s
  change B.card+(FlankVertices p x).card=(DistanceTwo G x).card+F.card at tight
  symm
  exact eq_of_subset_of_card_le sub (by change T.card≤(FlankVertices p x).card; omega)

/-- Pósa rotation with the full coordinate description. -/
theorem rotate_start_map (hp : IsLongest p) (j : ℕ) (hj : j<p.length)
    (jump : G.Adj a (p.getVert (j+1))) :
    ∃ q : G.Walk (p.getVert j) b, IsLongest q ∧
      (∀ z : V, z∈p.support ↔ z∈q.support) ∧ q.length=p.length ∧
      ∀ i≤p.length, q.getVert i = p.getVert (if i≤j then j-i else i) := by
  let l := p.take j
  let r := p.drop (j+1)
  let q := l.reverse.append (.cons jump r)
  have split := split_path_edge p j hj
  have ps : p.support = l.support ++ r.support := by
    conv_lhs => rw [←split]
    simp only [support_append,support_cons,List.tail_cons,l,r]
  have qs : q.support = l.support.reverse ++ r.support := by
    simp only [q,support_append,support_reverse,support_cons,List.tail_cons]
  have qpath : q.IsPath := by
    rw [isPath_def,qs,List.nodup_append]
    have nod := hp.1.support_nodup
    rw [ps,List.nodup_append] at nod
    refine ⟨List.nodup_reverse.mpr nod.1,nod.2.1,?_⟩
    intro u hu hv
    exact nod.2.2 (List.mem_reverse.mp hu) hv
  have qsupport (z : V) : z∈p.support ↔ z∈q.support := by rw [ps,qs]; simp
  have llen : l.length=j := (lengths_take_drop p j (by omega)).1
  have rlen : r.length=p.length-(j+1) := (lengths_take_drop p (j+1) (by omega)).2
  have qlen : q.length=p.length := by
    simp only [q,length_append,length_reverse,length_cons,llen,rlen]
    omega
  have qmax : IsLongest q := ⟨qpath,fun u v w hw => qlen.symm ▸ hp.2 u v w hw⟩
  have original (n : ℕ) (hn : n≤j) : l.getVert n = p.getVert n := by
    by_cases eq : n=j
    · subst n
      simpa only [llen] using l.getVert_length
    · have cut : n<l.length := by omega
      have c := congrArg (fun w : G.Walk a b => w.getVert n) split
      change (l.append (.cons (p.adj_getVert_succ hj) r)).getVert n = p.getVert n at c
      rw [getVert_append,if_pos cut] at c
      exact c
  refine ⟨q,qmax,qsupport,qlen,?_⟩
  intro n hn
  by_cases ne : n≤j
  · rw [if_pos ne]
    by_cases eq : n=j
    · subst n
      simp [q,getVert_append,llen]
    · have hs : n<l.reverse.length := by rw [length_reverse,llen]; omega
      change (l.reverse.append _).getVert n = _
      rw [getVert_append,if_pos hs,getVert_reverse,llen]
      exact original _ (by omega)
  · rw [if_neg ne]
    have cut : ¬ n<l.length := by omega
    have cut' : ¬ n<l.reverse.length := by rwa [length_reverse]
    have c := congrArg (fun w : G.Walk a b => w.getVert n) split
    change (l.append (.cons (p.adj_getVert_succ hj) r)).getVert n = p.getVert n at c
    rw [getVert_append,if_neg cut] at c
    change (l.reverse.append _).getVert n = _
    rw [getVert_append,if_neg cut',length_reverse,←c]
    have hn' : 0<n-l.length := by omega
    obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n-l.length≠0)
    rw [ht]
    rfl

private lemma same_support_star {a' b' : V} {q : G.Walk a' b'}
    (same : ∀ v, v∈p.support ↔ v∈q.support) : OmittedStar p x = OmittedStar q x := by
  ext z
  rw [mem_omittedStar,mem_omittedStar,same z]

private lemma same_support_pin_count {a' b' : V} {q : G.Walk a' b'} (hp : IsLongest p)
    (hq : IsLongest q) (hx : x∉p.support)
    (same : ∀ v, v∈p.support ↔ v∈q.support) : (Pins p x).card = (Pins q x).card := by
  have hq' : x∉q.support := fun e => hx ((same x).mpr e)
  have set_eq : PinVertices p x = PinVertices q x := by
    ext z
    rw [pin_mem_iff hp hx,pin_mem_iff hq hq',same z]
  rw [←card_pinVertices hp,set_eq,card_pinVertices hq]

private lemma flank_on_left {i : ℕ} (hi : i∈Pins p x) :
    p.getVert (i-1)∈FlankVertices p x :=
  mem_image.mpr ⟨i-1,mem_union.mpr (Or.inl (mem_image.mpr ⟨i,hi,rfl⟩)),rfl⟩

private lemma left_endpoint_not_flank (hp : IsLongest p)
    (internal : ∀ i∈Pins p x, 2≤i) : a∉FlankVertices p x := by
  intro e
  obtain ⟨i,withfl,ie⟩ := mem_image.mp e
  have ee := ie.trans p.getVert_zero.symm
  rcases mem_union.mp withfl with h|h
  · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
    have lt := (pin_data hj).1
    have he := hp.1.getVert_injOn (show j-1≤p.length by omega) (show 0≤p.length by omega) ee
    have hi := internal j hj
    omega
  · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
    have lt := (pin_data hj).1
    have he := hp.1.getVert_injOn (show j+1≤p.length by omega) (show 0≤p.length by omega) ee
    omega

private lemma chord_forces_first_fringe (hc : G.Connected) (hp : IsLongest p)
    (hx : x∉p.support) {i : ℕ} (hi : i∈Pins p x) (internal : ∀ i∈Pins p x, 2≤i)
    (rigid : DistanceTwo G x \ External G (OmittedStar p x) = FlankVertices p x) :
    ¬G.Adj a (p.getVert i) := by
  intro h
  have hip := internal i hi
  have hil := (pin_data hi).1
  have shift : i-1+1=i := by omega
  obtain ⟨q,hq,same,ql,map⟩ := rotate_start_map hp (i-1) (by omega) (by simpa only [shift] using h)
  have hqi : q.getVert i = p.getVert i := by
    have e := map i hil.le
    rw [if_neg (by omega : ¬ i≤i-1)] at e
    exact e
  have qmem : i∈Pins q x := mem_filter.mpr ⟨mem_range.mpr (by omega),by rw [hqi]; exact (pin_data hi).2⟩
  have qx : x∉q.support := fun e => hx ((same x).mpr e)
  have hf := flank_on_left qmem
  have qprev : q.getVert (i-1)=a := by
    have e := map (i-1) (by omega)
    simpa only [le_rfl,if_true,Nat.sub_self,getVert_zero] using e
  have hor := flanks_outside_boundary hc hq qx hf
  rw [qprev,←same_support_star (x:=x) same,rigid] at hor
  exact left_endpoint_not_flank hp internal hor

#print axioms rotate_start_map

private lemma singleton_pins_eq {i : ℕ} (hi : i∈Pins p x) (size : (Pins p x).card=1) :
    Pins p x={i} := by
  symm
  apply eq_of_subset_of_card_le
  · intro j hj
    exact (mem_singleton.mp hj).symm ▸ hi
  · rw [size,card_singleton]

private lemma double_pins_eq {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p x)
    (size : (Pins p x).card=2) (ne : i≠j) : Pins p x={i,j} := by
  symm
  apply eq_of_subset_of_card_le
  · intro t ht
    rcases mem_insert.mp ht with rfl|h
    · exact hi
    · exact (mem_singleton.mp h).symm ▸ hj
  · simp [size,ne]

private lemma local_rigid_from_card (hc : G.Connected) (hp : IsLongest p)
    (hx : x∉p.support) (s : ℕ)
    (size : (Pins p x).card=s) (cap : (DistanceTwo G x).card≤4)
    (bl : 3≤(External G (OmittedStar p x)).card)
    (fl : s+1≤(FlankVertices p x).card) :
    DistanceTwo G x \ External G (OmittedStar p x) = FlankVertices p x := by
  have c := boundary_flank_count hc hp hx
  rw [←cardinal_flankVertices hp,size] at c
  apply rigidity_of_tight hc hp hx
  rw [card_pinVertices hp,size]
  omega

/-- A singleton pin with a full local boundary may not have a chord to
the initial endpoint, unless it is the first internal vertex. -/
theorem singleton_left_chord (hc : G.Connected) (hp : IsLongest p)
    (hx : x∉p.support) {i : ℕ} (hi : i∈Pins p x) (size : (Pins p x).card=1)
    (cap : (DistanceTwo G x).card≤4)
    (bl : 3≤(External G (OmittedStar p x)).card)
    (edge : G.Adj a (p.getVert i)) : i=1 := by
  by_contra! ne
  have lo := pin_pos hp hx hi
  have rigid := local_rigid_from_card hc hp hx 1 size cap bl (by
    rw [cardinal_flankVertices hp,flank_count_exact hp hx,size]
    have c := card_pos.mpr (first_pins_nonempty ⟨i,hi⟩)
    omega)
  have ie := singleton_pins_eq hi size
  have internal : ∀ j∈Pins p x, 2≤j := by
    intro j hj
    rw [ie,mem_singleton] at hj
    omega
  exact chord_forces_first_fringe hc hp hx hi internal rigid edge

/-- For a paired double porter with a full local boundary, a chord
from the initial endpoint to either pin forces the first pin at index 1. -/
theorem paired_left_chord (hc : G.Connected) (hp : IsLongest p)
    (hx : x∉p.support) {i : ℕ} (hi : i∈Pins p x) (hj : i+2∈Pins p x)
    (size : (Pins p x).card=2) (cap : (DistanceTwo G x).card≤4)
    (bl : 3≤(External G (OmittedStar p x)).card)
    (edge : G.Adj a (p.getVert i) ∨ G.Adj a (p.getVert (i+2))) : i=1 := by
  by_contra! ne
  have lo := pin_pos hp hx hi
  have up := (pin_data hj).1
  have ie := double_pins_eq hi hj size (by omega)
  rcases edge with l|r
  · have internal : ∀ j∈Pins p x, 2≤j := by
      intro j hj'
      rw [ie] at hj'
      rcases mem_insert.mp hj' with e|e
      · omega
      · have e' := mem_singleton.mp e
        omega
    have rigid := local_rigid_from_card hc hp hx 2 size cap bl (by
      rw [cardinal_flankVertices hp,flank_count_exact hp hx,size]
      have c := card_pos.mpr (first_pins_nonempty ⟨i,hi⟩)
      omega)
    exact chord_forces_first_fringe hc hp hx hi internal rigid l
  · obtain ⟨q,hq,same,ql,map⟩ := rotate_start_map hp (i+1) (by omega) r
    have q₁ : q.getVert 1=p.getVert i := by
      have e := map 1 (by omega)
      have ne : 1≤i+1 := by omega
      have e₁ : i+1-1=i := by omega
      simpa only [if_pos ne,e₁] using e
    have q₂ : q.getVert (i+2)=p.getVert (i+2) := by
      have e := map (i+2) up.le
      have ne : ¬ i+2≤i+1 := by omega
      simpa only [if_neg ne] using e
    have qx : x∉q.support := fun e => hx ((same x).mpr e)
    have q₁mem : 1∈Pins q x := mem_filter.mpr ⟨mem_range.mpr (by omega),by rw [q₁]; exact (pin_data hi).2⟩
    have q₂mem : i+2∈Pins q x := mem_filter.mpr ⟨mem_range.mpr (by omega),by rw [q₂]; exact (pin_data hj).2⟩
    have fs := same_support_pin_count hp hq hx same
    have big := (two_separated_pins_cap_four hc hq qx (by omega) cap q₁mem q₂mem (by omega)).2.1
    have bq : 3≤(External G (OmittedStar q x)).card := by
      rw [←same_support_star (x:=x) same]
      exact bl
    rw [big] at bq
    have small := card_insert_le (q.getVert 1) ({q.getVert (i+2)} : Finset V)
    rw [card_singleton] at small
    omega

private lemma reverse_longest {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    IsLongest p.reverse := ⟨hp.1.reverse,fun u v q hq => by simpa using hp.2 u v q hq⟩

private lemma pin_reverse {i : ℕ} (hp : IsLongest p) (hx : x∉p.support) (hi : i∈Pins p x) :
    p.length-i∈Pins p.reverse x := by
  have h := (pin_data hi).1
  have g := pin_pos hp hx hi
  apply mem_filter.mpr
  constructor
  · rw [mem_range,length_reverse]
    omega
  · rw [getVert_reverse]
    have shift : p.length-(p.length-i)=i := by omega
    rw [shift]
    exact (pin_data hi).2

theorem singleton_right_chord (hc : G.Connected) (hp : IsLongest p)
    (hx : x∉p.support) {i : ℕ} (hi : i∈Pins p x) (size : (Pins p x).card=1)
    (cap : (DistanceTwo G x).card≤4)
    (bl : 3≤(External G (OmittedStar p x)).card)
    (edge : G.Adj b (p.getVert i)) : i+1=p.length := by
  have hs (z : V) : z∈p.support ↔ z∈p.reverse.support := by simp
  have hp' := reverse_longest hp
  have hx' : x∉p.reverse.support := fun m => hx ((hs _).mpr m)
  have e : G.Adj b (p.reverse.getVert (p.length-i)) := by
    rw [getVert_reverse]
    have h : p.length-(p.length-i)=i := by have := (pin_data hi).1; omega
    rwa [h]
  have sz := same_support_pin_count hp hp' hx hs
  have nn : 3≤(External G (OmittedStar p.reverse x)).card := by
    rwa [←same_support_star (x:=x) hs]
  have h := singleton_left_chord hc hp' hx' (pin_reverse hp hx hi) (by omega) cap nn e
  have up := (pin_data hi).1
  omega

theorem paired_right_chord (hc : G.Connected) (hp : IsLongest p)
    (hx : x∉p.support) {i : ℕ} (hi : i∈Pins p x) (hj : i+2∈Pins p x)
    (size : (Pins p x).card=2) (cap : (DistanceTwo G x).card≤4)
    (bl : 3≤(External G (OmittedStar p x)).card)
    (edge : G.Adj b (p.getVert i) ∨ G.Adj b (p.getVert (i+2))) : i+3=p.length := by
  have hs (z : V) : z∈p.support ↔ z∈p.reverse.support := by simp
  have hp' := reverse_longest hp
  have hx' : x∉p.reverse.support := fun m => hx ((hs _).mpr m)
  have up := (pin_data hj).1
  let j := p.length-(i+2)
  have ji : j+2=p.length-i := by omega
  have h₁ : j∈Pins p.reverse x := pin_reverse hp hx hj
  have h₂ : j+2∈Pins p.reverse x := ji.symm ▸ pin_reverse hp hx hi
  have es : G.Adj b (p.reverse.getVert j) ∨ G.Adj b (p.reverse.getVert (j+2)) := by
    rw [ji,getVert_reverse,getVert_reverse]
    have q₁ : p.length-j=i+2 := by omega
    have q₂ : p.length-(p.length-i)=i := by omega
    rw [q₁,q₂]
    exact edge.symm
  have sz := same_support_pin_count hp hp' hx hs
  have nn : 3≤(External G (OmittedStar p.reverse x)).card := by
    rwa [←same_support_star (x:=x) hs]
  have hh := paired_left_chord hc hp' hx' h₁ h₂ (by omega) cap nn es
  omega

#print axioms paired_left_chord
#print axioms paired_right_chord

private def LeftMarks {a b : V} (p : G.Walk a b) : Finset ℕ :=
  (range p.length).filter fun i => G.Adj a (p.getVert (i+1))

private def RightMarks {a b : V} (p : G.Walk a b) : Finset ℕ :=
  (range p.length).filter fun i => G.Adj b (p.getVert i)

private theorem card_leftMarks {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    (LeftMarks p).card = G.degree a := by
  classical
  have eq : (LeftMarks p).image (fun i => p.getVert (i+1)) = G.neighborFinset a := by
    ext z
    rw [G.mem_neighborFinset,mem_image]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact (mem_filter.mp hi).2
    · intro e
      have zs : z ∈ p.support := by
        by_contra h
        exact (no_endpoints hp h).1 e.symm
      obtain ⟨i,ei,il⟩ := mem_support_iff_exists_getVert.mp zs
      have ip : 0<i := by
        by_contra h
        have he : i=0 := by omega
        rw [he,getVert_zero] at ei
        exact e.ne ei
      have iq : i-1+1=i := by omega
      exact ⟨i-1,mem_filter.mpr ⟨mem_range.mpr (by omega),by rwa [iq,ei]⟩,by rwa [iq]⟩
  have inj : ((LeftMarks p).image (fun i => p.getVert (i+1))).card = (LeftMarks p).card := by
    apply card_image_iff.mpr
    intro i hi j hj e
    have il := mem_range.mp (mem_filter.mp hi).1
    have jl := mem_range.mp (mem_filter.mp hj).1
    have h := hp.1.getVert_injOn (show i+1≤p.length by omega) (show j+1≤p.length by omega) e
    omega
  rw [eq,card_neighborFinset_eq_degree] at inj
  exact inj.symm

private theorem card_rightMarks {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    (RightMarks p).card = G.degree b := by
  classical
  have eq : (RightMarks p).image p.getVert = G.neighborFinset b := by
    ext z
    rw [G.mem_neighborFinset,mem_image]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact (mem_filter.mp hi).2
    · intro e
      have zs : z ∈ p.support := by
        by_contra h
        exact (no_endpoints hp h).2 e.symm
      obtain ⟨i,ei,il⟩ := mem_support_iff_exists_getVert.mp zs
      have ip : i < p.length := by
        by_contra h
        have he : i=p.length := by omega
        rw [he,getVert_length] at ei
        exact e.ne ei
      exact ⟨i,mem_filter.mpr ⟨mem_range.mpr ip,by rwa [ei]⟩,ei⟩
  have inj : ((RightMarks p).image p.getVert).card = (RightMarks p).card := by
    apply card_image_iff.mpr
    intro i hi j hj e
    have il := mem_range.mp (mem_filter.mp hi).1
    have jl := mem_range.mp (mem_filter.mp hj).1
    exact hp.1.getVert_injOn il.le jl.le e
  rw [eq,card_neighborFinset_eq_degree] at inj
  exact inj.symm


/-- The three-pin arrangement consisting of a paired double porter and
a singleton with tight local boundaries needs at least twelve path
vertices when both endpoint degrees are at least four. -/
theorem path_order_ge_twelve (hc : G.Connected) (hp : IsLongest p)
    (a₄ : 4≤G.degree a) (b₄ : 4≤G.degree b)
    (hx : x∉p.support) {i : ℕ} (hi : i∈Pins p x) (hj : i+2∈Pins p x)
    (size : (Pins p x).card=2) (cap : (DistanceTwo G x).card≤4)
    (bl : 3≤(External G (OmittedStar p x)).card)
    {y : V} (hy : y∉p.support) {j : ℕ} (hjy : j∈Pins p y) (sz : (Pins p y).card=1)
    (capy : (DistanceTwo G y).card≤4) (bly : 3≤(External G (OmittedStar p y)).card)
    (apart₁ : i+3≤j ∨ j+3≤i) (apart₂ : i+5≤j ∨ j+3≤i+2) :
    12≤p.length+1 := by
  classical
  let L := LeftMarks p
  let R := RightMarks p
  have ldeg : L.card=G.degree a := card_leftMarks hp
  have rdeg : R.card=G.degree b := card_rightMarks hp
  have marked : L ∪ R ⊆ range p.length := by
    intro t ht
    exact (mem_union.mp ht).elim (fun h => (mem_filter.mp h).1) (fun h => (mem_filter.mp h).1)
  have dis : Disjoint L R := by
    rw [disjoint_left]
    intro t ht hu
    obtain ⟨ttl,ea⟩ := mem_filter.mp ht
    exact not_adj_both_end_marks hp hx (p.getVert_mem_support i) (pin_data hi).2
      (mem_range.mp ttl) ea (mem_filter.mp hu).2
  have lower := card_le_card marked
  rw [card_union_of_disjoint dis,ldeg,rdeg,card_range] at lower
  let I := ({i,i+2,j}:Finset ℕ)
  have iPos := pin_pos hp hx hi
  have jPos := pin_pos hp hy hjy
  have iLt := (pin_data hj).1
  have jLt := (pin_data hjy).1
  have pos (t : ℕ) (h : t∈I) : 0<t ∧ t<p.length := by
    simp only [I,mem_insert,mem_singleton] at h
    rcases h with rfl|rfl|rfl <;> omega
  have ic : I.card=3 := by
    have ne : i≠i+2 := by omega
    have ne₁ : i≠j := by omega
    have ne₂ : i+2≠j := by omega
    have no₁ : i∉({i+2,j}:Finset ℕ) := fun h =>
      (mem_insert.mp h).elim ne (fun h=>ne₁ (mem_singleton.mp h))
    have no₂ : i+2∉({j}:Finset ℕ) := fun h => ne₂ (mem_singleton.mp h)
    change ({i,i+2,j}:Finset ℕ).card=3
    rw [card_insert_of_not_mem no₁,card_insert_of_not_mem no₂,card_singleton]
  let J := I.image (·-1)
  have jc : J.card=I.card := by
    apply card_image_iff.mpr
    intro v hv w hw e
    have a := (pos v hv).1
    have b := (pos w hw).1
    change v-1=w-1 at e
    omega
  have ij : Disjoint I J := by
    rw [disjoint_left]
    intro t ht h
    obtain ⟨w,hw,e⟩ := mem_image.mp h
    have wpos := (pos w hw).1
    change w-1=t at e
    simp only [I,mem_insert,mem_singleton] at ht hw
    rcases ht with rfl|rfl|rfl <;> rcases hw with rfl|rfl|rfl <;> omega
  let U := I ∪ J
  have uc : U.card=6 := by
    rw [card_union_of_disjoint ij,jc,ic]
  have u_rng : U ⊆ range p.length := by
    intro t hu
    rcases mem_union.mp hu with e|e
    · exact mem_range.mpr (pos t e).2
    · obtain ⟨v,hv,rfl⟩ := mem_image.mp e
      have h := (pos v hv).2
      exact mem_range.mpr (by omega)
  let EL : Finset ℕ := if i=1 then {i-1,i+1} else if j=1 then {j-1} else ∅
  let ER : Finset ℕ := if i+3=p.length then {i,i+2} else if j+1=p.length then {j} else ∅
  have el_no : i≠1 → EL.card≤1 := by
    intro ne
    change (if i=1 then ({i-1,i+1}:Finset ℕ) else if j=1 then {j-1} else ∅).card≤1
    rw [if_neg ne]
    split <;> simp
  have er_no : i+3≠p.length → ER.card≤1 := by
    intro ne
    change (if i+3=p.length then ({i,i+2}:Finset ℕ) else if j+1=p.length then {j} else ∅).card≤1
    rw [if_neg ne]
    split <;> simp
  have el_yes : i=1 → EL.card≤2 := by
    intro h
    change (if i=1 then ({i-1,i+1}:Finset ℕ) else if j=1 then {j-1} else ∅).card≤2
    rw [if_pos h]
    have c := card_insert_le (i-1) ({i+1}:Finset ℕ)
    rwa [card_singleton] at c
  have er_yes : i+3=p.length → ER.card≤2 := by
    intro h
    change (if i+3=p.length then ({i,i+2}:Finset ℕ) else if j+1=p.length then {j} else ∅).card≤2
    rw [if_pos h]
    have c := card_insert_le i ({i+2}:Finset ℕ)
    rwa [card_singleton] at c
  have ecard : (EL ∪ ER).card≤3 := by
    have lc := card_union_le EL ER
    by_cases hl : i=1
    · have hr : i+3≠p.length := by omega
      have l := el_yes hl
      have r := er_no hr
      omega
    · have l := el_no hl
      by_cases hr : i+3=p.length
      · have r := er_yes hr
        omega
      · have r := er_no hr
        omega
  have left_only (t : ℕ) (tl : t∈L) (tu : t∈U) : t∈EL := by
    have e : G.Adj a (p.getVert (t+1)) := (mem_filter.mp tl).2
    rcases mem_union.mp tu with k|k
    · simp only [I,mem_insert,mem_singleton] at k
      rcases k with rfl|rfl|rfl
      · exact (start_not_adj_pin_successor hp hx hi e).elim
      · exact (start_not_adj_pin_successor hp hx hj e).elim
      · exact (start_not_adj_pin_successor hp hy hjy e).elim
    · obtain ⟨r,hr,rt⟩ := mem_image.mp k
      change r-1=t at rt
      have rp := (pos r hr).1
      have shift : t+1=r := by omega
      rw [shift] at e
      simp only [I,mem_insert,mem_singleton] at hr
      rcases hr with rfl|rfl|rfl
      · have hlo := paired_left_chord hc hp hx hi hj size cap bl (Or.inl e)
        simp [EL,hlo,←rt]
      · have hlo := paired_left_chord hc hp hx hi hj size cap bl (Or.inr e)
        have ee : t=i+1 := by omega
        simp [EL,hlo,ee]
      · have hlo := singleton_left_chord hc hp hy hjy sz capy bly e
        have ne : i≠1 := by omega
        simp [EL,hlo,ne,←rt]
  have right_only (t : ℕ) (tr : t∈R) (tu : t∈U) : t∈ER := by
    have e : G.Adj b (p.getVert t) := (mem_filter.mp tr).2
    rcases mem_union.mp tu with k|k
    · simp only [I,mem_insert,mem_singleton] at k
      rcases k with rfl|rfl|rfl
      · have hr := paired_right_chord hc hp hx hi hj size cap bl (Or.inl e)
        simp [ER,hr]
      · have hr := paired_right_chord hc hp hx hi hj size cap bl (Or.inr e)
        simp [ER,hr]
      · have hr := singleton_right_chord hc hp hy hjy sz capy bly e
        have ne : i+3≠p.length := by omega
        simp [ER,hr,ne]
    · obtain ⟨r,hr,rt⟩ := mem_image.mp k
      change r-1=t at rt
      rw [←rt] at e
      simp only [I,mem_insert,mem_singleton] at hr
      rcases hr with rfl|rfl|rfl
      · exact (end_not_adj_pin_predecessor hp hx hi e).elim
      · exact (end_not_adj_pin_predecessor hp hx hj e).elim
      · exact (end_not_adj_pin_predecessor hp hy hjy e).elim
  let E := EL ∪ ER
  let M := U \ E
  have m3 : 3≤M.card := by
    have s : U⊆M∪E := by
      intro t ht
      by_cases h : t∈E
      · exact mem_union.mpr (Or.inr h)
      · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨ht,h⟩))
    have c := card_le_card s
    have c' := card_union_le M E
    have ec : E.card≤3 := ecard
    omega
  have dM : Disjoint (L ∪ R) M := by
    rw [disjoint_left]
    intro t tm tM
    obtain ⟨u,no⟩ := mem_sdiff.mp tM
    rcases mem_union.mp tm with l|r
    · exact no (mem_union.mpr (Or.inl (left_only t l u)))
    · exact no (mem_union.mpr (Or.inr (right_only t r u)))
  have total : (L∪R)∪M ⊆ range p.length :=
    union_subset marked (fun _ m => u_rng (mem_sdiff.mp m).1)
  have lower' := card_le_card total
  rw [card_union_of_disjoint dM,card_union_of_disjoint dis,ldeg,rdeg,card_range] at lower'
  omega

#print axioms path_order_ge_twelve
theorem path_order_ge_eleven (hc : G.Connected) (hp : IsLongest p)
    (a₄ : 4≤G.degree a) (b₄ : 4≤G.degree b)
    (hx : x∉p.support) {i : ℕ} (hi : i∈Pins p x) (hj : i+2∈Pins p x)
    (size : (Pins p x).card=2) (cap : (DistanceTwo G x).card≤4)
    (bl : 3≤(External G (OmittedStar p x)).card) :
    11≤p.length+1 := by
  classical
  let L := LeftMarks p
  let R := RightMarks p
  have ldeg : L.card=G.degree a := card_leftMarks hp
  have rdeg : R.card=G.degree b := card_rightMarks hp
  have marked : L ∪ R ⊆ range p.length := by
    intro t ht
    exact (mem_union.mp ht).elim (fun h => (mem_filter.mp h).1) (fun h => (mem_filter.mp h).1)
  have dis : Disjoint L R := by
    rw [disjoint_left]
    intro t ht hu
    obtain ⟨ttl,ea⟩ := mem_filter.mp ht
    exact not_adj_both_end_marks hp hx (p.getVert_mem_support i) (pin_data hi).2
      (mem_range.mp ttl) ea (mem_filter.mp hu).2
  have lower := card_le_card marked
  rw [card_union_of_disjoint dis,ldeg,rdeg,card_range] at lower
  let I := ({i,i+2}:Finset ℕ)
  have iPos := pin_pos hp hx hi
  have iLt := (pin_data hj).1
  have pos (t : ℕ) (h : t∈I) : 0<t ∧ t<p.length := by
    simp only [I,mem_insert,mem_singleton] at h
    rcases h with rfl|rfl <;> omega
  have ic : I.card=2 := by
    have ne : i≠i+2 := by omega
    change ({i,i+2}:Finset ℕ).card=2
    simp [ne]
  let J := I.image (·-1)
  have jc : J.card=I.card := by
    apply card_image_iff.mpr
    intro v hv w hw e
    have a := (pos v hv).1
    have b := (pos w hw).1
    change v-1=w-1 at e
    omega
  have ij : Disjoint I J := by
    rw [disjoint_left]
    intro t ht h
    obtain ⟨w,hw,e⟩ := mem_image.mp h
    have wpos := (pos w hw).1
    change w-1=t at e
    simp only [I,mem_insert,mem_singleton] at ht hw
    rcases ht with rfl|rfl <;> rcases hw with rfl|rfl <;> omega
  let U := I ∪ J
  have uc : U.card=4 := by
    rw [card_union_of_disjoint ij,jc,ic]
  have u_rng : U ⊆ range p.length := by
    intro t hu
    rcases mem_union.mp hu with e|e
    · exact mem_range.mpr (pos t e).2
    · obtain ⟨v,hv,rfl⟩ := mem_image.mp e
      have h := (pos v hv).2
      exact mem_range.mpr (by omega)
  let EL : Finset ℕ := if i=1 then {i-1,i+1} else ∅
  let ER : Finset ℕ := if i+3=p.length then {i,i+2} else ∅
  have ecard : (EL ∪ ER).card≤2 := by
    have lc := card_union_le EL ER
    by_cases h : i=1
    · have ne : i+3≠p.length := by omega
      have e : ER=∅ := by simp [ER,ne]
      rw [e,union_empty]
      have q := card_insert_le (i-1) ({i+1}:Finset ℕ)
      simpa only [EL,if_pos h,card_singleton] using q
    · have e : EL=∅ := by simp [EL,h]
      rw [e,empty_union]
      by_cases q : i+3=p.length
      · have c := card_insert_le i ({i+2}:Finset ℕ)
        simpa only [ER,if_pos q,card_singleton] using c
      · simp [ER,q]
  have left_only (t : ℕ) (tl : t∈L) (tu : t∈U) : t∈EL := by
    have e : G.Adj a (p.getVert (t+1)) := (mem_filter.mp tl).2
    rcases mem_union.mp tu with k|k
    · simp only [I,mem_insert,mem_singleton] at k
      rcases k with rfl|rfl
      · exact (start_not_adj_pin_successor hp hx hi e).elim
      · exact (start_not_adj_pin_successor hp hx hj e).elim
    · obtain ⟨r,hr,rt⟩ := mem_image.mp k
      change r-1=t at rt
      have rp := (pos r hr).1
      have shift : t+1=r := by omega
      rw [shift] at e
      simp only [I,mem_insert,mem_singleton] at hr
      rcases hr with rfl|rfl
      · have hlo := paired_left_chord hc hp hx hi hj size cap bl (Or.inl e)
        simp [EL,hlo,←rt]
      · have hlo := paired_left_chord hc hp hx hi hj size cap bl (Or.inr e)
        have ee : t=i+1 := by omega
        simp [EL,hlo,ee]
  have right_only (t : ℕ) (tr : t∈R) (tu : t∈U) : t∈ER := by
    have e : G.Adj b (p.getVert t) := (mem_filter.mp tr).2
    rcases mem_union.mp tu with k|k
    · simp only [I,mem_insert,mem_singleton] at k
      rcases k with rfl|rfl
      · have hr := paired_right_chord hc hp hx hi hj size cap bl (Or.inl e)
        simp [ER,hr]
      · have hr := paired_right_chord hc hp hx hi hj size cap bl (Or.inr e)
        simp [ER,hr]
    · obtain ⟨r,hr,rt⟩ := mem_image.mp k
      change r-1=t at rt
      rw [←rt] at e
      simp only [I,mem_insert,mem_singleton] at hr
      rcases hr with rfl|rfl
      · exact (end_not_adj_pin_predecessor hp hx hi e).elim
      · exact (end_not_adj_pin_predecessor hp hx hj e).elim
  let E := EL ∪ ER
  let M := U \ E
  have m3 : 2≤M.card := by
    have s : U⊆M∪E := by
      intro t ht
      by_cases h : t∈E
      · exact mem_union.mpr (Or.inr h)
      · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨ht,h⟩))
    have c := card_le_card s
    have c' := card_union_le M E
    have ec : E.card≤2 := ecard
    omega
  have dM : Disjoint (L ∪ R) M := by
    rw [disjoint_left]
    intro t tm tM
    obtain ⟨u,no⟩ := mem_sdiff.mp tM
    rcases mem_union.mp tm with l|r
    · exact no (mem_union.mpr (Or.inl (left_only t l u)))
    · exact no (mem_union.mpr (Or.inr (right_only t r u)))
  have total : (L∪R)∪M ⊆ range p.length :=
    union_subset marked (fun _ m => u_rng (mem_sdiff.mp m).1)
  have lower' := card_le_card total
  rw [card_union_of_disjoint dM,card_union_of_disjoint dis,ldeg,rdeg,card_range] at lower'
  omega


#print axioms path_order_ge_eleven

omit [Fintype V] [DecidableRel G.Adj] in
private theorem outside_edge {a b : V} (p : G.Walk a b) (hc : G.Connected)
    (hn : ∃ x, x ∉ p.support) :
    ∃ x ∉ p.support, ∃ y ∈ p.support, G.Adj x y := by
  obtain ⟨x,hx⟩ := hn
  obtain ⟨q⟩ := hc x a
  have go {x z : V} (q : G.Walk x z) (hx : x ∉ p.support) (hz : z ∈ p.support) :
      ∃ x ∉ p.support, ∃ y ∈ p.support, G.Adj x y := by
    induction q with
    | nil => exact (hx hz).elim
    | @cons u v w e q ih =>
      by_cases hv : v ∈ p.support
      · exact ⟨u,hx,v,hv,e⟩
      · exact ih hv hz
  exact go q hx p.start_mem_support

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

theorem rotate_to_two_high_endpoints_general (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k) (d : ℕ)
    (conn : ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V, u ≠ v → d ≤ G.degree u ∨ d ≤ G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) {x : V} (hx : x ∉ p.support) :
    ∃ (u v : V) (q : G.Walk u v), IsLongest q ∧
      (∀ z : V, z ∈ p.support ↔ z ∈ q.support) ∧
      d ≤ G.degree u ∧ d ≤ G.degree v := by
  classical
  have alow {a b : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x ∉ p.support) :
      k ≤ G.degree a := by
    have xne : x ≠ a := fun e => hx (e.symm ▸ p.start_mem_support)
    rw [← G.card_neighborFinset_eq_degree]
    apply boundary_card_of_connectivity k conn (x:=a) (a:=x) (A:={a})
    · exact mem_singleton_self _
    · exact fun e => xne (mem_singleton.mp e)
    · exact fun e => (no_endpoints hp hx).1 ((G.mem_neighborFinset _ _).mp e).symm
    · rw [disjoint_left]
      intro z za zb
      rw [mem_singleton] at za
      subst z
      exact G.loopless _ ((G.mem_neighborFinset _ _).mp zb)
    · intro y hy z _ e
      rw [mem_singleton] at hy
      subst y
      exact (G.mem_neighborFinset _ _).mpr e
  have step {a b : V} {p : G.Walk a b} (hp : IsLongest p) (hx : x ∉ p.support)
      (alo : ¬d ≤ G.degree a) (bhi : d ≤ G.degree b) :
      ∃ (u v : V) (q : G.Walk u v), IsLongest q ∧
        (∀ z : V, z ∈ p.support ↔ z ∈ q.support) ∧
        d ≤ G.degree u ∧ d ≤ G.degree v := by
    have lower := alow hp hx
    have mcard := card_leftMarks hp
    obtain ⟨j,hj,hne⟩ : ∃ j ∈ LeftMarks p, j ≠ 0 := by
      by_contra h
      have sub : LeftMarks p ⊆ {0} := by
        intro j hj
        apply mem_singleton.mpr
        by_contra hn
        exact h ⟨j,hj,hn⟩
      have cnt := card_le_card sub
      simp only [card_singleton] at cnt
      omega
    have data := mem_filter.mp hj
    have jlt := mem_range.mp data.1
    obtain ⟨q,hq,hs,_,_,_⟩ := rotate_start hp j jlt data.2
    have nej : a ≠ p.getVert j := by
      intro eq
      have e := p.getVert_zero.trans eq
      have bad := hp.1.getVert_injOn (show 0 ≤ p.length by omega) jlt.le e
      omega
    exact ⟨_,_,q,hq,hs,(degree a _ nej).resolve_left alo,bhi⟩
  have ab : a ≠ b := by
    intro he
    subst b
    have eq := (isPath_iff_eq_nil p).mp hp.1
    obtain ⟨u,_,v,_,e⟩ := outside_edge p hc ⟨x,hx⟩
    have pos := hp.2 u v e.toWalk (IsPath.of_adj e)
    simp [eq] at pos
  by_cases al : d ≤ G.degree a
  · by_cases bl : d ≤ G.degree b
    · exact ⟨a,b,p,hp,fun _ => Iff.rfl,al,bl⟩
    · obtain ⟨u,v,q,hq,hs,uh,vh⟩ := step (reverse_longest hp) (by simpa using hx) bl al
      exact ⟨u,v,q,hq,fun z => by simpa only [support_reverse,List.mem_reverse] using hs z,uh,vh⟩
  · exact step hp hx al ((degree a b ab).resolve_left al)

#print axioms rotate_to_two_high_endpoints_general
end Graffiti189LongestPath.OneSlack.MultiRotation
