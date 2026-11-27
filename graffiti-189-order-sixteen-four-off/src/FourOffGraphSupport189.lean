import SmallOrderFour189
import Batteries.Tactic.OpenPrivate

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {p : G.Walk a b} {x : V}
open private no_endpoints dist_two pin_data pin_of_neighbor_mem pin_pos mem_distanceTwo card_pinVertices cardinal_flankVertices LeftMarks RightMarks card_leftMarks card_rightMarks same_support_optimal reverse_long reverse_pin mark_length degree_off_bound two_flanks_full second_pin_no_start_of_high from SmallOrderFour189
private theorem two_pin_hole_dichotomy
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (xo : x∉p.support)
    {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p x) (gap : i+3≤j) :
    (4≤G.degree (p.getVert (j-1)) → j-1∉LeftMarks p∪RightMarks p) ∧
    (4≤G.degree (p.getVert (i+1)) → i∉LeftMarks p∪RightMarks p) ∧
    (j-1∉LeftMarks p∪RightMarks p ∨ i∉LeftMarks p∪RightMarks p) := by
  classical
  have cap := fun x => distanceTwo_le_of_even 4 x (even x)
  have few {a b : V} {q : G.Walk a b} (hq : EdgeOptimal q) {z : V} (zo : z∉q.support) :
      (Pins q z).card≤2 :=
    (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree hq zo).1
  have positive := pin_pos hp.1 xo hi
  have jl := (pin_data hj).1
  have left (hh : 4≤G.degree (p.getVert (j-1))) : j-1∉LeftMarks p∪RightMarks p := by
    have ban := second_pin_no_start_of_high hc even conn degree hp bh xo (few hp xo) hi hj gap hh
    intro hm
    rcases mem_union.mp hm with h|h
    · exact ban (by
        have g := (mem_filter.mp h).2
        rwa [show j-1+1=j by omega] at g)
    · exact end_not_adj_pin_predecessor hp.1 xo hj (mem_filter.mp h).2
  have right (hh : 4≤G.degree (p.getVert (i+1))) : i∉LeftMarks p∪RightMarks p := by
    have ep : EdgeOptimal p.reverse := same_support_optimal hp (reverse_long hp.1) (by intro z; simp)
    have ro : x∉p.reverse.support := by simpa using xo
    have rgh : 4≤G.degree (p.reverse.getVert (p.length-i-1)) := by
      rw [getVert_reverse,show p.length-(p.length-i-1)=i+1 by omega]
      exact hh
    have ban : ¬G.Adj b (p.getVert i) := by
      have e := second_pin_no_start_of_high hc even conn degree ep ah ro
        (few ep ro) (reverse_pin hp.1 xo hj) (reverse_pin hp.1 xo hi) (by omega) rgh
      rwa [getVert_reverse,show p.length-(p.length-i)=i by omega] at e
    intro hm
    exact (mem_union.mp hm).elim
      (fun h => start_not_adj_pin_successor hp.1 xo hi (mem_filter.mp h).2)
      (fun h => ban (mem_filter.mp h).2)
  have ne : p.getVert (j-1)≠p.getVert (i+1) := by
    intro e
    have h := hp.1.1.getVert_injOn (show j-1≤p.length by omega) (show i+1≤p.length by omega) e
    omega
  exact ⟨left,right,(degree _ _ ne).imp left right⟩

private theorem off_neighbors_complete_of_tight
    {a b x z : V} {p : G.Walk a b} (hp : IsLongest p)
    (xo : x∉p.support) (zo : z∉p.support) (ne : z≠x)
    (tight : (Pins p x).card + ((univ : Finset V)\p.support.toFinset).card-1 ≤ G.degree x) :
    G.Adj x z := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  have xO : x∈O := mem_sdiff.mpr ⟨mem_univ _,fun e => xo (List.mem_toFinset.mp e)⟩
  have zO : z∈O := mem_sdiff.mpr ⟨mem_univ _,fun e => zo (List.mem_toFinset.mp e)⟩
  have sub : G.neighborFinset x ⊆ PinVertices p x∪O.erase x := by
    intro y yn
    have xy := (mem_neighborFinset G x y).mp yn
    by_cases yp : y∈p.support
    · obtain ⟨i,hi,e⟩ := pin_of_neighbor_mem hp xo yp xy
      exact mem_union.mpr (.inl (mem_image.mpr ⟨i,hi,e⟩))
    · exact mem_union.mpr (.inr (mem_erase.mpr
        ⟨xy.ne.symm,mem_sdiff.mpr ⟨mem_univ _,fun e => yp (List.mem_toFinset.mp e)⟩⟩))
  have cb := card_union_le (PinVertices p x) (O.erase x)
  rw [card_erase_of_mem xO,card_pinVertices hp] at cb
  have op : 0<O.card := card_pos.mpr ⟨x,xO⟩
  change (Pins p x).card + O.card-1 ≤ G.degree x at tight
  have bd : (PinVertices p x∪O.erase x).card≤(G.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree]
    omega
  have eq := eq_of_subset_of_card_le sub bd
  exact (mem_neighborFinset G x z).mp (eq ▸ mem_union.mpr (.inr (mem_erase.mpr ⟨ne,zO⟩)))

private theorem pins_gap_at_four
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (xo : x∉p.support) {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p x) (ij : i<j) :
    i+3≤j := by
  obtain ⟨T,xT,Tne,Toff,Tclosed,Tjoined⟩ := exists_omitted_component xo
  let H : OmittedComponent p := ⟨T,Tne,Toff,Tclosed,Tjoined⟩
  exact component_pins_spaced_four hc even conn degree hp ah bh H xT xT hi hj ij

private theorem pin_two_contacts_end
    {a b x : V} {p : G.Walk a b}
    (hp : IsLongest p) (hc : G.Connected) (xo : x∉p.support)
    (F2 : (Pins p x).card≤2) (cap : (DistanceTwo G x).card≤4)
    {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p x) (gap : i+3≤j) :
    (∀ k∈Pins p x,G.Adj a (p.getVert k) → i=1) ∧
      (∀ k∈Pins p x,G.Adj b (p.getVert k) → j+1=p.length) := by
  obtain ⟨f,fi⟩ := two_flanks_full hp hc xo F2 cap hi hj gap
  have ip := pin_pos hp xo hi
  have jl := (pin_data hj).1
  have no := no_endpoints hp xo
  constructor
  · intro k hk e
    have nae : x≠a := fun e => xo (e.symm ▸ p.start_mem_support)
    have ax : a∈DistanceTwo G x := mem_distanceTwo.mpr
      (dist_two hc nae no.1 (pin_data hk).2 e.symm)
    rw [f] at ax
    obtain ⟨t,tf,ta⟩ := mem_image.mp ax
    rw [fi] at tf
    have cases : t=i-1 ∨ t=i+1 ∨ t=j-1 ∨ t=j+1 := by simpa using tf
    have tr : t≤p.length := by rcases cases with h|h|h|h <;> omega
    have t0 : t=0 := hp.1.getVert_injOn tr (Nat.zero_le _) (ta.trans p.getVert_zero.symm)
    rcases cases with h|h|h|h <;> omega
  · intro k hk e
    have nae : x≠b := fun e => xo (e.symm ▸ p.end_mem_support)
    have ax : b∈DistanceTwo G x := mem_distanceTwo.mpr
      (dist_two hc nae no.2 (pin_data hk).2 e.symm)
    rw [f] at ax
    obtain ⟨t,tf,ta⟩ := mem_image.mp ax
    rw [fi] at tf
    have cases : t=i-1 ∨ t=i+1 ∨ t=j-1 ∨ t=j+1 := by simpa using tf
    have tr : t≤p.length := by rcases cases with h|h|h|h <;> omega
    have te : t=p.length := hp.1.getVert_injOn tr (Nat.le_refl _) (ta.trans p.getVert_length.symm)
    rcases cases with h|h|h|h <;> omega

private theorem mark_length_ten_at_most_two_holes
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    (xo : x∉p.support) (yp : y∈p.support) (xy : G.Adj x y)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length≤10)
    {i j k : ℕ} (ir : i<p.length) (jr : j<p.length) (kr : k<p.length)
    (ih : i∉LeftMarks p∪RightMarks p) (jh : j∉LeftMarks p∪RightMarks p)
    (kh : k∉LeftMarks p∪RightMarks p) :
    i=j ∨ i=k ∨ j=k := by
  classical
  by_contra! ne
  let S : Finset ℕ := {i,j,k}
  have cs : S.card=3 := by
    simp [S, ne.1, ne.2.1, ne.2.2, card_insert_of_not_mem]
  have sub : S⊆range p.length := by
    intro z zm
    have hz : z=i ∨ z=j ∨ z=k := by simpa [S] using zm
    rcases hz with rfl|rfl|rfl <;> exact mem_range.mpr (by assumption)
  have dis : Disjoint (LeftMarks p∪RightMarks p) S := by
    apply disjoint_left.mpr
    intro z za zs
    have h : z=i ∨ z=j ∨ z=k := by simpa [S] using zs
    rcases h with rfl|rfl|rfl
    · exact ih za
    · exact jh za
    · exact kh za
  have bd := mark_length hp xo yp xy S sub dis
  omega

private theorem mark_holes_of_pin_and_missing_endpoint
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (xo : x∉p.support) {i : ℕ} (hi : i∈Pins p x) :
    (¬G.Adj a (p.getVert i) → i-1∉LeftMarks p∪RightMarks p) ∧
    (¬G.Adj b (p.getVert i) → i∉LeftMarks p∪RightMarks p) := by
  have ip := pin_pos hp xo hi
  constructor
  · intro no h
    rcases mem_union.mp h with lm|rm
    · apply no
      have h := (mem_filter.mp lm).2
      rwa [show i-1+1=i by omega] at h
    · exact end_not_adj_pin_predecessor hp xo hi (mem_filter.mp rm).2
  · intro no h
    exact (mem_union.mp h).elim
      (fun h => start_not_adj_pin_successor hp xo hi (mem_filter.mp h).2)
      (fun h => no (mem_filter.mp h).2)

private theorem length_ten_two_pin_shape
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=10)
    (xo : x∉p.support) {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p x) (ij : i<j) :
    (i=1 ∨ j=9) ∧
    (i≠1 → i-1∉LeftMarks p∪RightMarks p ∧ j-1∉LeftMarks p∪RightMarks p) ∧
    (j≠9 → i∉LeftMarks p∪RightMarks p ∧ j∉LeftMarks p∪RightMarks p) := by
  have cap := fun x => distanceTwo_le_of_even 4 x (even x)
  have f := (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree hp xo).1
  have gap := pins_gap_at_four hc even conn degree hp ah bh xo hi hj ij
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  have ip := pin_pos hp.1 xo hi
  have en := pin_two_contacts_end hp.1 hc xo f (cap x) hi hj gap
  have left (no : i≠1) : i-1∉LeftMarks p∪RightMarks p ∧ j-1∉LeftMarks p∪RightMarks p :=
    ⟨(mark_holes_of_pin_and_missing_endpoint hp.1 xo hi).1 (fun h => no (en.1 i hi h)),
     (mark_holes_of_pin_and_missing_endpoint hp.1 xo hj).1 (fun h => no (en.1 j hj h))⟩
  have right (no : j≠9) : i∉LeftMarks p∪RightMarks p ∧ j∉LeftMarks p∪RightMarks p :=
    ⟨(mark_holes_of_pin_and_missing_endpoint hp.1 xo hi).2
       (fun h => no (by have e := en.2 i hi h; omega)),
     (mark_holes_of_pin_and_missing_endpoint hp.1 xo hj).2
       (fun h => no (by have e := en.2 j hj h; omega))⟩
  refine ⟨?_,left,right⟩
  by_contra! no
  have o := mark_length_ten_at_most_two_holes hp.1 xo (p.getVert_mem_support i) (pin_data hi).2
    ah bh len.le (show i-1<p.length by omega) il jl (left no.1).1 (right no.2).1 (right no.2).2
  omega

#print axioms length_ten_two_pin_shape

private theorem left_minimum_d2_with_two_ports
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    (xo : x∉p.support) (yo : y∉p.support)
    {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p y) (ij : i≠j)
    (ai : G.Adj a (p.getVert i)) (aj : G.Adj a (p.getVert j))
    (S : Finset V) (out : ∀ z∈S,z∉p.support)
    (touch : ∀ z∈S, ∃ k∈Pins p z,G.Adj a (p.getVert k)) :
    S.card≤2 := by
  classical
  have offd (z : V) (zs : z∈S) : z∈DistanceTwo G a := by
    have zo := out z zs
    obtain ⟨k,hk,ak⟩ := touch z zs
    exact mem_distanceTwo.mpr (dist_two hc (fun e => zo (e ▸ p.start_mem_support))
      (fun h => (no_endpoints hp zo).1 h.symm) ak (pin_data hk).2.symm)
  have successor {z : V} (zo : z∉p.support) {k : ℕ}
      (hk : k∈Pins p z) (ak : G.Adj a (p.getVert k)) :
      p.getVert (k+1)∈DistanceTwo G a := by
    have kk := (pin_data hk).1
    apply mem_distanceTwo.mpr
    exact dist_two hc (fun e => by
      have Q := hp.1.getVert_injOn (Nat.zero_le _) (show k+1≤p.length by omega) (p.getVert_zero.trans e)
      omega) (start_not_adj_pin_successor hp zo hk) ak (p.adj_getVert_succ kk)
  have sub : insert (p.getVert (i+1)) (insert (p.getVert (j+1)) S) ⊆ DistanceTwo G a := by
    intro z hz
    rcases mem_insert.mp hz with hh|hh
    · exact hh.symm ▸ successor xo hi ai
    rcases mem_insert.mp hh with hh|hh
    · exact hh.symm ▸ successor yo hj aj
    · exact offd z hh
  have not_S {k : ℕ} : p.getVert k∉S := fun h => out _ h (p.getVert_mem_support _)
  have extra : p.getVert (i+1)∉insert (p.getVert (j+1)) S := by
    intro h
    rcases mem_insert.mp h with h|h
    · have il := (pin_data hi).1
      have jl := (pin_data hj).1
      have ee := hp.1.getVert_injOn (show i+1≤p.length by omega) (show j+1≤p.length by omega) h
      omega
    · exact not_S h
  have cd := card_le_card sub
  rw [card_insert_of_not_mem extra,card_insert_of_not_mem (not_S (k:=j+1))] at cd
  have cap := distanceTwo_le_of_even 4 a (even a)
  omega

private theorem two_pin_flanks_path_only
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (xo : x∉p.support)
    {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p x) (ij : i<j) :
    (∀ z∈DistanceTwo G x,z∈p.support) ∧
      ∀ y∉p.support,G.Adj x y → Pins p y ⊆ ({i,j}:Finset ℕ) := by
  classical
  have cap := fun x => distanceTwo_le_of_even 4 x (even x)
  have f := (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree hp xo).1
  have gap := pins_gap_at_four hc even conn degree hp ah bh xo hi hj ij
  obtain ⟨eq,_⟩ := two_flanks_full hp.1 hc xo f (cap x) hi hj gap
  have on : ∀ z∈DistanceTwo G x,z∈p.support := by
    intro z zd
    rw [eq] at zd
    obtain ⟨k,_,rfl⟩ := mem_image.mp zd
    exact p.getVert_mem_support _
  have sub : ({i,j}:Finset ℕ)⊆Pins p x := by
    intro k km
    rcases mem_insert.mp km with rfl|ks
    · exact hi
    · simpa only [mem_singleton.mp ks] using hj
  have peq : Pins p x={i,j} :=
    (eq_of_subset_of_card_le sub (by simpa [card_insert_of_not_mem,ij.ne] using f)).symm
  refine ⟨on,?_⟩
  intro y yo xy k ky
  by_contra no
  have notpin : ¬G.Adj x (p.getVert k) := by
    intro e
    have pin : k∈Pins p x := by
      exact mem_filter.mpr ⟨mem_range.mpr (pin_data ky).1,e⟩
    exact no (peq ▸ pin)
  have d : p.getVert k∈DistanceTwo G x := mem_distanceTwo.mpr
    (dist_two hc (fun e => xo (e ▸ p.getVert_mem_support k)) notpin xy (pin_data ky).2)
  obtain ⟨_,idx⟩ := two_flanks_full hp.1 hc xo f (cap x) hi hj gap
  rw [eq] at d
  obtain ⟨l,lm,le⟩ := mem_image.mp d
  rw [idx] at lm
  have lc : l=i-1 ∨ l=i+1 ∨ l=j-1 ∨ l=j+1 := by simpa using lm
  have ib := (pin_data hi).1
  have jb := (pin_data hj).1
  have lb : l≤p.length := by rcases lc with h|h|h|h <;> omega
  have kl := hp.1.1.getVert_injOn lb (pin_data ky).1.le le
  subst l
  obtain ⟨T,xT,Tne,Toff,Tclosed,Tjoined⟩ := exists_omitted_component xo
  let H : OmittedComponent p := ⟨T,Tne,Toff,Tclosed,Tjoined⟩
  have xH : x ∈ H.vertices := xT
  exact False.elim (by
    have yH : y∈H.vertices := Classical.byContradiction (fun e => yo (H.closed x xH y e xy))
    have gap' {k t : ℕ} (hk : k∈Pins p x) (ht : t∈Pins p y) (kt : k<t) :=
      component_pins_spaced_four hc even conn degree hp ah bh H xH yH hk ht kt
    have gap'' {k t : ℕ} (hk : k∈Pins p y) (ht : t∈Pins p x) (kt : k<t) :=
      component_pins_spaced_four hc even conn degree hp ah bh H yH xH hk ht kt
    have ip := pin_pos hp.1 xo hi
    have jp := pin_pos hp.1 xo hj
    rcases lc with h|h|h|h
    · have := gap'' ky hi (by omega); omega
    · have := gap' hi ky (by omega); omega
    · have := gap'' ky hj (by omega); omega
    · have := gap' hj ky (by omega); omega)
#print axioms two_pin_flanks_path_only


private theorem two_pin_universal_in_omitted_component
    (hc : G.Connected)
    {a b x : V} {p : G.Walk a b} (H : OmittedComponent p) (hx : x∈H.vertices)
    (path_only : ∀ z∈DistanceTwo G x,z∈p.support) :
    ∀ y∈H.vertices,y≠x → G.Adj x y := by
  intro y hy ne
  obtain ⟨q,_,stay⟩ := H.joined x hx y hy
  have propagate {u v : V} (r : G.Walk u v) (inside : ∀ z∈r.support,z∈H.vertices) :
      (u=x ∨ G.Adj x u) → v=x ∨ G.Adj x v := by
    induction r with
    | nil => exact id
    | @cons u v w uv r ih =>
      intro before
      have stay' (z : V) (hz : z∈r.support) : z∈H.vertices := inside _ (by simp [hz])
      apply ih stay'
      rcases before with rfl|xu
      · exact .inr uv
      by_contra! n
      have d : v∈DistanceTwo G x := mem_distanceTwo.mpr (dist_two hc n.1.symm n.2 xu uv)
      exact H.off _ (stay' _ r.start_mem_support) (path_only _ d)
  exact (propagate q stay (.inl rfl)).resolve_left ne

private theorem omitted_degree_component_bound
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : OmittedComponent p) (hx : x∈H.vertices) :
    G.degree x ≤ (Pins p x).card+H.vertices.card-1 := by
  classical
  have nx : G.neighborFinset x ⊆ PinVertices p x ∪ H.vertices.erase x := by
    intro z zn
    have xz := (mem_neighborFinset G x z).mp zn
    by_cases zp : z∈p.support
    · obtain ⟨i,hi,e⟩ := pin_of_neighbor_mem hp (H.off _ hx) zp xz
      exact mem_union.mpr (.inl (mem_image.mpr ⟨i,hi,e⟩))
    · have zT : z∈H.vertices := Classical.byContradiction (fun n => zp (H.closed x hx z n xz))
      exact mem_union.mpr (.inr (mem_erase.mpr ⟨xz.ne.symm,zT⟩))
  have n := card_le_card nx
  have bound := card_union_le (PinVertices p x) (H.vertices.erase x)
  rw [card_erase_of_mem hx,card_pinVertices hp] at bound
  rw [card_neighborFinset_eq_degree] at n
  have hpos := card_pos.mpr H.nonempty
  omega

private theorem off_four_component_carries_all_high
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (off : ((univ : Finset V)\p.support.toFinset).card=4)
    (few : ∀ x∉p.support,(Pins p x).card≤2) :
    ∃ H : OmittedComponent p, 3≤H.vertices.card ∧
      (∀ z∉p.support,4≤G.degree z → z∈H.vertices) ∧
      3≤(H.vertices.filter (fun z => 4≤G.degree z)).card := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  have out {z : V} : z∈O ↔ z∉p.support := by simp [O]
  have oc : O.card=4 := off
  obtain ⟨x,hx,y,hy,xy⟩ := one_lt_card.mp (show 1<O.card by omega)
  obtain ⟨z,zo,zh⟩ : ∃ z,z∈O ∧ 4≤G.degree z := (degree x y xy).elim
    (fun h => ⟨x,hx,h⟩) (fun h => ⟨y,hy,h⟩)
  obtain ⟨T,zT,Tne,Toff,Tclosed,Tjoined⟩ := exists_omitted_component (out.mp zo)
  let H : OmittedComponent p := ⟨T,Tne,Toff,Tclosed,Tjoined⟩
  have large : 3≤H.vertices.card := by
    have d := omitted_degree_component_bound hp H zT
    have f := few z (out.mp zo)
    omega
  have sub : H.vertices⊆O := fun _ h => out.mpr (H.off _ h)
  have subc := card_sdiff_add_card_eq_card sub
  have all (w : V) (wo : w∉p.support) (wh : 4≤G.degree w) : w∈H.vertices := by
    by_contra no
    obtain ⟨U,wU,Une,Uoff,Uclosed,Ujoined⟩ := exists_omitted_component wo
    let J : OmittedComponent p := ⟨U,Une,Uoff,Uclosed,Ujoined⟩
    have large' : 3≤J.vertices.card := by
      have d := omitted_degree_component_bound hp J wU
      have f := few w wo
      omega
    have disj : J.vertices⊆O\H.vertices := by
      intro v vm
      refine mem_sdiff.mpr ⟨out.mpr (J.off _ vm),?_⟩
      intro vh
      obtain ⟨r,_,stay⟩ := J.joined v vm w wU
      have walk {i j : V} (q : G.Walk i j) (inJ : ∀ z∈q.support,z∈J.vertices) :
          i∈H.vertices → j∈H.vertices := by
        induction q with
        | nil => exact id
        | @cons i j k adj q ih =>
          intro iH
          have incl (v : V) (hv : v∈q.support) := inJ v (by simp [hv])
          apply ih incl
          by_contra jH
          exact J.off _ (incl _ q.start_mem_support) (H.closed i iH j jH adj)
      exact no (walk r stay vh)
    have cd := card_le_card disj
    omega
  refine ⟨H,large,all,?_⟩
  let A := O.filter (fun v => 4≤G.degree v)
  let B := O.filter (fun v => ¬4≤G.degree v)
  have bsmall : B.card≤1 := by
    by_contra! nob
    have gb : 1<B.card := by omega
    obtain ⟨u,hu,v,hv,ne⟩ := one_lt_card.mp gb
    exact (degree u v ne).elim (mem_filter.mp hu).2 (mem_filter.mp hv).2
  have cu : A.card+B.card=O.card := filter_card_add_filter_neg_card_eq_card (s:=O) (fun v => 4≤G.degree v)
  have ad : A⊆H.vertices.filter (fun z => 4≤G.degree z) := by
    intro v h
    have hv := mem_filter.mp h
    exact mem_filter.mpr ⟨all v (out.mp hv.1) hv.2,hv.2⟩
  have cd := card_le_card ad
  omega
#print axioms off_four_component_carries_all_high


private theorem right_minimum_d2_with_two_ports
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    (xo : x∉p.support) (yo : y∉p.support)
    {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p y) (ij : i≠j)
    (bi : G.Adj b (p.getVert i)) (bj : G.Adj b (p.getVert j))
    (S : Finset V) (out : ∀ z∈S,z∉p.support)
    (touch : ∀ z∈S, ∃ k∈Pins p z,G.Adj b (p.getVert k)) :
    S.card≤2 := by
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  have bc {k : ℕ} (kk : k≤p.length) :
      p.reverse.getVert (p.length-k)=p.getVert k := by
    rw [getVert_reverse,show p.length-(p.length-k)=k by omega]
  apply left_minimum_d2_with_two_ports hc even (p:=p.reverse) (reverse_long hp)
    (by simpa using xo) (by simpa using yo) (reverse_pin hp xo hi) (reverse_pin hp yo hj)
    (by omega) (by rwa [bc il.le]) (by rwa [bc jl.le]) S (by simpa only [support_reverse,List.mem_reverse] using out)
  intro z hz
  obtain ⟨k,km,ak⟩ := touch z hz
  exact ⟨p.length-k,reverse_pin hp (out _ hz) km,by rwa [bc (pin_data km).1.le]⟩



end Graffiti189LongestPath.TwoCut.SmallOrderFour
