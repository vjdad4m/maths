import FourOffGraphSupport189

namespace Graffiti189LongestPath.TwoCut.SmallOrderFour
open SimpleGraph SimpleGraph.Walk Finset
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
variable {V : Type*} {G : SimpleGraph V}
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {p : G.Walk a b} {x : V}
open private no_endpoints dist_two pin_data pin_of_neighbor_mem pin_pos mem_distanceTwo card_pinVertices cardinal_flankVertices LeftMarks RightMarks card_leftMarks card_rightMarks same_support_optimal reverse_long reverse_pin mark_length degree_off_bound two_flanks_full second_pin_no_start_of_high from SmallOrderFour189
open private two_pin_hole_dichotomy off_neighbors_complete_of_tight pins_gap_at_four pin_two_contacts_end mark_length_ten_at_most_two_holes mark_holes_of_pin_and_missing_endpoint length_ten_two_pin_shape left_minimum_d2_with_two_ports two_pin_flanks_path_only two_pin_universal_in_omitted_component omitted_degree_component_bound off_four_component_carries_all_high right_minimum_d2_with_two_ports from FourOffGraphSupport189

private theorem single_pin_endpoint_contact_when_two_foreign
    (hc : G.Connected)
    {a b x y z : V} {p : G.Walk a b} (hp : IsLongest p)
    (xo : x∉p.support) (yo : y∉p.support) (zo : z∉p.support) (xy : G.Adj x y) (xz : G.Adj x z)
    (cap : (DistanceTwo G x).card≤4)
    (few : (Pins p x).card≤1)
    {i j k : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p y) (hk : k∈Pins p z)
    (ij : i+3≤j ∨ j+3≤i) (ik : i+3≤k ∨ k+3≤i) (jk : j≠k)
    : (G.Adj a (p.getVert i) → i=1) ∧ (G.Adj b (p.getVert i) → i+1=p.length) := by
  classical
  have ip := pin_pos hp xo hi
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  have kl := (pin_data hk).1
  have y0 := pin_pos hp yo hj
  have z0 := pin_pos hp zo hk
  let S : Finset ℕ := {i-1,i+1,j,k}
  have rangeS {l : ℕ} (lm : l∈S) : l≤p.length := by
    have e : l=i-1 ∨ l=i+1 ∨ l=j ∨ l=k := by simpa [S] using lm
    rcases e with rfl|rfl|rfl|rfl <;> omega
  have gS : S.card=4 := by
    have n1 : i-1∉({i+1,j,k}:Finset ℕ) := by
      simp only [mem_insert,mem_singleton]
      omega
    have n2 : i+1∉({j,k}:Finset ℕ) := by
      simp only [mem_insert,mem_singleton]
      omega
    have n3 : j∉({k}:Finset ℕ) := by simpa using jk
    rw [show S={i-1,i+1,j,k} from rfl,card_insert_of_not_mem n1,
      card_insert_of_not_mem n2,card_insert_of_not_mem n3,card_singleton]
  have cardV : (S.image p.getVert).card=4 := by
    rw [card_image_iff.mpr (fun _ u _ v e => hp.1.getVert_injOn (rangeS u) (rangeS v) e),gS]
  have fminus : p.getVert (i-1)∈DistanceTwo G x :=
    (mem_sdiff.mp (flanks_outside_boundary hc hp xo (show p.getVert (i-1)∈FlankVertices p x from
      mem_image.mpr ⟨i-1,mem_union.mpr (.inl (mem_image.mpr ⟨i,hi,rfl⟩)),rfl⟩))).1
  have fplus : p.getVert (i+1)∈DistanceTwo G x :=
    (mem_sdiff.mp (flanks_outside_boundary hc hp xo (show p.getVert (i+1)∈FlankVertices p x from
      mem_image.mpr ⟨i+1,mem_union.mpr (.inr (mem_image.mpr ⟨i,hi,rfl⟩)),rfl⟩))).1
  have foreign {w : V} {l : ℕ} (lx : i≠l) (lw : l∈Pins p w) (xw : G.Adj x w) :
      p.getVert l∈DistanceTwo G x := by
    have not : ¬G.Adj x (p.getVert l) := by
      intro a
      have inx : l∈Pins p x := mem_filter.mpr ⟨mem_range.mpr (pin_data lw).1,a⟩
      have cnt := one_lt_card.mpr ⟨i,hi,l,inx,lx⟩
      omega
    exact mem_distanceTwo.mpr (dist_two hc (fun e => xo (e ▸ p.getVert_mem_support l))
      not xw (pin_data lw).2)
  have sub : S.image p.getVert⊆DistanceTwo G x := by
    intro v vm
    obtain ⟨l,lm,rfl⟩ := mem_image.mp vm
    have le : l=i-1 ∨ l=i+1 ∨ l=j ∨ l=k := by simpa [S] using lm
    rcases le with rfl|rfl|rfl|rfl
    · exact fminus
    · exact fplus
    · exact foreign (by omega) hj xy
    · exact foreign (by omega) hk xz
  have eq : S.image p.getVert=DistanceTwo G x := eq_of_subset_of_card_le sub (by omega)
  constructor
  · intro lah
    have da : a∈DistanceTwo G x := mem_distanceTwo.mpr (dist_two hc
      (fun e => xo (e.symm ▸ p.start_mem_support)) (no_endpoints hp xo).1
      (pin_data hi).2 lah.symm)
    rw [←eq] at da
    obtain ⟨l,lm,la⟩ := mem_image.mp da
    have le : l=0 := hp.1.getVert_injOn (rangeS lm) (Nat.zero_le _) (la.trans p.getVert_zero.symm)
    have ls : l=i-1 ∨ l=i+1 ∨ l=j ∨ l=k := by simpa [S] using lm
    omega
  · intro lbh
    have db : b∈DistanceTwo G x := mem_distanceTwo.mpr (dist_two hc
      (fun e => xo (e.symm ▸ p.end_mem_support)) (no_endpoints hp xo).2
      (pin_data hi).2 lbh.symm)
    rw [←eq] at db
    obtain ⟨r,rm,rb⟩ := mem_image.mp db
    have re : r=p.length := hp.1.getVert_injOn (rangeS rm) (show p.length≤p.length from le_rfl) (rb.trans p.getVert_length.symm)
    have rs : r=i-1 ∨ r=i+1 ∨ r=j ∨ r=k := by simpa [S] using rm
    omega


private theorem length_eleven_four_off_single_pin_shape
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=11)
    (off : ((univ : Finset V)\p.support.toFinset).card=4)
    (few : ∀ x∉p.support,(Pins p x).card≤1) :
    ∃ (x y : V) (i j : ℕ), x∉p.support ∧ y∉p.support ∧ i∈Pins p x ∧ j∈Pins p y ∧ i+3≤j ∧
      (∀ z∉p.support, Pins p z⊆({i,j}:Finset ℕ)) ∧
      (∀ z∉p.support,∀ w∉p.support,z≠w → G.Adj z w) ∧
      (¬G.Adj a (p.getVert i) ∨ ¬G.Adj a (p.getVert j)) ∧
      (¬G.Adj b (p.getVert i) ∨ ¬G.Adj b (p.getVert j)) := by
  classical
  have cap := fun z => distanceTwo_le_of_even 4 z (even z)
  obtain ⟨H,_,_,high_many⟩ := off_four_component_carries_all_high degree hp.1 off
    (fun z zo => (few z zo).trans (by decide))
  let Hact := H.vertices.filter (fun z => 4≤G.degree z)
  have a3 : 3≤Hact.card := high_many
  have aout (z : V) (zA : z∈Hact) : z∉p.support := H.off _ (mem_filter.mp zA).1
  have active (z : V) (zA : z∈Hact) : (Pins p z).Nonempty := by
    have d := degree_off_bound hp.1 (aout z zA)
    rw [off] at d
    exact card_pos.mp (by have hg := (mem_filter.mp zA).2; omega)
  have clique (z : V) (zo : z∉p.support) (w : V) (wo : w∉p.support) (ne : z≠w) :
      G.Adj z w := by
    rcases degree z w ne with d|d
    · apply off_neighbors_complete_of_tight hp.1 zo wo ne.symm
      rw [off]
      have f := few z zo
      omega
    · apply G.symm
      apply off_neighbors_complete_of_tight hp.1 wo zo ne
      rw [off]
      have f := few w wo
      omega
  have whole (z : V) (zo : z∉p.support) : z∈H.vertices := by
    by_contra no
    obtain ⟨w,wH⟩ := H.nonempty
    have ne : w≠z := fun h => no (h ▸ wH)
    exact zo (H.closed _ wH _ no (clique w (H.off _ wH) z zo ne))
  obtain ⟨u,up,v,vp,uv⟩ := one_lt_card.mp (show 1<(componentPins H).card by
    have c := componentPins_card hp.1 H 2 conn
    omega)
  obtain ⟨up,x,xH,xu⟩ := mem_filter.mp up
  obtain ⟨vp,y,yH,yv⟩ := mem_filter.mp vp
  have xo := H.off _ xH
  have yo := H.off _ yH
  obtain ⟨i,hi,iu⟩ := pin_of_neighbor_mem hp.1 xo (List.mem_toFinset.mp up) xu
  obtain ⟨j,hj,jv⟩ := pin_of_neighbor_mem hp.1 yo (List.mem_toFinset.mp vp) yv
  have ine : i≠j := fun e => uv (iu.symm.trans (e ▸ jv))
  obtain ⟨x,y,i,j,xo,yo,hi,hj,ij⟩ : ∃ (x y : V) (i j : ℕ), x∉p.support ∧
      y∉p.support ∧ i∈Pins p x ∧ j∈Pins p y ∧ i<j := by
    rcases lt_or_gt_of_ne ine with h|h
    · exact ⟨x,y,i,j,xo,yo,hi,hj,h⟩
    · exact ⟨y,x,j,i,yo,xo,hj,hi,h⟩
  have gap {u v : V} (uo : u∉p.support) (vo : v∉p.support)
      {k l : ℕ} (hk : k∈Pins p u) (hl : l∈Pins p v) (ne : k≠l) : k+3≤l ∨ l+3≤k := by
    rcases lt_or_gt_of_ne ne with h|h
    · exact .inl (component_pins_spaced_four hc even conn degree hp ah bh H (whole u uo) (whole v vo) hk hl h)
    · exact .inr (component_pins_spaced_four hc even conn degree hp ah bh H (whole v vo) (whole u uo) hl hk h)
  have port_distinct {u v : V} (uo : u∉p.support) {k l : ℕ}
      (hk : k∈Pins p u) (hl : l∈Pins p v) (ne : k≠l) : u≠v := by
    intro h
    subst v
    have ha := one_lt_card.mpr ⟨k,hk,l,hl,ne⟩
    exact (Nat.not_lt_of_ge (few u uo)) ha
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  have ip := pin_pos hp.1 xo hi
  have jp := pin_pos hp.1 yo hj
  have ijg : i+3≤j := (gap xo yo hi hj ij.ne).resolve_right (by omega)
  have contact {u v w : V} (uo : u∉p.support) (vo : v∉p.support) (wo : w∉p.support)
      {k l m : ℕ} (hk : k∈Pins p u) (hl : l∈Pins p v) (hm : m∈Pins p w)
      (kl : k≠l) (km : k≠m) (lm : l≠m) :=
    single_pin_endpoint_contact_when_two_foreign hc hp.1 uo vo wo
      (clique u uo v vo (port_distinct uo hk hl kl))
      (clique u uo w wo (port_distinct uo hk hm km)) (cap u) (few u uo)
      hk hl hm (gap uo vo hk hl kl) (gap uo wo hk hm km) lm
  have no_three {u v w : V} (uo : u∉p.support) (vo : v∉p.support) (wo : w∉p.support)
      {r s t : ℕ} (hr : r∈Pins p u) (hs : s∈Pins p v) (ht : t∈Pins p w)
      (rs : r<s) (st : s<t) : False := by
    have rt : r<t := rs.trans st
    have rs3 := (gap uo vo hr hs rs.ne).resolve_right (by omega)
    have st3 := (gap vo wo hs ht st.ne).resolve_right (by omega)
    have rp := pin_pos hp.1 uo hr
    have tl := (pin_data ht).1
    have rh := (mark_holes_of_pin_and_missing_endpoint hp.1 uo hr).2 (fun e => by
      have c := (contact uo vo wo hr hs ht rs.ne rt.ne st.ne).2 e
      omega)
    have sl := (mark_holes_of_pin_and_missing_endpoint hp.1 vo hs).1 (fun e => by
      have c := (contact vo uo wo hs hr ht rs.ne.symm st.ne rt.ne).1 e
      omega)
    have sh := (mark_holes_of_pin_and_missing_endpoint hp.1 vo hs).2 (fun e => by
      have c := (contact vo uo wo hs hr ht rs.ne.symm st.ne rt.ne).2 e
      omega)
    have th := (mark_holes_of_pin_and_missing_endpoint hp.1 wo ht).1 (fun e => by
      have c := (contact wo uo vo ht hr hs rt.ne.symm st.ne.symm rs.ne).1 e
      omega)
    let M : Finset ℕ := {r,s-1,s,t-1}
    have mc : M.card=4 := by
      have h1 : r∉({s-1,s,t-1}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
      have h2 : s-1∉({s,t-1}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
      have h3 : s∉({t-1}:Finset ℕ) := by simp only [mem_singleton]; omega
      rw [show M={r,s-1,s,t-1} from rfl,card_insert_of_not_mem h1,card_insert_of_not_mem h2,
        card_insert_of_not_mem h3,card_singleton]
    have sub : M⊆range p.length := by
      intro k h
      have e : k=r ∨ k=s-1 ∨ k=s ∨ k=t-1 := by simpa [M] using h
      rcases e with rfl|rfl|rfl|rfl <;> exact mem_range.mpr (by omega)
    have dis : Disjoint (LeftMarks p∪RightMarks p) M := by
      apply disjoint_left.mpr
      intro k kM h
      have e : k=r ∨ k=s-1 ∨ k=s ∨ k=t-1 := by simpa [M] using h
      rcases e with rfl|rfl|rfl|rfl
      · exact rh kM
      · exact sl kM
      · exact sh kM
      · exact th kM
    have m := mark_length hp.1 uo (p.getVert_mem_support r) (pin_data hr).2 M sub dis
    omega
  have all (z : V) (zo : z∉p.support) : Pins p z⊆({i,j}:Finset ℕ) := by
    intro k hk
    by_contra no
    have bans : k≠i ∧ k≠j := by simpa using no
    by_cases a : k<i
    · exact no_three zo xo yo hk hi hj a ij
    by_cases b : k<j
    · exact no_three xo zo yo hi hk hj (by omega) b
    · exact no_three xo yo zo hi hj hk ij (by omega)
  have le : ¬G.Adj a (p.getVert i) ∨ ¬G.Adj a (p.getVert j) := by
    by_contra! h
    have c := left_minimum_d2_with_two_ports hc even hp.1 xo yo hi hj ij.ne h.1 h.2 Hact aout (by
      intro z zA
      obtain ⟨k,km⟩ := active z zA
      have ks := all z (aout z zA) km
      rcases mem_insert.mp ks with rfl|ks
      · exact ⟨_,km,h.1⟩
      · obtain rfl := mem_singleton.mp ks
        exact ⟨_,km,h.2⟩)
    omega
  have re : ¬G.Adj b (p.getVert i) ∨ ¬G.Adj b (p.getVert j) := by
    by_contra! h
    have c := right_minimum_d2_with_two_ports hc even hp.1 xo yo hi hj ij.ne h.1 h.2 Hact aout (by
      intro z zA
      obtain ⟨k,km⟩ := active z zA
      have ks := all z (aout z zA) km
      rcases mem_insert.mp ks with rfl|ks
      · exact ⟨_,km,h.1⟩
      · obtain rfl := mem_singleton.mp ks
        exact ⟨_,km,h.2⟩)
    omega
  exact ⟨x,y,i,j,xo,yo,hi,hj,ijg,all,clique,le,re⟩
#print axioms length_eleven_four_off_single_pin_shape
private theorem endpoint_block_from_two_path_distances_at_pin_one
    (hc : G.Connected)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : 6≤p.length)
    (xo : x∉p.support) (h1 : 1∈Pins p x)
    (small : ((DistanceTwo G a).filter (· ∈ p.support)).card≤2) :
    ∃ t : ℕ, 5≤t ∧ t+1<p.length ∧
      (∀ k : ℕ,3≤k → k≤t → G.Adj a (p.getVert k)) ∧
      (∀ k : ℕ,k≤p.length → G.Adj a (p.getVert k) → k=1 ∨ (3≤k ∧ k≤t)) ∧
      ¬G.Adj a b ∧ b∉DistanceTwo G a := by
  classical
  let D := (DistanceTwo G a).filter (· ∈ p.support)
  change D.card≤2 at small
  have vr {i j : ℕ} (ir : i≤p.length) (jr : j≤p.length) (ne : i≠j) :
      p.getVert i≠p.getVert j := fun e => ne (hp.1.getVert_injOn ir jr e)
  have na : ¬G.Adj a b := by
    intro e
    let k := p.length-1
    have kl : k<p.length := by omega
    have eq : k+1=p.length := by omega
    have ea : G.Adj a (p.getVert (k+1)) := by rw [eq,p.getVert_length]; exact e
    have eb := (p.adj_getVert_succ kl).symm
    rw [eq,p.getVert_length] at eb
    exact not_adj_both_end_marks hp xo (p.getVert_mem_support 1) (pin_data h1).2 kl ea eb
  have aA : ¬G.Adj a (p.getVert 0) := by simp
  have first : G.Adj a (p.getVert 1) := by simpa using p.adj_getVert_succ (i:=0) (by omega)
  have nTwo : ¬G.Adj a (p.getVert 2) := start_not_adj_pin_successor hp xo h1
  have mkD {i : ℕ} (ip : 0<i) (ir : i≤p.length)
      (no : ¬G.Adj a (p.getVert i)) {j : ℕ} (adj : G.Adj a (p.getVert j))
      (edge : G.Adj (p.getVert j) (p.getVert i)) : p.getVert i∈D :=
    mem_filter.mpr ⟨mem_distanceTwo.mpr (dist_two hc (fun e => vr (i:=0) (Nat.zero_le _) ir
      (by omega) (p.getVert_zero.trans e)) no adj edge),p.getVert_mem_support i⟩
  have d2 : p.getVert 2∈D := mkD (by omega) (by omega) nTwo first
    (p.adj_getVert_succ (i:=1) (by omega))
  let A := (range (p.length+1)).filter (fun i => G.Adj a (p.getVert i))
  have memA {i : ℕ} : i∈A ↔ i<p.length+1 ∧ G.Adj a (p.getVert i) := by simp [A]
  have sa : A.Nonempty := ⟨1,memA.mpr ⟨by omega,first⟩⟩
  let t := A.max' sa
  have tm : t∈A := max'_mem A sa
  have tb : t+1≤p.length := by
    have b := memA.mp tm
    by_contra! big
    have eq : t=p.length := by omega
    have q := b.2
    rw [eq,p.getVert_length] at q
    exact na q
  have tmax {i : ℕ} (h : i∈A) : i≤t := le_max' A i h
  have injectA : (A.image p.getVert).card=A.card := by
    apply card_image_iff.mpr
    intro u hu v hv e
    have ur : u<p.length+1 := (memA.mp hu).1
    have vv : v<p.length+1 := (memA.mp hv).1
    exact hp.1.getVert_injOn (show u≤p.length by omega) (show v≤p.length by omega) e
  have allAdj : G.neighborFinset a ⊆ A.image p.getVert := by
    intro z zm
    have az := (mem_neighborFinset G a z).mp zm
    have zp : z∈p.support := Classical.byContradiction (fun e => (no_endpoints hp e).1 az.symm)
    obtain ⟨k,ke,kp⟩ := mem_support_iff_exists_getVert.mp zp
    exact mem_image.mpr ⟨k,memA.mpr ⟨by omega,ke.symm ▸ az⟩,ke⟩
  have amin : 4≤A.card := by
    have q := card_le_card allAdj
    rw [injectA,card_neighborFinset_eq_degree] at q
    omega
  have tge : 5≤t := by
    by_contra! low
    have aa : A⊆({1,3,4}:Finset ℕ) := by
      intro v vm
      have vl : v≤t := tmax vm
      have vlt : v<5 := lt_of_le_of_lt vl low
      have va := (memA.mp vm).2
      by_cases n0 : v=0
      · exact False.elim (aA (n0 ▸ va))
      by_cases n2 : v=2
      · exact False.elim (nTwo (n2 ▸ va))
      have vc : v=1 ∨ v=3 ∨ v=4 := by omega
      simpa using vc
    have c := card_le_card aa
    have c3 : ( {1,3,4}:Finset ℕ).card=3 := by decide
    omega
  have dt : p.getVert (t+1)∈D := by
    have no : ¬G.Adj a (p.getVert (t+1)) := fun h => by
      have := tmax (memA.mpr ⟨by omega,h⟩)
      omega
    exact mkD (by omega) (by omega) no (memA.mp tm).2 (p.adj_getVert_succ (i:=t) (by omega))
  have deq : D=({p.getVert 2,p.getVert (t+1)}:Finset V) := by
    symm
    apply eq_of_subset_of_card_le
    · intro z hz
      exact (mem_insert.mp hz).elim (fun e => e.symm ▸ d2) (fun e => (mem_singleton.mp e).symm ▸ dt)
    · rw [card_insert_of_not_mem (by
          simpa using vr (i:=2) (j:=t+1) (by omega) (by omega) (by omega)),card_singleton]
      omega
  have back (k : ℕ) (r : 3≤k) (kt : k≤t) : G.Adj a (p.getVert k) := by
    let P := fun n : ℕ => 3≤t-n → G.Adj a (p.getVert (t-n))
    have yes : ∀ n,P n := by
      intro n
      induction n with
      | zero => intro _; simpa using (memA.mp tm).2
      | succ n ih =>
          intro ge
          have r' : 3≤t-n := by
            change 3≤t-(n+1) at ge
            omega
          have old := ih r'
          by_cases yes : G.Adj a (p.getVert (t-(n+1)))
          · exact yes
          exfalso
          have e : t-n = t-(n+1)+1 := by
            change 3≤t-(n+1) at ge
            omega
          have zz : p.getVert (t-(n+1))∈D :=
            mkD (by change 3≤t-(n+1) at ge; omega) (by omega) yes old
              (by rw [e]; exact (p.adj_getVert_succ (i:=t-(n+1)) (by omega)).symm)
          rw [deq] at zz
          rcases mem_insert.mp zz with o|o
          · exact vr (i:=t-(n+1)) (j:=2) (by omega) (by omega)
              (by change 3≤t-(n+1) at ge; omega) o
          · exact vr (i:=t-(n+1)) (j:=t+1) (by omega) (by omega)
              (by omega) (mem_singleton.mp o)
    have k' : t-(t-k)=k := by omega
    have eq := yes (t-k)
    simp only [P,k'] at eq
    exact eq r
  have ee : t+1≠p.length := by
    intro eq
    have dis : Disjoint (LeftMarks p∪RightMarks p) (∅:Finset ℕ) := by simp
    have bd := mark_length hp xo (p.getVert_mem_support 1) (pin_data h1).2 ∅ (empty_subset _) dis
    let T := insert 1 (Icc 3 t)
    have ss : T⊆A := by
      intro v vm
      rcases mem_insert.mp vm with rfl|vm
      · exact memA.mpr ⟨by omega,first⟩
      · obtain ⟨vl,vu⟩ := mem_Icc.mp vm
        exact memA.mpr ⟨by omega,back v vl vu⟩
    have sz : T.card=t-1 := by
      have mn : 1∉Icc 3 t := fun h => by have p := (mem_Icc.mp h).1; omega
      change (insert 1 (Icc 3 t)).card=t-1
      rw [card_insert_of_not_mem mn,Nat.card_Icc]
      omega
    have size := card_le_card ss
    have sub : A.image p.getVert⊆G.neighborFinset a := by
      intro v vm
      obtain ⟨i,im,rfl⟩ := mem_image.mp vm
      exact (mem_neighborFinset G a _).mpr (memA.mp im).2
    have ag := card_le_card sub
    rw [injectA,card_neighborFinset_eq_degree] at ag
    simp at bd
    omega
  have nbD : b∉D := by
    intro h
    rw [deq] at h
    rcases mem_insert.mp h with hh|hh
    · exact vr (i:=p.length) (j:=2) le_rfl (by omega) (by omega) (p.getVert_length.trans hh)
    · exact vr (i:=p.length) (j:=t+1) le_rfl (by omega) (by omega)
        (p.getVert_length.trans (mem_singleton.mp hh))

  refine ⟨t,tge,by omega,back,?_,na,?_⟩
  · intro k kr h
    have kA : k∈A := memA.mpr ⟨by omega,h⟩
    have kl : k≤t := tmax kA
    have n0 : k≠0 := fun e => aA (e ▸ h)
    have n2 : k≠2 := fun e => nTwo (e ▸ h)
    omega
  · intro d
    exact nbD (mem_filter.mpr ⟨d,p.end_mem_support⟩)
#print axioms endpoint_block_from_two_path_distances_at_pin_one

private theorem left_boundary_porters_at_most_two
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : 6≤p.length) (xo : x∉p.support) (xi : 1∈Pins p x)
    (S : Finset V) (off : ∀ z∈S,z∉p.support) (pins : ∀ z∈S,1∈Pins p z) :
    S.card≤2 := by
  classical
  by_contra n
  let D := DistanceTwo G a
  let U := D.filter (· ∉ p.support)
  let T := D.filter (· ∈ p.support)
  have a1 : G.Adj a (p.getVert 1) := by simpa using p.adj_getVert_succ (i:=0) (by omega)
  have sub : S⊆U := by
    intro z zs
    have zo := off _ zs
    exact mem_filter.mpr ⟨mem_distanceTwo.mpr (dist_two hc
      (fun e => zo (e ▸ p.start_mem_support)) (fun e => (no_endpoints hp zo).1 e.symm)
      a1 (pin_data (pins z zs)).2.symm),zo⟩
  have cS := card_le_card sub
  have c := filter_card_add_filter_neg_card_eq_card (s:=D) (· ∈ p.support)
  change T.card+U.card=D.card at c
  have da : D.card≤4 := distanceTwo_le_of_even 4 a (even a)
  have small : T.card≤1 := by omega
  obtain ⟨t,t5,tb,back,all,_,_⟩ := endpoint_block_from_two_path_distances_at_pin_one hc hp ah bh len xo xi
    (small.trans (by decide))
  have dst {k : ℕ} (kp : 0<k) (kl : k≤p.length) (n : ¬G.Adj a (p.getVert k))
      {q : ℕ} (aq : G.Adj a (p.getVert q)) (qq : G.Adj (p.getVert q) (p.getVert k)) :
      p.getVert k∈T := by
    refine mem_filter.mpr ⟨mem_distanceTwo.mpr (dist_two hc ?_ n aq qq),p.getVert_mem_support _⟩
    intro eq
    have g := hp.1.getVert_injOn (show 0≤p.length by omega) kl (p.getVert_zero.trans eq)
    omega
  have v2 := dst (k:=2) (by decide) (by omega) (start_not_adj_pin_successor hp xo xi)
    a1 (p.adj_getVert_succ (i:=1) (by omega))
  have nxt : ¬G.Adj a (p.getVert (t+1)) := fun H => by
    have e := all (t+1) (by omega) H
    omega
  have vt := dst (k:=t+1) (by omega) (by omega) nxt (back t (by omega) le_rfl)
    (p.adj_getVert_succ (i:=t) (by omega))
  have vne : p.getVert 2≠p.getVert (t+1) := fun e => by
    have g := hp.1.getVert_injOn (show 2≤p.length by omega) (show t+1≤p.length by omega) e
    omega
  have big := one_lt_card.mpr ⟨p.getVert 2,v2,p.getVert (t+1),vt,vne⟩
  omega

private theorem right_boundary_porters_at_most_two
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (ah : 4≤G.degree a) (bh : 4≤G.degree b)
    (len : 6≤p.length) (xo : x∉p.support) {i : ℕ} (xi : i∈Pins p x) (il : i+1=p.length)
    (S : Finset V) (off : ∀ z∈S,z∉p.support) (pins : ∀ z∈S,i∈Pins p z) :
    S.card≤2 := by
  have left : 1∈Pins p.reverse x := by
    simpa only [show p.length-i=1 by omega] using reverse_pin hp xo xi
  apply left_boundary_porters_at_most_two hc even (reverse_long hp) bh ah (by simpa using len)
    (by simpa using xo) left S (by simpa only [support_reverse,List.mem_reverse] using off)
  intro z zs
  simpa only [show p.length-i=1 by omega] using reverse_pin hp (off z zs) (pins z zs)

#print axioms left_boundary_porters_at_most_two

private theorem length_eleven_two_pin_hits_boundary
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=11)
    (xo : x∉p.support) {i j : ℕ} (hi : i∈Pins p x) (hj : j∈Pins p x) (gap : i+3≤j) :
    (i=1 ∨ j=10) ∧
    (j≠10 → i∉LeftMarks p∪RightMarks p ∧ j∉LeftMarks p∪RightMarks p) := by
  classical
  have cap := fun v => distanceTwo_le_of_even 4 v (even v)
  have f := (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree hp xo).1
  have en := pin_two_contacts_end hp.1 hc xo f (cap x) hi hj gap
  have il := (pin_data hi).1
  have jl := (pin_data hj).1
  have ip := pin_pos hp.1 xo hi
  have left (no : i≠1) : i-1∉LeftMarks p∪RightMarks p ∧ j-1∉LeftMarks p∪RightMarks p :=
    ⟨(mark_holes_of_pin_and_missing_endpoint hp.1 xo hi).1 (fun h => no (en.1 i hi h)),
     (mark_holes_of_pin_and_missing_endpoint hp.1 xo hj).1 (fun h => no (en.1 j hj h))⟩
  have right (no : j≠10) : i∉LeftMarks p∪RightMarks p ∧ j∉LeftMarks p∪RightMarks p :=
    ⟨(mark_holes_of_pin_and_missing_endpoint hp.1 xo hi).2
       (fun h => no (by have e := en.2 i hi h; omega)),
     (mark_holes_of_pin_and_missing_endpoint hp.1 xo hj).2
       (fun h => no (by have e := en.2 j hj h; omega))⟩
  refine ⟨?_,right⟩
  by_contra! no
  let S : Finset ℕ := {i-1,i,j-1,j}
  have sub : S⊆range p.length := by
    intro k km
    have h : k=i-1 ∨ k=i ∨ k=j-1 ∨ k=j := by simpa [S] using km
    rcases h with h|h|h|h <;> exact mem_range.mpr (by omega)
  have size : S.card=4 := by
    have nh1 : i-1∉({i,j-1,j}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have nh2 : i∉({j-1,j}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have nh3 : j-1∉({j}:Finset ℕ) := by simp only [mem_singleton]; omega
    rw [show S={i-1,i,j-1,j} from rfl,card_insert_of_not_mem nh1,card_insert_of_not_mem nh2,
      card_insert_of_not_mem nh3,card_singleton]
  have nd : Disjoint (LeftMarks p∪RightMarks p) S := by
    apply disjoint_left.mpr
    intro k km ks
    have h : k=i-1 ∨ k=i ∨ k=j-1 ∨ k=j := by simpa [S] using ks
    rcases h with rfl|rfl|rfl|rfl
    · exact (left no.1).1 km
    · exact (right no.2).1 km
    · exact (left no.1).2 km
    · exact (right no.2).2 km
  have bd := mark_length hp.1 xo (p.getVert_mem_support i) (pin_data hi).2 S sub nd
  omega
#print axioms length_eleven_two_pin_hits_boundary

private theorem two_pins_choose_ordered
    {a b x : V} {p : G.Walk a b} (h : 2≤(Pins p x).card) :
    ∃ i j : ℕ, i∈Pins p x ∧ j∈Pins p x ∧ i<j := by
  obtain ⟨i,hi,j,hj,ne⟩ := one_lt_card.mp (show 1<(Pins p x).card by omega)
  exact (lt_or_gt_of_ne ne).elim (fun e => ⟨i,j,hi,hj,e⟩) (fun e => ⟨j,i,hj,hi,e⟩)

private theorem length_eleven_four_off_two_pin_shape
    (hc : G.Connected) (even : ∀ v,(EvenFrom G v).card≤5)
    (conn : ∀ S : Finset V,S.card<2 → (G.induce ((↑S : Set V)ᶜ)).Connected)
    (degree : ∀ u v : V,u≠v → 4≤G.degree u ∨ 4≤G.degree v)
    {a b x : V} {p : G.Walk a b} (hp : EdgeOptimal p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=11)
    (off : ((univ : Finset V)\p.support.toFinset).card=4)
    (xo : x∉p.support) (x2 : 2≤(Pins p x).card) :
    ∃ (y : V) (i j : ℕ), y∉p.support ∧ i∈Pins p y ∧ j∈Pins p y ∧ i+3≤j ∧
      (i=1 ∨ j=10) ∧ (∀ z∉p.support,Pins p z⊆({i,j}:Finset ℕ)) ∧
      (∀ z∉p.support,∀ w∉p.support,z≠w → G.Adj z w) ∧
      i∉LeftMarks p∪RightMarks p ∧ j-1∉LeftMarks p∪RightMarks p ∧
      (i≠1 → i-1∉LeftMarks p∪RightMarks p) ∧ (j≠10 → j∉LeftMarks p∪RightMarks p) := by
  classical
  have cap := fun x => distanceTwo_le_of_even 4 x (even x)
  have few (z : V) (zo : z∉p.support) : (Pins p z).card≤2 :=
    (at_most_two_pins_one_slack hc 2 (by decide) cap conn degree hp zo).1
  let O := (univ : Finset V)\p.support.toFinset
  have out {z : V} : z∈O ↔ z∉p.support := by simp [O]
  have oc : O.card=4 := off
  obtain ⟨H,Hlarge,high_H,high_many⟩ := off_four_component_carries_all_high degree hp.1 off few
  let A := H.vertices.filter (fun z => 4≤G.degree z)
  have a3 : 3≤A.card := high_many
  have sub : H.vertices⊆O := fun _ h => out.mpr (H.off _ h)
  have split := card_sdiff_add_card_eq_card sub
  have hole_of_outside {w : V} (wo : w∉p.support) (wH : w∉H.vertices) :
      H.vertices.card=3 ∧ O\H.vertices={w} := by
    have yes : w∈O\H.vertices := mem_sdiff.mpr ⟨out.mpr wo,wH⟩
    have pos := card_pos.mpr ⟨w,yes⟩
    refine ⟨by omega,?_⟩
    symm
    exact eq_of_subset_of_card_le (singleton_subset_iff.mpr yes) (by rw [card_singleton]; omega)
  have y2 : ∃ y∈H.vertices,2≤(Pins p y).card := by
    by_cases hx : x∈H.vertices
    · exact ⟨x,hx,x2⟩
    obtain ⟨large,_⟩ := hole_of_outside xo hx
    obtain ⟨v,vm⟩ := card_pos.mp (show 0<A.card by omega)
    obtain ⟨vH,vhigh⟩ := mem_filter.mp vm
    have d := omitted_degree_component_bound hp.1 H vH
    exact ⟨v,vH,by omega⟩
  obtain ⟨y,yH,y2⟩ := y2
  have yo := H.off _ yH
  obtain ⟨i,j,hi,hj,ij⟩ := two_pins_choose_ordered y2
  obtain ⟨inside,subpin⟩ := two_pin_flanks_path_only hc even conn degree hp ah bh yo hi hj ij
  have sub_H (z : V) (zH : z∈H.vertices) : Pins p z⊆({i,j}:Finset ℕ) := by
    by_cases e : z=y
    · subst z
      have ss : ({i,j} : Finset ℕ)⊆Pins p y := by
        intro k km
        rcases mem_insert.mp km with rfl|kk
        · exact hi
        · exact (mem_singleton.mp kk).symm ▸ hj
      have eq : ({i,j}:Finset ℕ)=Pins p y :=
        eq_of_subset_of_card_le ss (by simpa [card_insert_of_not_mem,ij.ne] using few y yo)
      rw [eq]
    · exact subpin z (H.off _ zH) (two_pin_universal_in_omitted_component hc H yH inside z zH e)
  have active (z : V) (zA : z∈A) : (Pins p z).Nonempty := by
    obtain ⟨zH,zh⟩ := mem_filter.mp zA
    have d := degree_off_bound hp.1 (H.off _ zH)
    rw [off] at d
    exact card_pos.mp (by omega)
  have aout (z : V) (zA : z∈A) : z∉p.support := H.off _ (mem_filter.mp zA).1

  have gap := pins_gap_at_four hc even conn degree hp ah bh yo hi hj ij
  have border : i=1 ∨ j=10 :=
    (length_eleven_two_pin_hits_boundary hc even conn degree hp ah bh len yo hi hj gap).1
  have H4 : H.vertices.card=4 := by
    by_contra n
    have c := card_le_card sub
    have eq : H.vertices.card=3 := by omega
    have twin (z : V) (zA : z∈A) : i∈Pins p z ∧ j∈Pins p z := by
      obtain ⟨zH,zhi⟩ := mem_filter.mp zA
      have d := omitted_degree_component_bound hp.1 H zH
      have f := sub_H z zH
      have cc : ({i,j}:Finset ℕ).card=2 := by simp [card_insert_of_not_mem,ij.ne]
      have rp : Pins p z={i,j} := eq_of_subset_of_card_le f (by omega)
      simp [rp]
    rcases border with i1|j10
    · subst i
      have sm := left_boundary_porters_at_most_two hc even hp.1 ah bh (by omega) yo hi A aout
        (fun z zm => (twin z zm).1)
      omega
    · have jl : j+1=p.length := by omega
      have sm := right_boundary_porters_at_most_two hc even hp.1 ah bh (by omega) yo hj jl A aout
        (fun z zm => (twin z zm).2)
      omega
  have fullH : H.vertices=O := eq_of_subset_of_card_le sub (by omega)
  have whole (z : V) (zo : z∉p.support) : z∈H.vertices := fullH.symm ▸ out.mpr zo
  have complete (z : V) (zo : z∉p.support) (zh : 4≤G.degree z)
      (w : V) (wo : w∉p.support) (ne : z≠w) : G.Adj z w := by
    by_cases small : (Pins p z).card≤1
    · apply off_neighbors_complete_of_tight hp.1 zo wo ne.symm
      rw [off]
      omega
    have two : 2≤(Pins p z).card := by omega
    obtain ⟨i',j',hi',hj',ij'⟩ := two_pins_choose_ordered two
    have stay := (two_pin_flanks_path_only hc even conn degree hp ah bh zo hi' hj' ij').1
    exact two_pin_universal_in_omitted_component hc H (whole _ zo) stay w (whole _ wo) ne.symm
  have C (z : V) (zo : z∉p.support) (w : V) (wo : w∉p.support) (ne : z≠w) :
      G.Adj z w := (degree z w ne).elim (fun d => complete z zo d w wo ne)
        (fun d => (complete w wo d z zo ne.symm).symm)
  have noL (ai : G.Adj a (p.getVert i)) (aj : G.Adj a (p.getVert j)) : False := by
    have small := left_minimum_d2_with_two_ports hc even hp.1 yo yo hi hj ij.ne ai aj A aout (by
      intro z zA
      obtain ⟨k,km⟩ := active z zA
      have ks := sub_H z (mem_filter.mp zA).1 km
      rcases mem_insert.mp ks with rfl|ks
      · exact ⟨_,km,ai⟩
      · obtain rfl := mem_singleton.mp ks
        exact ⟨_,km,aj⟩)
    omega
  have noR (bi : G.Adj b (p.getVert i)) (bj : G.Adj b (p.getVert j)) : False := by
    have small := right_minimum_d2_with_two_ports hc even hp.1 yo yo hi hj ij.ne bi bj A aout (by
      intro z zA
      obtain ⟨k,km⟩ := active z zA
      have ks := sub_H z (mem_filter.mp zA).1 km
      rcases mem_insert.mp ks with rfl|ks
      · exact ⟨_,km,bi⟩
      · obtain rfl := mem_singleton.mp ks
        exact ⟨_,km,bj⟩)
    omega
  obtain ⟨le,re⟩ := pin_two_contacts_end hp.1 hc yo (few y yo) (cap y) hi hj gap
  have la : ¬G.Adj a (p.getVert j) := by
    intro e
    have ie := le j hj e
    have first : G.Adj a (p.getVert i) := by
      rw [ie]
      simpa using p.adj_getVert_succ (i:=0) (by omega)
    exact noL first e
  have rb : ¬G.Adj b (p.getVert i) := by
    intro e
    have je := re i hi e
    have last : G.Adj b (p.getVert j) := by
      have q := (p.adj_getVert_succ (pin_data hj).1).symm
      rwa [je,p.getVert_length] at q
    exact noR e last
  have iH := mark_holes_of_pin_and_missing_endpoint hp.1 yo hi
  have jH := mark_holes_of_pin_and_missing_endpoint hp.1 yo hj
  exact ⟨y,i,j,yo,hi,hj,gap,border,(fun z zo => sub_H z (whole z zo)),C,iH.2 rb,jH.1 la,
    (fun p => iH.1 (fun e => p (le i hi e))),
    (fun p => jH.2 (fun e => p (by have z := re j hj e; omega)))⟩
#print axioms length_eleven_four_off_two_pin_shape


private theorem hamilton_of_labeled_chain {n : ℕ} (φ : Fin n→V)
    [Nonempty V] (inj : Function.Injective φ) (onto : Function.Surjective φ)
    (l : List (Fin n)) (nd : l.Nodup) (all : ∀ i, i∈l)
    (chain : List.Chain' (fun i j => G.Adj (φ i) (φ j)) l) :
    ∃ a b : V, ∃ p : G.Walk a b,p.IsPath ∧ ∀ x,x∈p.support := by
  have make (a : V) (L : List V) (adj : List.Chain' G.Adj (a::L)) :
      ∃ b,∃ p : G.Walk a b,p.support=a::L := by
    induction L generalizing a with
    | nil => exact ⟨a,.nil,rfl⟩
    | cons b L ih =>
      obtain ⟨c,p,eq⟩ := ih b adj.tail
      exact ⟨c,.cons adj.rel_head p,by simp [eq]⟩
  have nl : (l.map φ).Nodup := nd.map inj
  have ml (x : V) : x∈l.map φ := by
    obtain ⟨i,rfl⟩ := onto x
    exact List.mem_map.mpr ⟨i,all i,rfl⟩
  have cl : List.Chain' G.Adj (l.map φ) := List.chain'_map_of_chain' φ (fun _ _ h => h) chain
  cases e : l.map φ with
  | nil =>
    -- The graph has a vertex in all intended applications.
    obtain ⟨x⟩ := (inferInstance : Nonempty V)
    have h := ml x
    simp [e] at h
  | cons a l =>
    rw [e] at cl nl
    obtain ⟨b,p,eq⟩ := make a l cl
    exact ⟨a,b,p,IsPath.mk' (eq.symm ▸ nl),fun x => by rw [eq,←e]; exact ml x⟩


private def omittedNeighbors {a b : V} (p : G.Walk a b) (x : V) : Finset V :=
  (G.neighborFinset x).filter (fun z=>z∉p.support)

private theorem omittedDegree_eq {a b x : V} {p : G.Walk a b}
    (hp : IsLongest p) (xo : x∉p.support) :
    G.degree x=(Pins p x).card+(omittedNeighbors p x).card := by
  classical
  have E : G.neighborFinset x=PinVertices p x∪omittedNeighbors p x := by
    ext w
    constructor
    · intro ww
      by_cases in_p : w∈p.support
      · obtain ⟨i,hi,iw⟩ := pin_of_neighbor_mem hp xo in_p ((mem_neighborFinset G x w).mp ww)
        exact mem_union.mpr (.inl (mem_image.mpr ⟨i,hi,iw⟩))
      · exact mem_union.mpr (.inr (mem_filter.mpr ⟨ww,in_p⟩))
    · intro ww
      rcases mem_union.mp ww with q|q
      · obtain ⟨i,hi,rfl⟩ := mem_image.mp q
        exact (mem_neighborFinset G x _).mpr (pin_data hi).2
      · exact (mem_filter.mp q).1
  have D : Disjoint (PinVertices p x) (omittedNeighbors p x) := disjoint_left.mpr (by
    intro z hz h
    obtain ⟨i,_,rfl⟩ := mem_image.mp hz
    exact (mem_filter.mp h).2 (p.getVert_mem_support _))
  have c := congrArg Finset.card E
  rwa [card_neighborFinset_eq_degree,card_union_of_disjoint D,card_pinVertices hp] at c


private theorem order_sixteen_four_off_labeling
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p) (len : p.length=11)
    (off : ((univ : Finset V)\p.support.toFinset).card=4) (xo : x∉p.support) :
    ∃ φ : Fin 16→V, Function.Injective φ ∧ Function.Surjective φ ∧ φ 12=x ∧
      (∀ k : Fin 16,k.val≤11 → φ k=p.getVert k.val) ∧
      (∀ k : Fin 16,12≤k.val → φ k∉p.support) := by
  classical
  let O := (univ : Finset V)\p.support.toFinset
  let Q := O.erase x
  have out {z : V} : z∈O ↔ z∉p.support := by simp [O]
  have xO := out.mpr xo
  have q3 : Q.card=3 := by
    change (O.erase x).card=3
    rw [card_erase_of_mem xO,show O.card=4 from off]
  let e : Fin 3 ≃ Q := (Fintype.equivFinOfCardEq (by simpa using q3)).symm
  let φ : Fin 16→V := fun v =>
    if h : v.val≤11 then p.getVert v.val else
    if k : v.val=12 then x else
    (e ⟨v.val-13,by have vu := v.isLt; omega⟩).val
  have on (v : Fin 16) (h : v.val≤11) : φ v=p.getVert v.val := by simp [φ,h]
  have at12 (v : Fin 16) (h : v.val=12) : φ v=x := by simp [φ,h]
  have after (v : Fin 16) (h : 13≤v.val) :
      φ v=(e ⟨v.val-13,by have vu := v.isLt; omega⟩).val := by
    simp [φ,show ¬v.val≤11 by omega,show v.val≠12 by omega]
  have afterQ (v : Fin 16) (hv : 13≤v.val) : φ v∈Q := by
    rw [after v hv]
    exact Subtype.property _
  have offP (v : Fin 16) (h : 12≤v.val) : φ v∉p.support := by
    by_cases h12 : v.val=12
    · rw [at12 v h12]
      exact xo
    · exact out.mp (mem_erase.mp (afterQ v (by omega))).2
  have inj : Function.Injective φ := by
    intro u v h
    apply Fin.ext
    by_cases uo : u.val≤11 <;> by_cases vo : v.val≤11
    · exact hp.1.getVert_injOn (show u.val≤p.length by omega) (show v.val≤p.length by omega)
        ((on u uo).symm.trans (h.trans (on v vo)))
    · exact False.elim (offP v (by omega) (h ▸ ((on u uo).symm ▸ p.getVert_mem_support u.val)))
    · exact False.elim (offP u (by omega) (h.symm ▸ ((on v vo).symm ▸ p.getVert_mem_support v.val)))
    by_cases u12 : u.val=12 <;> by_cases v12 : v.val=12
    · omega
    · exact False.elim ((mem_erase.mp (afterQ v (by omega))).1 (h.symm.trans (at12 u u12)))
    · exact False.elim ((mem_erase.mp (afterQ u (by omega))).1 (h.trans (at12 v v12)))
    · rw [after u (by omega),after v (by omega)] at h
      have q := congrArg Fin.val (e.injective (Subtype.ext h))
      change u.val-13=v.val-13 at q
      omega
  have cardV : Fintype.card V=16 := by
    have q := card_sdiff_add_card_eq_card (subset_univ p.support.toFinset)
    rw [List.toFinset_card_of_nodup hp.1.support_nodup,length_support,len,card_univ,off] at q
    exact q.symm
  have onto : Function.Surjective φ := by
    by_contra n
    have s := Fintype.card_lt_of_injective_not_surjective φ inj n
    rw [Fintype.card_fin,cardV] at s
    omega
  exact ⟨φ,inj,onto,at12 12 rfl,on,offP⟩
#print axioms order_sixteen_four_off_labeling
private theorem length_eleven_left_block_of_small_path_d2
    (hc : G.Connected)
    {a b x : V} {p : G.Walk a b} (hp : IsLongest p)
    (ah : 4≤G.degree a) (bh : 4≤G.degree b) (len : p.length=11)
    (xo : x∉p.support) (h1 : 1∈Pins p x)
    (small : ((DistanceTwo G a).filter (· ∈ p.support)).card≤2) :
    ∃ t : ℕ, 5≤t ∧ t≤9 ∧
      (∀ k : ℕ,3≤k → k≤t → G.Adj a (p.getVert k)) ∧
      (∀ k : ℕ,k≤p.length → G.Adj a (p.getVert k) → k=1 ∨ (3≤k ∧ k≤t)) ∧
      ¬G.Adj a b ∧ b∉DistanceTwo G a := by
  classical
  let D := (DistanceTwo G a).filter (· ∈ p.support)
  change D.card≤2 at small
  have vr {i j : ℕ} (ir : i≤p.length) (jr : j≤p.length) (ne : i≠j) :
      p.getVert i≠p.getVert j := fun e => ne (hp.1.getVert_injOn ir jr e)
  have na : ¬G.Adj a b := by
    intro e
    have ar : 10<p.length := by omega
    have ten : p.getVert 11=b := by simpa only [len] using p.getVert_length
    have ea : G.Adj a (p.getVert (10+1)) := by simpa only [ten] using e
    have eb : G.Adj b (p.getVert 10) := by simpa only [ten] using (p.adj_getVert_succ ar).symm
    exact not_adj_both_end_marks hp xo (p.getVert_mem_support 1) (pin_data h1).2 ar ea eb
  have aA : ¬G.Adj a (p.getVert 0) := by simp
  have first : G.Adj a (p.getVert 1) := by simpa using p.adj_getVert_succ (i:=0) (by omega)
  have nTwo : ¬G.Adj a (p.getVert 2) := start_not_adj_pin_successor hp xo h1
  have mkD {i : ℕ} (ip : 0<i) (ir : i≤p.length)
      (no : ¬G.Adj a (p.getVert i)) {j : ℕ} (adj : G.Adj a (p.getVert j))
      (edge : G.Adj (p.getVert j) (p.getVert i)) : p.getVert i∈D :=
    mem_filter.mpr ⟨mem_distanceTwo.mpr (dist_two hc (fun e => vr (i:=0) (Nat.zero_le _) ir
      (by omega) (p.getVert_zero.trans e)) no adj edge),p.getVert_mem_support i⟩
  have d2 : p.getVert 2∈D := mkD (by omega) (by omega) nTwo first
    (p.adj_getVert_succ (i:=1) (by omega))
  let A := (range 12).filter (fun i => G.Adj a (p.getVert i))
  have memA {i : ℕ} : i∈A ↔ i<12 ∧ G.Adj a (p.getVert i) := by simp [A]
  have sa : A.Nonempty := ⟨1,memA.mpr ⟨by omega,first⟩⟩
  let t := A.max' sa
  have tm : t∈A := max'_mem A sa
  have tb : t≤10 := by
    have b := memA.mp tm
    by_contra! big
    have eq : t=11 := by omega
    have q := b.2
    rw [eq,←len,p.getVert_length] at q
    exact na q
  have tmax {i : ℕ} (h : i∈A) : i≤t := le_max' A i h
  have injectA : (A.image p.getVert).card=A.card := by
    apply card_image_iff.mpr
    intro u hu v hv e
    have ur : u<12 := (memA.mp hu).1
    have vv : v<12 := (memA.mp hv).1
    exact hp.1.getVert_injOn (show u≤p.length by omega) (show v≤p.length by omega) e
  have allAdj : G.neighborFinset a ⊆ A.image p.getVert := by
    intro z zm
    have az := (mem_neighborFinset G a z).mp zm
    have zp : z∈p.support := Classical.byContradiction (fun e => (no_endpoints hp e).1 az.symm)
    obtain ⟨k,ke,kp⟩ := mem_support_iff_exists_getVert.mp zp
    exact mem_image.mpr ⟨k,memA.mpr ⟨by omega,ke.symm ▸ az⟩,ke⟩
  have amin : 4≤A.card := by
    have q := card_le_card allAdj
    rw [injectA,card_neighborFinset_eq_degree] at q
    omega
  have tge : 5≤t := by
    by_contra! low
    have aa : A⊆({1,3,4}:Finset ℕ) := by
      intro v vm
      have vl : v≤t := tmax vm
      have vlt : v<5 := lt_of_le_of_lt vl low
      have va := (memA.mp vm).2
      by_cases n0 : v=0
      · exact False.elim (aA (n0 ▸ va))
      by_cases n2 : v=2
      · exact False.elim (nTwo (n2 ▸ va))
      have vc : v=1 ∨ v=3 ∨ v=4 := by omega
      simpa using vc
    have c := card_le_card aa
    have c3 : ( {1,3,4}:Finset ℕ).card=3 := by decide
    omega
  have dt : p.getVert (t+1)∈D := by
    have no : ¬G.Adj a (p.getVert (t+1)) := fun h => by
      have := tmax (memA.mpr ⟨by omega,h⟩)
      omega
    exact mkD (by omega) (by omega) no (memA.mp tm).2 (p.adj_getVert_succ (i:=t) (by omega))
  have deq : D=({p.getVert 2,p.getVert (t+1)}:Finset V) := by
    symm
    apply eq_of_subset_of_card_le
    · intro z hz
      exact (mem_insert.mp hz).elim (fun e => e.symm ▸ d2) (fun e => (mem_singleton.mp e).symm ▸ dt)
    · rw [card_insert_of_not_mem (by
          simpa using vr (i:=2) (j:=t+1) (by omega) (by omega) (by omega)),card_singleton]
      omega
  have back (k : ℕ) (r : 3≤k) (kt : k≤t) : G.Adj a (p.getVert k) := by
    let P := fun n : ℕ => 3≤t-n → G.Adj a (p.getVert (t-n))
    have yes : ∀ n,P n := by
      intro n
      induction n with
      | zero => intro _; simpa using (memA.mp tm).2
      | succ n ih =>
          intro ge
          have r' : 3≤t-n := by
            change 3≤t-(n+1) at ge
            omega
          have old := ih r'
          by_cases yes : G.Adj a (p.getVert (t-(n+1)))
          · exact yes
          exfalso
          have e : t-n = t-(n+1)+1 := by
            change 3≤t-(n+1) at ge
            omega
          have zz : p.getVert (t-(n+1))∈D :=
            mkD (by change 3≤t-(n+1) at ge; omega) (by omega) yes old
              (by rw [e]; exact (p.adj_getVert_succ (i:=t-(n+1)) (by omega)).symm)
          rw [deq] at zz
          rcases mem_insert.mp zz with o|o
          · exact vr (i:=t-(n+1)) (j:=2) (by omega) (by omega)
              (by change 3≤t-(n+1) at ge; omega) o
          · exact vr (i:=t-(n+1)) (j:=t+1) (by omega) (by omega)
              (by omega) (mem_singleton.mp o)
    have k' : t-(t-k)=k := by omega
    have eq := yes (t-k)
    simp only [P,k'] at eq
    exact eq r
  have ee : t≠10 := by
    intro eq
    have dis : Disjoint (LeftMarks p∪RightMarks p) (∅:Finset ℕ) := by simp
    have bd := mark_length hp xo (p.getVert_mem_support 1) (pin_data h1).2 ∅ (empty_subset _) dis
    have ss : ({1,3,4,5,6,7,8,9,10}:Finset ℕ)⊆A := by
      intro v vm
      have q : v=1 ∨ (3≤v ∧ v≤10) := by
        simp only [mem_insert,mem_singleton] at vm
        omega
      rcases q with rfl|h
      · exact memA.mpr ⟨by omega,first⟩
      · exact memA.mpr ⟨by omega,back v h.1 (by omega)⟩
    have size := card_le_card ss
    norm_num at size
    -- The indexed left neighborhood is injective and contained in the actual neighborhood.
    have sub : A.image p.getVert⊆G.neighborFinset a := by
      intro v vm
      obtain ⟨i,im,rfl⟩ := mem_image.mp vm
      exact (mem_neighborFinset G a _).mpr (memA.mp im).2
    have ag := card_le_card sub
    rw [injectA,card_neighborFinset_eq_degree] at ag
    simp at bd
    omega
  have nbD : b∉D := by
    intro h
    rw [deq] at h
    rcases mem_insert.mp h with hh|hh
    · exact vr (i:=p.length) (j:=2) le_rfl (by omega) (by omega) (p.getVert_length.trans hh)
    · exact vr (i:=p.length) (j:=t+1) le_rfl (by omega) (by omega)
        (p.getVert_length.trans (mem_singleton.mp hh))

  refine ⟨t,tge,by omega,back,?_,na,?_⟩
  · intro k kr h
    have kA : k∈A := memA.mpr ⟨by omega,h⟩
    have kl : k≤t := tmax kA
    have n0 : k≠0 := fun e => aA (e ▸ h)
    have n2 : k≠2 := fun e => nTwo (e ▸ h)
    omega
  · intro d
    exact nbD (mem_filter.mpr ⟨d,p.end_mem_support⟩)
#print axioms length_eleven_left_block_of_small_path_d2



end Graffiti189LongestPath.TwoCut.SmallOrderFour
