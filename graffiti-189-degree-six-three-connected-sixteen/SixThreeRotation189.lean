import SixThreeFlanks189

namespace Graffiti189LongestPath.SixThreeSixteen
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.lengths_take_drop Graffiti189LongestPath.Rigidity.split_path_edge
  Graffiti189LongestPath.Rigidity.reverse_longest Graffiti189LongestPath.Rigidity.pin_reverse from Rigidity189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem getVert_take_local {a b : V} (p : G.Walk a b) (n i : ℕ) (hi : i≤n) :
    (p.take n).getVert i=p.getVert i := by
  induction p generalizing n i with
  | nil => cases n <;> cases i <;> rfl
  | @cons a b c e p ih =>
    cases n with
    | zero =>
      have q : i=0 := by omega
      subst i
      simp
    | succ n =>
      cases i with
      | zero => simp
      | succ i => exact ih n i (by omega)

theorem rotate_start_first_edge {a b : V} {p : G.Walk a b} (hp : IsLongest p) (j : ℕ)
    (j0 : 0<j) (jl : j<p.length) (jump : G.Adj a (p.getVert (j+1))) :
    ∃ q : G.Walk (p.getVert j) b, IsLongest q ∧
      (∀ z,z∈p.support ↔ z∈q.support) ∧ q.getVert 1=p.getVert (j-1) := by
  let l := p.take j
  let r := p.drop (j+1)
  let q := l.reverse.append (.cons jump r)
  have split := Graffiti189LongestPath.Rigidity.split_path_edge p j jl
  have ps : p.support=l.support++r.support := by
    conv_lhs => rw [←split]
    simp only [support_append,support_cons,List.tail_cons,l,r]
  have qs : q.support=l.support.reverse++r.support := by
    simp only [q,support_append,support_reverse,support_cons,List.tail_cons]
  have qpath : q.IsPath := by
    rw [isPath_def,qs,List.nodup_append]
    have nd := hp.1.support_nodup
    rw [ps,List.nodup_append] at nd
    exact ⟨List.nodup_reverse.mpr nd.1,nd.2.1,fun _ u v=>nd.2.2 (List.mem_reverse.mp u) v⟩
  have llen : l.length=j := (Graffiti189LongestPath.Rigidity.lengths_take_drop p j (by omega)).1
  have rlen : r.length=p.length-(j+1) :=
    (Graffiti189LongestPath.Rigidity.lengths_take_drop p (j+1) (by omega)).2
  have len : q.length=p.length := by
    simp only [q,length_append,length_reverse,length_cons,llen,rlen]
    omega
  have qLv : q.getVert 1=p.getVert (j-1) := by
    by_cases eq : j=1
    · have a0 : p.getVert (j-1)=a := by simp [eq]
      have j' : 1-l.reverse.length=0 := by simp [llen,eq]
      rw [show q=l.reverse.append (Walk.cons jump r) from rfl,getVert_append,
        if_neg (by simp [llen,eq]),j',getVert_zero,a0]
    have m : 1<l.reverse.length := by simp [llen]; omega
    rw [show q=l.reverse.append (Walk.cons jump r) from rfl,getVert_append,if_pos m,getVert_reverse,llen]
    exact getVert_take_local p j (j-1) (by omega)
  exact ⟨q,⟨qpath,fun u v w hw=>len.symm ▸ hp.2 u v w hw⟩,
    fun z=>by simp [ps,qs],qLv⟩

theorem endpoint_is_flank_implies_first_pin {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x∉p.support) (fa : a∈FlankVertices p x) :
    1∈Pins p x := by
  obtain ⟨j,jf,ja⟩ := mem_image.mp fa
  rcases mem_union.mp jf with jf|jf
  · obtain ⟨i,hi,e⟩ := mem_image.mp jf
    have il := (Graffiti189LongestPath.pin_data hi).1
    change i-1=j at e
    have d := hp.1.getVert_injOn (by omega : j≤p.length) (Nat.zero_le _)
      (ja.trans p.getVert_zero.symm)
    have i0 : i≠0 := by
      intro iz
      exact (Graffiti189LongestPath.no_endpoints hp hx).1
        (by simpa [iz] using (Graffiti189LongestPath.pin_data hi).2)
    have one : i=1 := by omega
    exact one ▸ hi
  obtain ⟨i,hi,e⟩ := mem_image.mp jf
  have il := (Graffiti189LongestPath.pin_data hi).1
  change i+1=j at e
  have d := hp.1.getVert_injOn (by omega : j≤p.length) (Nat.zero_le _)
    (ja.trans p.getVert_zero.symm)
  omega

theorem no_chord_to_pin_start (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤16) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x∉p.support) {i : ℕ} (hi : i∈Pins p x) (imin : 2≤i) :
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
  have sat := (saturated_flanks hc conn cap degree ord hq hxo).2
  have np := endpoint_is_flank_implies_first_pin hq hxo (sat ▸ inD)
  have edge' := (Graffiti189LongestPath.pin_data np).2
  rw [first] at edge'
  have fi : i-1-1∈Pins p x := mem_filter.mpr ⟨mem_range.mpr (by omega),edge'⟩
  have eq : i-1-1+2=i := by omega
  exact no_gap_two hc conn cap degree ord hp hx fi (eq.symm ▸ hi)

theorem no_chord_to_pin_end (hc : G.Connected) (conn : ConnThree G)
    (cap : ∀ v,(EvenFrom G v).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (ord : Fintype.card V≤16) {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {x : V} (hx : x∉p.support) {i : ℕ} (hi : i∈Pins p x) (imax : i+2≤p.length) :
    ¬G.Adj b (p.getVert i) := by
  have h := no_chord_to_pin_start hc conn cap degree ord
    (Graffiti189LongestPath.Rigidity.reverse_longest hp) (by simpa using hx)
    (Graffiti189LongestPath.Rigidity.pin_reverse hp hx hi) (by omega)
  rw [getVert_reverse,show p.length-(p.length-i)=i by omega] at h
  exact h

#print axioms no_chord_to_pin_start
#print axioms no_chord_to_pin_end
end Graffiti189LongestPath.SixThreeSixteen
