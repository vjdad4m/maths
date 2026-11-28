import SixThree21OmittedRoute189

namespace Graffiti189LongestPath.SixThreeTwentyOne
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity 
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.lengths_take_drop from Rigidity189
open private Graffiti189LongestPath.SixThreeTwenty.getVert_take_local from SixThree20IndexedRotation189
open private Graffiti189LongestPath.SixThreeNineteen.getVert_drop_local from SixThree19ExtremeRotation189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem linked_pins_gap_at_least_route {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    {i j : ℕ} (ip : i∈Pins p x) (jp : j∈Pins p y) (ij : i<j)
    (q : G.Walk x y) (hq : q.IsPath) (off : ∀ v∈q.support,v∉p.support) :
    i+q.length+2≤j := by
  classical
  have il := (Graffiti189LongestPath.pin_data ip).1
  have jl := (Graffiti189LongestPath.pin_data jp).1
  let L := p.take i
  let R := p.drop j
  have ll : L.length=i := (Graffiti189LongestPath.Rigidity.lengths_take_drop p i il.le).1
  have rl : R.length=p.length-j := (Graffiti189LongestPath.Rigidity.lengths_take_drop p j jl.le).2
  have li (k : ℕ) (kl : k≤L.length) : L.getVert k=p.getVert k :=
    Graffiti189LongestPath.SixThreeTwenty.getVert_take_local p i k (by omega)
  have ri (k : ℕ) : R.getVert k=p.getVert (j+k) :=
    Graffiti189LongestPath.SixThreeNineteen.getVert_drop_local p j k
  have lp : L.IsPath := by
    apply (IsPath.getVert_injOn_iff L).mp
    intro s sl t tl h
    change s≤L.length at sl
    change t≤L.length at tl
    rw [li s sl,li t tl] at h
    exact hp.1.getVert_injOn (by omega : s≤p.length) (by omega : t≤p.length) h
  have rp : R.IsPath := by
    apply (IsPath.getVert_injOn_iff R).mp
    intro s sl t tl h
    change s≤R.length at sl
    change t≤R.length at tl
    rw [ri s,ri t] at h
    have eq := hp.1.getVert_injOn (by omega : j+s≤p.length) (by omega : j+t≤p.length) h
    omega
  have ldata {v : V} (vm : v∈L.support) : ∃ k : ℕ, k ≤ i ∧ p.getVert k=v := by
    obtain ⟨k,e,kl⟩ := mem_support_iff_exists_getVert.mp vm
    exact ⟨k,by omega,(li k kl).symm.trans e⟩
  have rdata {v : V} (vm : v∈R.support) : ∃ k : ℕ, j ≤ k ∧ k≤p.length ∧ p.getVert k=v := by
    obtain ⟨k,e,kl⟩ := mem_support_iff_exists_getVert.mp vm
    exact ⟨j+k,by omega,by omega,(ri k).symm.trans e⟩
  have sep : List.Disjoint L.support R.support := by
    intro v vl vr
    obtain ⟨s,si,sv⟩ := ldata vl
    obtain ⟨t,jt,tl,tv⟩ := rdata vr
    have eq := hp.1.getVert_injOn (by omega : s≤p.length) tl (sv.trans tv.symm)
    omega
  let u : G.Walk (p.getVert i) y := Walk.cons (Graffiti189LongestPath.pin_data ip).2.symm q
  let w : G.Walk y b := Walk.cons (Graffiti189LongestPath.pin_data jp).2 R
  let r := L.append (u.append w)
  have supp : r.support=L.support++(q.support++R.support) := by
    simp only [r,u,w,support_append,support_cons,List.tail_cons,List.cons_append]
  have qr : List.Disjoint q.support R.support := by
    intro v vq vr
    obtain ⟨k,_,_,e⟩ := rdata vr
    exact off v vq (e ▸ p.getVert_mem_support k)
  have ls : List.Disjoint L.support (q.support++R.support) := by
    intro v vl vm
    rcases List.mem_append.mp vm with vq|vr
    · obtain ⟨k,_,e⟩ := ldata vl
      exact off v vq (e ▸ p.getVert_mem_support k)
    exact sep vl vr
  have path : r.IsPath := by
    apply IsPath.mk'
    rw [supp,List.nodup_append,List.nodup_append]
    exact ⟨lp.support_nodup,⟨hq.support_nodup,rp.support_nodup,qr⟩,ls⟩
  have len := hp.2 a b r path
  simp only [r,length_append,u,w,length_cons,ll,rl] at len
  omega

#print axioms linked_pins_gap_at_least_route
end Graffiti189LongestPath.SixThreeTwentyOne
