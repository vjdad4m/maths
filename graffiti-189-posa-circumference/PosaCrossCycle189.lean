import PosaCycleCover189
import StarCycleClosure189
import PosaCrossing189
open Finset SimpleGraph SimpleGraph.Walk
open Graffiti189LongestPath.PosaSpine Graffiti189LongestPath.StarCycleClosure Graffiti189LongestPath.PosaSpliceCommon
open PosaCrossing189
open private Graffiti189LongestPath.FanRoutable.path_append_separated from FanLower189
set_option warningAsError true
set_option maxHeartbeats 5000000
namespace Graffiti189LongestPath.PosaCrossCycle
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
/-- Two crossing endpoint chords close the outer two spine intervals. -/
theorem cycle_from_crossing {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (i j : Nat) (jp : 0<j) (ji : j<i) (in' : i<p.length)
    (e : G.Adj a (p.getVert i)) (f : G.Adj b (p.getVert j)) :
    ∃ c : G.Walk (p.getVert i) (p.getVert i), c.IsCycle ∧
      (∀ z∈c.support,z∈p.support) ∧
      (∀ k∈kept p.length j i,p.getVert k∈c.support) := by
  classical
  have jn := ji.le.trans in'.le
  obtain ⟨P,pp,po,pb,_,ps,pc⟩ := spine_segment p hp 0 j (by omega) jn
  obtain ⟨Q,qp,qo,qb,_,qs,qc⟩ := spine_segment p hp i p.length (by omega) le_rfl
  let L := P.copy p.getVert_zero rfl
  let R := Q.copy rfl p.getVert_length
  have lp : L.IsPath := by simpa [L] using pp
  have rp : R.IsPath := by simpa [R] using qp
  have Ls : ∀ z∈L.support,z∈p.support := by simpa [L] using ps
  have Rs : ∀ z∈R.support,z∈p.support := by simpa [R] using qs
  have Lb : Bounds p L 0 j := by simpa [L,Bounds,support_copy] using pb
  have Rb : Bounds p R i p.length := by simpa [R,Bounds,support_copy] using qb
  have Lc : ∀ k≤p.length,p.getVert k∈L.support ↔ 0≤k ∧ k≤j := by
    simpa [L] using pc
  have Rc : ∀ k≤p.length,p.getVert k∈R.support ↔ i≤k ∧ k≤p.length := by
    simpa [R] using qc
  have dj : List.Disjoint L.support R.support := by
    intro z zl zr
    obtain ⟨k,e,kl⟩ := mem_support_iff_exists_getVert.mp (Ls z zl)
    have l := (Lb k kl (e.symm ▸ zl)).2
    have r := (Rb k kl (e.symm ▸ zr)).1
    omega
  let C := f.symm.toWalk
  have Cs : ∀ z∈C.support,z=p.getVert j ∨ z=b := by
    intro z hz
    simpa [C,Adj.toWalk] using hz
  have bl : b∉L.support := fun h =>
    (not_le_of_gt (by omega : j<p.length)) (Lb p.length le_rfl (p.getVert_length.symm ▸ h)).2
  let U := L.append C
  have Up : U.IsPath := Graffiti189LongestPath.FanRoutable.path_append_separated lp
    (IsPath.of_adj f.symm) (fun z zl zc => (Cs z zc).elim id (fun h => (bl (h ▸ zl)).elim))
  let W := U.append R.reverse
  have Wp : W.IsPath := Graffiti189LongestPath.FanRoutable.path_append_separated Up rp.reverse (by
    intro z zu zr
    rw [show U=L.append C from rfl,mem_support_append_iff] at zu
    rw [support_reverse,List.mem_reverse] at zr
    rcases zu with zl|zc
    · exact (dj zl zr).elim
    exact (Cs z zc).elim (fun h => (dj (h.symm ▸ L.end_mem_support) zr).elim) id)
  have ip : 0<i := by omega
  have aR : a∉R.support := fun h =>
    (not_le_of_gt ip) (Rb 0 (by omega) (p.getVert_zero.symm ▸ h)).1
  have naC : a∉C.support := by
    intro h
    have ne := internal_index_not_endpoint hp j jp (by omega)
    rcases Cs a h with h|h
    · exact ne.1 h.symm
    · have v := hp.getVert_injOn (by change 0≤p.length; omega) (by simp)
        (p.getVert_zero.trans (h.trans p.getVert_length.symm))
      omega
  have iL : p.getVert i∉L.support := fun h => (not_le_of_gt ji) (Lb i in'.le h).2
  have fresh : s(p.getVert i,a)∉W.edges := by
    intro h
    rw [show W=U.append R.reverse from rfl,edges_append,List.mem_append] at h
    rcases h with h|h
    · rw [show U=L.append C from rfl,edges_append,List.mem_append] at h
      exact h.elim (fun h => iL (L.fst_mem_support_of_mem_edges h))
        (fun h => naC (C.snd_mem_support_of_mem_edges h))
    exact aR (by simpa only [support_reverse,List.mem_reverse] using
      R.reverse.snd_mem_support_of_mem_edges h)
  let T := Walk.cons e.symm W
  have TP : T.IsCycle := (cons_isCycle_iff _ _).mpr ⟨Wp,fresh⟩
  have tbl : ∀ z∈W.support,z∈p.support := by
    intro z zw
    rw [show W=U.append R.reverse from rfl,mem_support_append_iff] at zw
    rcases zw with zu|zr
    · rw [show U=L.append C from rfl,mem_support_append_iff] at zu
      exact zu.elim (Ls z) (fun zc => (Cs z zc).elim
        (fun h => h.symm ▸ p.getVert_mem_support j) (fun h => h.symm ▸ p.end_mem_support))
    · exact Rs z (by simpa only [support_reverse,List.mem_reverse] using zr)
  refine ⟨T,TP,?_,?_⟩
  · intro z zt
    exact (List.mem_cons.mp zt).elim (fun h => h.symm ▸ p.getVert_mem_support i) (tbl z)
  · intro k kk
    apply List.mem_cons_of_mem
    apply (mem_support_append_iff U R.reverse).mpr
    rcases mem_kept.mp kk with a|⟨lo,hi⟩
    · exact Or.inl ((mem_support_append_iff L C).mpr
        (Or.inl ((Lc k (a.trans jn)).mpr ⟨Nat.zero_le _,a⟩)))
    · exact Or.inr (by simpa only [support_reverse,List.mem_reverse] using
        ((Rc k hi).mpr ⟨lo,hi⟩))

variable [Fintype V]

omit [Fintype V] in
theorem cycle_ge_index_card {a b z : V} (p : G.Walk a b) (hp : p.IsPath)
    (c : G.Walk z z) (hc : c.IsCycle) (S : Finset Nat)
    (range : ∀ i∈S,i≤p.length) (hit : ∀ i∈S,p.getVert i∈c.support) :
    S.card≤c.length := by
  classical
  have sub : S.image p.getVert⊆c.support.toFinset := by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hw
    exact List.mem_toFinset.mpr (hit i hi)
  have C := card_le_card sub
  rw [cycle_card_support c hc,card_image_of_injOn (fun i hi j hj e =>
    hp.getVert_injOn (range i hi) (range j hj) e)] at C
  exact C

omit [Fintype V] [DecidableEq V] in
theorem close_spine_path {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (long : 2≤p.length) (e : G.Adj a b) :
    ∃ c : G.Walk b b,c.IsCycle ∧ c.length=p.length+1 ∧
      (∀ z,z∈c.support ↔ z∈p.support) := by
  have es : s(b,a)∉p.edges := by
    cases p with
    | nil => simp at long
    | @cons a u b f q =>
      intro h
      rcases List.mem_cons.mp h with h|h
      · rcases Sym2.eq_iff.mp h with h|h
        · exact e.ne h.1.symm
        have eq : u=b := h.1.symm
        subst u
        have hq := ((cons_isPath_iff _ _).mp hp).1
        have eq := (isPath_iff_eq_nil _).mp hq
        simp [eq] at long
      · exact ((cons_isPath_iff _ _).mp hp).2 (q.snd_mem_support_of_mem_edges h)
  refine ⟨Walk.cons e.symm p,(cons_isCycle_iff _ _).mpr ⟨hp,es⟩,rfl,?_⟩
  intro z
  simp only [support_cons,List.mem_cons]
  exact ⟨fun h => h.elim (fun r => r.symm ▸ p.end_mem_support) id,Or.inr⟩

#print axioms cycle_from_crossing
#print axioms cycle_ge_index_card
#print axioms close_spine_path
end Graffiti189LongestPath.PosaCrossCycle
