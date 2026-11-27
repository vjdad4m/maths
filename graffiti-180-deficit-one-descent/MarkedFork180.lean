import DeficitOneCut180

set_option warningAsError true
namespace Minimal180.DescentOne
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For an independent mark, a marked branch and an edge avoiding the
mark spend two separate units in the degree-sum bound. -/
theorem marked_fork_count (M : SimpleGraph V) [DecidableRel M.Adj] (tr : M.IsTree) (hn : 1<Fintype.card V)
    {I : Finset V} (ind : Indep M I) {w a b : V} (wm : w∈I) (branch : 3≤M.degree w)
    (ab : M.Adj a b) (ai : a∉I) (bi : b∉I) :
    2*I.card+2≤(I∩leaves M).card+(Fintype.card V-1) := by
  classical
  let E := I.biUnion (fun i => M.incidenceFinset i)
  have mass : (∑ v∈I,M.degree v)=E.card := independent_mass M I ind
  have sub : E⊆M.edgeFinset := by
    intro e em
    obtain ⟨i,_,h⟩ := mem_biUnion.mp em
    rw [M.incidenceFinset_eq_filter] at h
    exact (mem_filter.mp h).1
  have fresh : s(a,b)∉E := by
    intro em
    obtain ⟨i,im,he⟩ := mem_biUnion.mp em
    rw [M.incidenceFinset_eq_filter] at he
    rcases Sym2.mem_iff.mp (mem_filter.mp he).2 with eq|eq
    · exact ai (eq ▸ im)
    · exact bi (eq ▸ im)
  have edges := card_le_card (insert_subset (show s(a,b)∈M.edgeFinset from mem_edgeFinset.mpr ab) sub)
  rw [card_insert_of_not_mem fresh] at edges
  have vi (v : V) : 2+(M.degree v-2)≤M.degree v+(if v∈leaves M then 1 else 0) := by
    obtain ⟨z,e⟩ := exists_adj M tr.isConnected hn v
    have pos := (M.degree_pos_iff_exists_adj v).mpr ⟨z,e⟩
    have lf : v∈leaves M ↔ M.degree v=1 := by simp [leaves,SimpleGraph.degree,SimpleGraph.neighborFinset]
    split_ifs with h
    · have := lf.mp h; omega
    · have := mt lf.mpr h; omega
  have total := sum_le_sum (s:=I) (fun v _ => vi v)
  have c : (∑ v∈I,if v∈leaves M then 1 else 0 : ℕ)=(I∩leaves M).card := by simp [filter_mem_eq_inter]
  simp only [sum_add_distrib,sum_const,smul_eq_mul] at total
  rw [mass,c] at total
  have ob := single_le_sum (s:=I) (f:=fun v => M.degree v-2) (fun _ _ => Nat.zero_le _) wm
  change M.degree w-2≤∑ v∈I,(M.degree v-2) at ob
  have := tr.card_edgeFinset
  omega

/-- A connected graph can retain three specified spokes and an extra
edge when one endpoint of the extra edge is outside the star. -/
theorem marked_fork (J : SimpleGraph V) (jc : J.Connected) (hn : 1<Fintype.card V)
    (I : Finset V) (ind : Indep J I) {w x y z a b : V} (wm : w∈I)
    (wx : J.Adj w x) (wy : J.Adj w y) (wz : J.Adj w z) (xy : x≠y) (zx : z≠x) (zy : z≠y)
    (ab : J.Adj a b) (ai : a∉I) (bi : b∉I) (out : a∉({x,y,z}:Finset V)) :
    2*I.card+2≤weightedLeaves J I+(Fintype.card V-1) := by
  classical
  have aw : a≠w := fun eq => ai (eq ▸ wm)
  let p (i : V) := if i=a then b else w
  let d (i : V) : ℕ := if i=w then 0 else if i=a then 2 else 1
  have down (i : V) (iw : i≠w) : d (p i)<d i := by
    by_cases ia : i=a
    · subst i
      have bw : b≠w := fun eq => bi (eq ▸ wm)
      simp [d,p,aw,bw,ab.ne.symm]
    · simp [d,p,iw,ia]
  obtain ⟨K,kt,keepK⟩ := virtual_tree w p d down
  obtain ⟨M,mj,tr,keep⟩ := keep_target J K jc kt
  have star {i : V} (im : i∈({x,y,z}:Finset V)) (wi : J.Adj w i) : M.Adj w i := by
    have ia : i≠a := fun eq => out (eq ▸ im)
    exact (keep (show (J⊓K).Adj i w from ⟨wi.symm,by simpa [p,ia] using keepK i wi.ne.symm⟩)).symm
  have e : M.Adj a b := keep ⟨ab,by simpa [p] using keepK a aw⟩
  have inc : ({z,x,y}:Finset V)⊆M.neighborFinset w := insert_subset
    ((M.mem_neighborFinset ..).mpr (star (by simp) wz)) (insert_subset
      ((M.mem_neighborFinset ..).mpr (star (by simp) wx)) (singleton_subset_iff.mpr ((M.mem_neighborFinset ..).mpr (star (by simp) wy))))
  have deg := card_le_card inc
  rw [card_insert_of_not_mem (by simp [zx,zy]),card_pair xy,card_neighborFinset_eq_degree] at deg
  have bound := marked_fork_count M tr hn (fun i hi j hj ne ed => ind i hi j hj ne (mj ed)) wm deg e ai bi
  have score : (I∩leaves M).card≤weightedLeaves J I :=
    le_sup (f:=fun K => (I∩leaves K).card) (mem_filter.mpr ⟨mem_univ _,mj,tr⟩)
  omega

#print axioms marked_fork
end Minimal180.DescentOne
