import CutEntry180

set_option warningAsError true
namespace Minimal180.CutGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

namespace TightCut
variable {J : SimpleGraph V} {S T : Finset V} {x y w : V} {r : ↥S} {odd : Bool} {A : Finset V}
variable (h : TightCut J S T x y w r odd A)
include h

/-- Away from the root an unequal-marked, lower-deficit-one cut has at
most one outward lower neighbor at each vertex of the union of marks. -/
theorem outward_unique (rank1 : bipartiteNum J+1=Fintype.card V) (ne : A≠parity (J⊔edge x y) r.val odd)
    {v i j : V} (mark : v∈A∪parity (J⊔edge x y) r.val odd) (vr : v≠r.val)
    (vi : J.Adj v i) (vj : J.Adj v j) (di : J.dist i r.val=J.dist v r.val+1)
    (dj : J.dist j r.val=J.dist v r.val+1) : i=j := by
  classical
  apply Classical.byContradiction
  intro ij
  obtain ⟨_,dx,dy⟩ := seam_layers h.connected h.split h.farTip h.rightSpoke h.absent r h.horizontal
  have nr {u : V} (eq : J.dist u r.val=J.dist w r.val+1) : r.val≠u := by
    rintro hv
    rw [←hv,dist_self] at eq
    omega
  have same {k : V} (e : (J⊔edge x y).Adj r.val k) : J.Adj r.val k := by
    rcases e with e|e
    · exact e
    rcases ((edge_adj ..).mp e).1 with z|z
    · exact (nr dx z.1).elim
    · exact (nr dy z.1).elim
  obtain ⟨l,m,rl,rm,lm⟩ := block_neighbors (J⊔edge x y) (h.connected.mono le_sup_left) (by have := h.order; omega) h.block r.val
  obtain ⟨M,mj,tr,root,mi,mk,⟨z,mz,zi,zj⟩,cross⟩ :=
    branching_layer_tree h.connected vi.symm vj di dj ⟨l,m,same rl,same rm,lm⟩ (fun eq => (vr eq).elim) odd
  have ai : Indep J A := fun u a k b d e => h.independent u a k b d (Or.inl e)
  have op {a b : V} (e : M.Adj a b) : a∈parity (J⊔edge x y) r.val odd ↔ b∉parity (J⊔edge x y) r.val odd := h.layers_eq ▸ cross e
  have cap := (one_defect_rigid J M tr mj (by have := h.order; omega) r.val root A _ ai ne op rank1 h.tight).2.1 v mark
  have inc : ({z,i,j}:Finset V)⊆M.neighborFinset v := insert_subset ((M.mem_neighborFinset ..).mpr mz)
    (insert_subset ((M.mem_neighborFinset ..).mpr mi.symm) (singleton_subset_iff.mpr ((M.mem_neighborFinset ..).mpr mk.symm)))
  have c := card_le_card inc
  rw [card_insert_of_not_mem (by simp [zi,zj]),card_pair (show i≠j from ij),card_neighborFinset_eq_degree] at c
  omega

/-- A failed lower-deficit-one cut forces a shortest-path chain of mark
disagreements. Each occupied depth is unique, and every disagreement after
the first has a unique predecessor in the whole lower graph. -/
theorem defect_one_chain (rank1 : bipartiteNum J+1=Fintype.card V) :
    let G := J⊔edge x y
    let P := parity G r.val odd
    let U := eligible A P r.val
    let D := (A∪P)\(A∩P)
    ¬weightedLeaves J U<weightedLeaves G U →
      P.card=A.card+1 ∧ ∃ t∈({x,y}:Finset V), t∈D ∧
        (∀ i∈D, J.dist t r.val≤J.dist i r.val) ∧
        (∀ i∈D, ∀ j∈D, J.dist i r.val=J.dist j r.val → i=j) ∧
        ∀ i∈D, i≠t → ∃ q∈D, Arc J r.val q i := by
  classical
  intro G P U D ng
  obtain ⟨root,mass,t,tip,td,enter⟩ := h.defect_one_entry rank1 ng
  change A.card<P.card at mass
  have transport {u v : V} (eq : u=v) (ud : u∈D) : v∈D := eq ▸ ud
  have ne : A≠P := fun eq => ng (h.confined_gain eq.le)
  let d (i : V) := J.dist i r.val
  let parent (i : V) := if ir : i=r.val then r.val else (Graffiti169.exists_predecessor J h.connected r.val i ir).choose
  have pred {i : V} (marked : i∈D) : J.Adj i (parent i) ∧ d i=d (parent i)+1 := by
    have ir : i≠r.val := fun e => root (transport e marked)
    simpa [parent,ir,d] using (Graffiti169.exists_predecessor J h.connected r.val i ir).choose_spec
  have stay {i q : V} (marked : i∈D) (it : i≠t) (iq : J.Adj i q) (dd : d i=d q+1) : q∈D :=
    Classical.byContradiction fun out => it (enter i marked q iq dd out)
  have pg {i : V} (marked : i∈D) (it : i≠t) : parent i∈D := stay marked it (pred marked).1 (pred marked).2
  have base (k : ℕ) : ∀ i∈D, d i=k → d t≤k := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i di eq
      by_cases it : i=t
      · simp [←it,eq]
      · have down := (pred di).2
        have prev := ih (d (parent i)) (by omega) (parent i) (pg di it) rfl
        omega
  have unique (k : ℕ) : ∀ i∈D, ∀ j∈D, d i=k → d j=k → i=j := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i di j dj idk jdk
      have tip_only {a : V} (ad : a∈D) (ak : d a=d t) : a=t := by
        apply Classical.byContradiction
        intro atip
        have prev := base _ _ (pg ad atip) rfl
        have down := (pred ad).2
        omega
      by_cases it : i=t
      · exact it.trans (tip_only dj (by rw [←it,idk,jdk])).symm
      by_cases jt : j=t
      · exact (tip_only di (by rw [←jt,idk,jdk])).trans jt.symm
      obtain ⟨ei,hi⟩ := pred di
      obtain ⟨ej,hj⟩ := pred dj
      have pi := pg di it
      have pj := pg dj jt
      have same := ih (d (parent i)) (by omega) _ pi _ pj rfl (by omega)
      have vr : parent i≠r.val := fun e => root (transport e pi)
      apply h.outward_unique rank1 ne (mem_sdiff.mp pi).1 vr ei.symm (same ▸ ej.symm) hi
      simpa only [same] using hj
  have parity_old : parity J r.val odd=P := h.layers_eq
  have opposite {i : V} (ip : i∈P) {q : V} (down : d i=d q+1) : q∉P := by
    rw [←parity_old] at ip ⊢
    intro qp
    have a := (mem_parity ..).mp ip
    have b := (mem_parity ..).mp qp
    change d i%2=odd.toNat at a
    change d q%2=odd.toNat at b
    omega
  have map_in {i : V} (hi : i∈(P\A).erase t) : parent i∈A\P := by
    obtain ⟨it,ip⟩ := mem_erase.mp hi
    obtain ⟨p,na⟩ := mem_sdiff.mp ip
    have dd : i∈D := mem_sdiff.mpr ⟨mem_union_right _ p,fun z => na (mem_inter.mp z).1⟩
    have no := opposite p (pred dd).2
    have q := mem_sdiff.mp (pg dd it)
    exact mem_sdiff.mpr ⟨(mem_union.mp q.1).resolve_right no,no⟩
  have inj : Set.InjOn parent (↑((P\A).erase t) : Set V) := by
    intro a ha b hb same
    have mD {i : V} (hi : i∈(P\A).erase t) : i∈D := by
      obtain ⟨pt,an⟩ := mem_sdiff.mp (mem_of_mem_erase hi)
      exact mem_sdiff.mpr ⟨mem_union_right _ pt,fun z => an (mem_inter.mp z).1⟩
    have ad := mD ha
    have bd := mD hb
    have da := (pred ad).2
    have db := (pred bd).2
    exact unique _ _ ad _ bd rfl (by rw [db,←same,←da])
  have cap := card_le_card (show ((P\A).erase t).image parent⊆A\P from fun _ v => by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp v
    exact map_in hi)
  rw [card_image_of_injOn inj] at cap
  have erase := card_le_card (show P\A⊆insert t ((P\A).erase t) from fun i hi => by
    by_cases eq : i=t
    · exact mem_insert.mpr (Or.inl eq)
    · exact mem_insert_of_mem (mem_erase.mpr ⟨eq,hi⟩))
  have ce := card_insert_le t ((P\A).erase t)
  have cp := card_sdiff_add_card_inter P A
  have ca := card_sdiff_add_card_inter A P
  rw [inter_comm P A] at cp
  refine ⟨by omega,t,tip,td,fun i di => base _ i di rfl,fun i di j dj k => unique _ i di j dj rfl k.symm,?_⟩
  intro i di it
  obtain ⟨e,down⟩ := pred di
  refine ⟨parent i,pg di it,e.symm,down,?_⟩
  intro z zi dz
  have zd := stay di it zi.symm dz
  exact unique _ z zd _ (pg di it) rfl (by change d i=d z+1 at dz; omega)

#print axioms outward_unique
#print axioms defect_one_chain
end TightCut
end Minimal180.CutGain
