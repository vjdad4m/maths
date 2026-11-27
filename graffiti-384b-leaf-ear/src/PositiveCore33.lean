import CoreColor33

namespace Graffiti384b.PositiveCore33
open Finset SimpleGraph LowSample
open private TrianglePrune.skeleton TrianglePrune.scores TrianglePrune.triangle_iff from TrianglePrune384b
open private OneEar.deg2 from OneEarFinish384b
open private Repair.triangles_le_choose Repair.omit_set from Repair384b
open private LowSample.two_degree from LowSample384b

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The spanning graph of edges occurring in triangles. The earlier skeleton's
choice of reference vertex has no effect when its exceptional set is empty. -/
abbrev backbone (z : V) := TrianglePrune.skeleton G z ∅

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem backbone_adj {z v w : V} : (backbone G z).Adj v w ↔
    G.Adj v w ∧ ∃ x,G.Adj v x ∧ G.Adj w x := by simp [backbone,TrianglePrune.skeleton]

theorem backbone_scores (z v : V) : trianglesAt (backbone G z) v=trianglesAt G v :=
  TrianglePrune.scores G z ∅ v

private theorem positive_ends {z v w : V} (vw : (backbone G z).Adj v w) : 0<trianglesAt G v := by
  obtain ⟨edge,x,vx,wx⟩ := (backbone_adj G).mp vw
  exact (TrianglePrune.triangle_iff G v).mpr ⟨w,x,edge,vx,wx⟩

/-- The opposite positive vertices, whichever color the zero vertex received. -/
def opposite (z : V) (A : Finset V) (v : V) :=
  ((univ : Finset V).erase z).filter (fun w => (w∈A ↔ v∉A))

def Colors (z : V) (A : Finset V) : Prop :=
  ∀ v,v≠z → 2≤nbr G v (opposite z A v)

private theorem opp_left {z v : V} {A : Finset V} (h : v∈A) : opposite z A v=Aᶜ.erase z := by
  ext w; simp [opposite,h]
private theorem opp_right {z v : V} {A : Finset V} (h : v∉A) : opposite z A v=A.erase z := by
  ext w; simp [opposite,h]

set_option maxHeartbeats 1800000 in
theorem color_exists {z : V} (inj : Function.Injective (trianglesAt G)) (zz : trianglesAt G z=0) :
    ∃ A,Colors (backbone G z) z A := by
  classical
  let J := backbone G z
  have sc (v : V) : trianglesAt J v=trianglesAt G v := backbone_scores G z v
  have pos {v : V} (ne : v≠z) : 0<trianglesAt J v := Nat.pos_of_ne_zero
    (fun eq => ne (inj ((sc v).symm.trans (eq.trans zz.symm))))
  have non {v : V} (ne : v≠z) : v∈nonleaves J := by
    obtain ⟨a,b,va,vb,ab⟩ := (TrianglePrune.triangle_iff J v).mp (pos ne)
    exact mem_filter.mpr ⟨mem_univ _,OneEar.deg2 J ab.ne va vb⟩
  have iso (v : V) : ¬J.Adj z v := fun edge => (Nat.ne_of_gt (positive_ends G edge)) zz
  have nz : z∉nonleaves J := by
    have empty : J.neighborFinset z=∅ := Finset.eq_empty_of_forall_not_mem (fun v m => iso v ((J.mem_neighborFinset _ _).mp m))
    have d : J.degree z=0 := by rw [← card_neighborFinset_eq_degree,empty,card_empty]
    intro m; have := (mem_filter.mp m).2; omega
  have twopos {v : V} (vm : v∈twos J) : 0<trianglesAt J v :=
    pos (fun eq => nz (eq ▸ (mem_sdiff.mp vm).1))
  have one {v : V} (vm : v∈twos J) : trianglesAt J v=1 := by
    have ub := Repair.triangles_le_choose J v
    rw [LowSample.two_degree J vm,Nat.choose_self] at ub
    have := twopos vm; omega
  have cut : CoreColor33.GoodCut J := by
    by_cases empty : twos J=∅
    · apply CoreColor33.pinned J (P:=∅) (Q:=∅) (by simp) _ (by simp) (by simp)
      intro v vn _ _
      by_cases vh : v∈high J
      · exact (mem_filter.mp vh).2
      · have inTwo : v∈twos J := mem_sdiff.mpr ⟨vn,vh⟩
        rw [empty] at inTwo
        exact (Finset.not_mem_empty _ inTwo).elim
    obtain ⟨e,em⟩ := nonempty_iff_ne_empty.mpr empty
    have single : twos J={e} := by
      ext v
      constructor
      · intro vm; apply mem_singleton.mpr; apply inj
        exact (sc v).symm.trans ((one vm).trans ((one em).symm.trans (sc e)))
      · intro vm; exact (mem_singleton.mp vm) ▸ em
    apply CoreColor33.single J _ (fun u v _ _ hu hv => inj ((sc u).symm.trans (hu.trans (hv.symm.trans (sc v))))) single (twopos em)
    intro u v edge _ _
    obtain ⟨uv,x,ux,vx⟩ := (backbone_adj G).mp edge
    exact ⟨x,(backbone_adj G).mpr ⟨ux,v,uv,vx.symm⟩,(backbone_adj G).mpr ⟨vx,u,uv.symm,ux.symm⟩⟩
  obtain ⟨A,L,R⟩ := cut
  refine ⟨A,?_⟩
  intro v ne
  have drop (B : Finset V) : nbr J v B = nbr J v (B.erase z) := by
    unfold nbr; congr 1; ext w
    by_cases wz : w=z
    · subst w; simp [show ¬J.Adj v z from fun h => iso v h.symm]
    · simp [wz]
  by_cases va : v∈A
  · rw [opp_left va,← drop]; exact L v (non ne) va
  · rw [opp_right va,← drop]; exact R v (non ne) (mem_compl.mpr va)

theorem lift_colors {z : V} {A : Finset V} (colors : Colors (backbone G z) z A) : Colors G z A := by
  intro v ne
  exact (colors v ne).trans (card_le_card (show _⊆(opposite z A v).filter (G.Adj v) from
    fun w m => mem_filter.mpr ⟨(mem_filter.mp m).1,((backbone_adj G).mp (mem_filter.mp m).2).1⟩))

theorem complement {z : V} {A : Finset V} (colors : Colors G z A) : Colors G z Aᶜ := by
  intro v ne; have h := colors v ne
  have eq : opposite z Aᶜ v=opposite z A v := by ext w; simp [opposite]; tauto
  rwa [eq]

/-- Any two such colors have sixteen positive members each. -/
theorem balanced (n : Fintype.card V=33) (t : (types G).card=33) (fail : bound G<gamma G)
    {z : V} {A : Finset V} (h : Colors G z A) :
    (A.erase z).card=16 ∧ (Aᶜ.erase z).card=16 ∧ gamma G=17 := by
  have cap (B : Finset V) (col : Colors G z B) : gamma G≤33-(B.erase z).card := by
    rw [← n]; apply Repair.omit_set
    intro v vm
    obtain ⟨ne,vb⟩ := mem_erase.mp vm
    have o := col v ne
    rw [opp_left vb] at o
    exact o.trans (card_le_card (filter_subset_filter _ (fun w wm => mem_compl.mpr
      (fun b => mem_compl.mp (erase_subset _ _ wm) (erase_subset _ _ b)))))
  have l := cap A h
  have r := cap Aᶜ (complement G h)
  have sum : (A.erase z).card+(Aᶜ.erase z).card=32 := by
    by_cases zm : z∈A
    · rw [card_erase_of_mem zm,erase_eq_of_not_mem (fun m => mem_compl.mp m zm),card_compl,n]
      have hz := card_pos.mpr (show A.Nonempty from ⟨z,zm⟩)
      have le : A.card≤33 := n ▸ card_le_univ A
      omega
    · rw [erase_eq_of_not_mem zm,card_erase_of_mem (mem_compl.mpr zm),card_compl,n]
      have hz := card_pos.mpr (show Aᶜ.Nonempty from ⟨z,mem_compl.mpr zm⟩)
      rw [card_compl,n] at hz
      omega
  unfold bound at fail; rw [n,t] at fail; omega

theorem forced_split (n : Fintype.card V=33) (t : (types G).card=33) (fail : bound G<gamma G)
    {z a b : V} {A : Finset V} (h : Colors G z A) (ab : a≠b) (za : G.Adj z a) (zb : G.Adj z b) :
    (a∈A ↔ b∉A) := by
  have no (B : Finset V) (col : Colors G z B) (aB : a∈B) (bB : b∈B) : False := by
    let D := B.erase z
    have dom : TwoDominates G D := by
      intro v vm
      by_cases eq : v=z
      · subst v; exact PinnedColor34.two G ab za zb (mem_erase.mpr ⟨za.ne.symm,aB⟩) (mem_erase.mpr ⟨zb.ne.symm,bB⟩)
      have out : v∉B := fun m => vm (mem_erase.mpr ⟨eq,m⟩)
      have good := col v eq
      rwa [opp_right out] at good
    have size := (balanced G n t fail col).1
    have cap : gamma G≤D.card := Nat.sInf_le ⟨D,dom,rfl⟩
    change gamma G≤(B.erase z).card at cap
    have := (balanced G n t fail col).2.2
    omega
  by_cases am : a∈A <;> by_cases bm : b∈A
  · exact (no A h am bm).elim
  · simp [am,bm]
  · simp [am,bm]
  · exact (no Aᶜ (complement G h) (mem_compl.mpr am) (mem_compl.mpr bm)).elim

end Graffiti384b.PositiveCore33
#print axioms Graffiti384b.PositiveCore33.color_exists
#print axioms Graffiti384b.PositiveCore33.balanced
#print axioms Graffiti384b.PositiveCore33.forced_split
