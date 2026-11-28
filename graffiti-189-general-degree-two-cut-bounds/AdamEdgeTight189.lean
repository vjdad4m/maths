import AdamNearEdge189
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Graffiti189.AdamEdge
open Finset SimpleGraph SimpleGraph.Walk
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem near_tight_slacks (hc : G.Connected) {a b x p : V}
    (ap : G.Adj a p) (ax : G.Adj a x) (dab : G.dist a b=3)
    (X Y : Finset V) (xX : x∈X) (pY : p∈Y) (bX : b∉X) (bY : b∉Y)
    (dis : Disjoint X Y) (cover : ∀ w : V,w=a ∨ w=b ∨ w∈X ∨ w∈Y)
    (noEdge : ∀ u∈X,∀ v∈Y,¬G.Adj u v) (near : G.dist b x=2)
    (p3 : G.dist b p=3) (noOdd : XOdd G X a b p = ∅) (noBad : Bad G Y a b p = ∅)
    (d : ℕ) (ba : (E G a).card≤d+1) (bp : (E G p).card≤d+1) (bx : (E G x).card≤d+1)
    (large : 3*d < Fintype.card V) :
    Fintype.card V=3*d+1 ∧ (E G a∩E G p)=∅ ∧ Extra G Y a b x p=∅ ∧
      Missing G Y a p=∅ ∧ (E G a).card=d+1 ∧ (E G p).card=d+1 ∧ (E G x).card=d+1 := by
  classical
  have h := near_edge_identity_of_cut hc ap ax dab X Y xX pY bX bY dis cover noEdge near
  rw [noOdd,noBad,card_flag] at h
  simp only [p3,if_true,card_empty] at h
  exact ⟨by omega,card_eq_zero.mp (by omega),card_eq_zero.mp (by omega),card_eq_zero.mp (by omega),
    by omega,by omega,by omega⟩

theorem near_tight_universal (hc : G.Connected) {a b x p : V}
    (X Y : Finset V) (xX : x∈X) (bX : b∉X) (dis : Disjoint X Y)
    (joins : ∀ u∈X,∀ v∈X,∃ q : G.Walk u v,∀ t∈q.support,t∈X)
    (noExtra : Extra G Y a b x p=∅) :
    ∀ w∈X,w≠x → G.Adj x w := by
  classical
  intro w hw ne
  by_contra hn
  have e := near_extra_witness hc (a:=a) (p:=p) X Y xX bX dis joins ⟨w,hw,ne,hn⟩
  rw [noExtra] at e
  simp at e

private lemma tight_lengths {x y : V} (p : G.Walk x y) (n : ℕ) (hn : n ≤ p.length) :
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


private theorem tight_middle {u v : V} (hc : G.Connected) (i : ℕ) (hi : i≤G.dist u v) :
    ∃ w, G.dist u w=i ∧ G.dist w v=G.dist u v-i := by
  obtain ⟨q,hq⟩ := hc.exists_walk_length_eq_dist u v
  refine ⟨q.getVert i,?_⟩
  have h₁ := G.dist_le (q.take i)
  have h₂ := G.dist_le (q.drop i)
  have h₃ := hc.dist_triangle (u:=u) (v:=q.getVert i) (w:=v)
  obtain ⟨lt,ld⟩ := tight_lengths q i (by rwa [hq])
  rw [lt] at h₁
  rw [ld,hq] at h₂
  omega



theorem tight_shore_even_profile (hc : G.Connected) {a b x p : V}
    (ax : G.Adj a x) (dab : G.dist a b=3)
    (X Y : Finset V) (xX : x∈X) (bX : b∉X) (bY : b∉Y) (dis : Disjoint X Y)
    (near : G.dist b x=2) (xcross : ∀ w∈Y,G.dist x w = min (1 + G.dist a w) (G.dist b x + G.dist b w))
    (noBad : Bad G Y a b p=∅) (noExtra : Extra G Y a b x p=∅) (d : ℕ)
    (full : (E G x).card=d+1) :
    ((Ports G Y a ∪ Remote G Y a p).card+1=d) ∧
      (∀ w∈Y,w∈E G x ↔ w∈Ports G Y a ∪ Remote G Y a p) := by
  classical
  let B := Ports G Y a ∪ Remote G Y a p
  have subY : B⊆Y := union_subset (filter_subset _ _) (filter_subset _ _)
  have eq : E G x = insert x (insert b B) := by
    ext w
    constructor
    · intro ew
      have h : w∈Base G Y a b x ∪ Remote G Y a p := by
        by_contra no
        have e : w∈Extra G Y a b x p := mem_sdiff.mpr ⟨ew,no⟩
        simp [noExtra] at e
      rcases mem_union.mp h with base|r
      · rcases mem_insert.mp base with hx|hp
        · exact mem_insert.mpr (.inl hx)
        rcases mem_union.mp hp with bf|port
        · exact mem_insert.mpr (.inr (mem_insert.mpr (.inl (mem_flag.mp bf).1)))
        · exact mem_insert.mpr (.inr (mem_insert.mpr (.inr (mem_union.mpr (.inl port)))))
      · exact mem_insert.mpr (.inr (mem_insert.mpr (.inr (mem_union.mpr (.inr r)))))
    · intro wmem
      rcases mem_insert.mp wmem with rfl|h
      · simp [SimpleGraph.dist_self]
      rcases mem_insert.mp h with hb|h
      · subst w
        rw [mem_E,G.dist_comm (u:=x) (v:=b),near]
      rcases mem_union.mp h with port|r
      · obtain ⟨wy,aw⟩ := mem_filter.mp port
        have q := xcross w wy
        rw [near,SimpleGraph.dist_eq_one_iff_adj.mpr aw,Nat.min_def] at q
        rw [mem_E]
        split at q <;> omega
      · have e := remote_sdiff_even_eq_bad hc (p:=p) dab near Y xcross
        by_contra hn
        have m : w∈Remote G Y a p \ E G x := mem_sdiff.mpr ⟨r,hn⟩
        simp [e,noBad] at m
  have bn : b∉B := fun h=>bY (subY h)
  have xn : x∉insert b B := by
    intro h
    rcases mem_insert.mp h with xb|m
    · exact bX (xb ▸ xX)
    · exact disjoint_left.mp dis xX (subY m)
  constructor
  · rw [eq,card_insert_of_not_mem xn,card_insert_of_not_mem bn] at full
    change B.card+1=d
    omega
  intro w wy
  rw [eq,mem_insert,mem_insert]
  have wx : w≠x := fun e=>disjoint_left.mp dis xX (e ▸ wy)
  have wb : w≠b := fun e=>bY (e ▸ wy)
  simp [wx,wb,B]

theorem tight_shore_alpha_two (hc : G.Connected) {a b p : V} (ap : G.Adj a p)
    (dab : G.dist a b=3) (Y : Finset V)
    (closed : ∀ u∈Y,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈Y)
    (noEE : E G a ∩ E G p=∅) (noMiss : Missing G Y a p=∅)
    {w : V} (wy : w∈Y) (far : 2≤G.dist a w) (below : G.dist a w<G.dist b w+3) :
    G.dist p w=G.dist a w-1 := by
  classical
  obtain ⟨s,as₂,sw⟩ := tight_middle hc 2 far
  obtain ⟨t,at₁,ts₁⟩ := tight_middle hc 1 (show 1≤G.dist a s by omega)
  have ts : G.Adj t s := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  have atEdge : G.Adj a t := SimpleGraph.dist_eq_one_iff_adj.mp at₁
  have ap1 := SimpleGraph.dist_eq_one_iff_adj.mpr ap
  have tW := hc.dist_triangle (u:=t) (v:=s) (w:=w)
  have tY : t∈Y := by
    by_contra nt
    have metric := cross_of_closed hc Y wy nt closed
    rw [G.dist_comm (u:=w) (v:=a),G.dist_comm (u:=w) (v:=t),
      G.dist_comm (u:=w) (v:=b),at₁] at metric
    have bt := hc.dist_triangle (u:=a) (v:=t) (w:=b)
    rw [dab,at₁,G.dist_comm (u:=t) (v:=b)] at bt
    simp only [Nat.min_def] at metric
    split at metric <;> omega
  have pT : t=p ∨ G.Adj p t := by
    by_contra! h
    have m : t∈Missing G Y a p := mem_filter.mpr ⟨mem_filter.mpr ⟨tY,atEdge⟩,h.1,h.2⟩
    simp [noMiss] at m
  have ps : G.Adj p s := by
    rcases pT with rfl|pt
    · exact ts
    by_contra no
    have ne : p≠s := by
      intro h
      rw [h] at ap1
      omega
    have d₁ := hc.one_lt_dist_of_ne_of_not_adj ne no
    have d₂ := hc.dist_triangle (u:=p) (v:=t) (w:=s)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr pt,SimpleGraph.dist_eq_one_iff_adj.mpr ts] at d₂
    have d : G.dist p s=2 := by omega
    have m : s∈E G a∩E G p := mem_inter.mpr ⟨(mem_E G).mpr (by rw [as₂]),(mem_E G).mpr (by rw [d])⟩
    simp [noEE] at m
  have l := hc.dist_triangle (u:=a) (v:=p) (w:=w)
  have r := hc.dist_triangle (u:=p) (v:=s) (w:=w)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr ps] at r
  omega

theorem tight_remote_gap (hc : G.Connected) {a b p : V} (ap : G.Adj a p)
    (dab : G.dist a b=3) (Y : Finset V)
    (closed : ∀ u∈Y,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈Y)
    (noEE : E G a ∩ E G p=∅) (noMiss : Missing G Y a p=∅) :
    ∀ w∈Remote G Y a p,G.dist a w=G.dist b w+3 ∧ G.dist b w % 2=0 := by
  intro w wm
  obtain ⟨wy,e,odd,big⟩ := mem_filter.mp wm
  have up := hc.dist_triangle (u:=a) (v:=b) (w:=w)
  by_cases lt : G.dist a w<G.dist b w+3
  · have m := tight_shore_alpha_two hc ap dab Y closed noEE noMiss wy (by omega) lt
    omega
  omega


noncomputable def Mid (G : SimpleGraph V) (Y : Finset V) (a b : V) : Finset V := by
  classical exact Y.filter (fun w=>G.dist a w=G.dist b w ∧ G.dist a w % 2=0)

noncomputable def Two (G : SimpleGraph V) (Y : Finset V) (a : V) : Finset V := by
  classical exact Y.filter (fun w=>G.dist a w=2)

theorem two_in_mid (hc : G.Connected) {a b p z q : V} (ap : G.Adj a p)
    (dab : G.dist a b=3) (Y : Finset V) (bY : b∉Y)
    (closed : ∀ u∈Y,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈Y)
    (p3 : G.dist b p=3) (noEE : E G a∩E G p=∅) (noMiss : Missing G Y a p=∅)
    (z2 : G.dist a z=2)
    (zcross : ∀ w∈Y,G.dist z w=min (1+G.dist b w) (G.dist a z+G.dist a w))
    (zprof : ∀ w∈Y,w∈E G z ↔ w∈Ports G Y b∪Remote G Y b q)
    (qgap : ∀ w∈Remote G Y b q,G.dist b w=G.dist a w+3 ∧ G.dist a w%2=0) :
    Two G Y a ⊆ Mid G Y a b := by
  classical
  intro w wm
  obtain ⟨wy,aw⟩ := mem_filter.mp wm
  have pos := (dist_ne_zero_iff_ne_and_reachable.mpr ⟨(show b≠w from fun h=>bY (h.symm ▸ wy)),hc b w⟩)
  have pw := tight_shore_alpha_two hc ap dab Y closed noEE noMiss wy (by omega) (by omega)
  have bw_hi := hc.dist_triangle (u:=b) (v:=p) (w:=w)
  have bw_lo := hc.dist_triangle (u:=b) (v:=w) (w:=p)
  rw [G.dist_comm (u:=w) (v:=p)] at bw_lo
  have lo : 2≤G.dist b w := by omega
  have hi : G.dist b w≤4 := by omega
  have eq : G.dist b w=2 := by
    by_contra ne
    have zw := zcross w wy
    have z4 : G.dist z w=4 := by rw [zw,z2,aw,min_eq_right]; omega
    have inE : w∈E G z := (mem_E G).mpr (by rw [z4])
    rcases mem_union.mp ((zprof w wy).mp inE) with port|r
    · have bb := SimpleGraph.dist_eq_one_iff_adj.mpr (mem_filter.mp port).2
      omega
    · have bb := (qgap w r).1
      omega
  exact mem_filter.mpr ⟨wy,by omega,by omega⟩

theorem degree_port_cap (hc : G.Connected) {a b p : V} (ap : G.Adj a p)
    (Y : Finset V) (pY : p∈Y)
    (closed : ∀ u∈Y,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈Y)
    (p3 : G.dist b p=3) [DecidableRel G.Adj] :
    G.degree p ≤ (Ports G Y a).card+(Two G Y a).card := by
  let P := Ports G Y a
  let T := Two G Y a
  have pP : p∈P := by simpa [P,Ports] using And.intro pY ap
  have sub : G.neighborFinset p ⊆ insert a (P.erase p ∪ T) := by
    intro w wm
    have pw := (G.mem_neighborFinset p w).mp wm
    rcases closed p pY w pw with rfl|rfl|wy
    · exact mem_insert.mpr (.inl rfl)
    · have e := SimpleGraph.dist_eq_one_iff_adj.mpr pw.symm
      omega
    have aw := hc.dist_triangle (u:=a) (v:=p) (w:=w)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ap,SimpleGraph.dist_eq_one_iff_adj.mpr pw] at aw
    by_cases wa : w=a
    · exact mem_insert.mpr (.inl wa)
    have one := dist_ne_zero_iff_ne_and_reachable.mpr ⟨Ne.symm wa,hc a w⟩
    by_cases h : G.dist a w=1
    · exact mem_insert.mpr (.inr (mem_union.mpr (.inl (mem_erase.mpr
        ⟨pw.symm.ne,by simpa [P,Ports] using And.intro wy (SimpleGraph.dist_eq_one_iff_adj.mp h)⟩))))
    · exact mem_insert.mpr (.inr (mem_union.mpr (.inr (mem_filter.mpr ⟨wy,by omega⟩))))
  have s := card_le_card sub
  have i := card_insert_le a (P.erase p∪T)
  have u := card_union_le (P.erase p) T
  rw [card_erase_of_mem pP] at u
  rw [SimpleGraph.card_neighborFinset_eq_degree] at s
  have hp := card_pos.mpr (show P.Nonempty from ⟨p,pP⟩)
  change G.degree p ≤ P.card+T.card
  omega

#print axioms degree_port_cap
#print axioms two_in_mid
#print axioms tight_remote_gap
#print axioms tight_shore_even_profile
#print axioms near_tight_slacks
#print axioms near_tight_universal
end Graffiti189.AdamEdge
