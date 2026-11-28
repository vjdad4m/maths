import AdamEdgeIdentity189

namespace Graffiti189.AdamEdge
open Finset SimpleGraph SimpleGraph.Walk
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def Bad (G : SimpleGraph V) (Y : Finset V) (a b p : V) : Finset V := by
  classical
  exact (Remote G Y a p).filter (fun w => G.dist a w = G.dist b w + 2 ∧ G.dist b w % 2 = 1)

theorem remote_sdiff_even_eq_bad (hc : G.Connected) {a b x p : V}
    (dab : G.dist a b=3) (near : G.dist b x=2)
    (Y : Finset V)
    (xcross : ∀ w∈Y,G.dist x w = min (1 + G.dist a w) (G.dist b x + G.dist b w)) :
    Remote G Y a p \ E G x = Bad G Y a b p := by
  classical
  ext w
  constructor
  · intro h
    obtain ⟨wr,no⟩ := mem_sdiff.mp h
    have r := mem_filter.mp wr
    have c := xcross w r.1
    have t := hc.dist_triangle (u:=a) (v:=b) (w:=w)
    rw [mem_E] at no
    rw [near,Nat.min_def] at c
    refine mem_filter.mpr ⟨wr,?_⟩
    have odd := r.2.2.1
    split at c <;> omega
  · intro h
    obtain ⟨wr,e,odd⟩ := mem_filter.mp h
    have c := xcross w (mem_filter.mp wr).1
    rw [near,Nat.min_def] at c
    refine mem_sdiff.mpr ⟨wr,?_⟩
    rw [mem_E]
    split at c <;> omega

theorem near_edge_identity_of_cut (hc : G.Connected) {a b x p : V}
    (ap : G.Adj a p) (ax : G.Adj a x) (dab : G.dist a b=3)
    (X Y : Finset V) (xX : x∈X) (pY : p∈Y) (bX : b∉X) (bY : b∉Y)
    (dis : Disjoint X Y) (cover : ∀ w : V,w=a ∨ w=b ∨ w∈X ∨ w∈Y)
    (noEdge : ∀ u∈X,∀ v∈Y,¬G.Adj u v) (near : G.dist b x=2) :
    Fintype.card V + 3 + (E G a∩E G p).card + (Extra G Y a b x p).card + (Missing G Y a p).card =
      (E G a).card + (E G p).card + (E G x).card +
      (XOdd G X a b p).card + (BFlag b (G.dist b p=3)).card + (Bad G Y a b p).card := by
  classical
  obtain ⟨_,xc⟩ := port_cross_pair hc ap ax X Y xX pY dis cover noEdge
  have h := edge_identity_of_cut hc ap ax dab X Y xX pY bX bY dis cover noEdge
  rw [remote_sdiff_even_eq_bad hc dab near Y xc,card_flag] at h
  have ev : G.dist x b % 2 = 0 := by rw [G.dist_comm (u:=x) (v:=b),near]
  simp only [ev,if_true] at h
  omega

private lemma local_lengths {x y : V} (p : G.Walk x y) (n : ℕ) (hn : n ≤ p.length) :
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


private theorem shortest_middle {u v : V} (hc : G.Connected) (i : ℕ) (hi : i≤G.dist u v) :
    ∃ w, G.dist u w=i ∧ G.dist w v=G.dist u v-i := by
  obtain ⟨q,hq⟩ := hc.exists_walk_length_eq_dist u v
  refine ⟨q.getVert i,?_⟩
  have h₁ := G.dist_le (q.take i)
  have h₂ := G.dist_le (q.drop i)
  have h₃ := hc.dist_triangle (u:=u) (v:=q.getVert i) (w:=v)
  obtain ⟨lt,ld⟩ := local_lengths q i (by rwa [hq])
  rw [lt] at h₁
  rw [ld,hq] at h₂
  omega

theorem bad_witness (hc : G.Connected) {a b p : V} (ap : G.Adj a p) (dab : G.dist a b=3)
    (Y : Finset V)
    (closed : ∀ u∈Y,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈Y)
    (bad : (Bad G Y a b p).Nonempty) :
    (E G a∩E G p).Nonempty ∨ (Missing G Y a p).Nonempty := by
  classical
  obtain ⟨w,wb⟩ := bad
  obtain ⟨wr,aw,odd⟩ := mem_filter.mp wb
  obtain ⟨wy,eq,_,far⟩ := mem_filter.mp wr
  obtain ⟨s,as₂,sw⟩ := shortest_middle hc 2 (show 2≤G.dist a w by omega)
  have ps_hi := hc.dist_triangle (u:=p) (v:=a) (w:=s)
  have ps_lo := hc.dist_triangle (u:=p) (v:=s) (w:=w)
  have ap1 := SimpleGraph.dist_eq_one_iff_adj.mpr ap
  rw [G.dist_comm (u:=p) (v:=a),ap1,as₂] at ps_hi
  by_cases ps : G.dist p s=2
  · exact .inl ⟨s,mem_inter.mpr ⟨(mem_E G).mpr (by rw [as₂]),(mem_E G).mpr (by rw [ps])⟩⟩
  have ps3 : G.dist p s=3 := by omega
  obtain ⟨t,at₁,ts₁⟩ := shortest_middle hc 1 (show 1≤G.dist a s by omega)
  have ats : G.Adj a t := SimpleGraph.dist_eq_one_iff_adj.mp at₁
  have ts : G.Adj t s := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
  have tW := hc.dist_triangle (u:=t) (v:=s) (w:=w)
  have pT : ¬G.Adj p t := by
    intro h
    have d := hc.dist_triangle (u:=p) (v:=t) (w:=s)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr h,SimpleGraph.dist_eq_one_iff_adj.mpr ts] at d
    omega
  have tp : t≠p := by
    intro e
    have nn := SimpleGraph.dist_eq_one_iff_adj.mpr ts
    rw [e,ps3] at nn
    omega
  have tY : t∈Y := by
    by_contra nt
    have metric := cross_of_closed hc Y wy nt closed
    rw [G.dist_comm (u:=w) (v:=a),
      G.dist_comm (u:=w) (v:=t), G.dist_comm (u:=w) (v:=b), at₁] at metric
    have bt := hc.dist_triangle (u:=a) (v:=t) (w:=b)
    rw [dab,at₁,G.dist_comm (u:=t) (v:=b)] at bt
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ts] at tW
    simp only [Nat.min_def] at metric
    split at metric <;> omega
  exact .inr ⟨t,mem_filter.mpr ⟨mem_filter.mpr ⟨tY,ats⟩,tp,pT⟩⟩


theorem near_extra_witness (hc : G.Connected) {a b x p : V} (X Y : Finset V)
    (xX : x∈X) (bX : b∉X) (dis : Disjoint X Y)
    (joins : ∀ u∈X,∀ v∈X,∃ q : G.Walk u v,∀ t∈q.support,t∈X)
    (notUniversal : ∃ z∈X,z≠x ∧ ¬G.Adj x z) :
    (Extra G Y a b x p).Nonempty := by
  classical
  by_contra! he
  have all (u : V) (hu : u∈X) (xu : u≠x) (n : ¬G.Adj x u)
      (v : V) (xv : G.Adj x v) (vu : G.Adj v u) : False := by
    have d := hc.dist_triangle (u:=x) (v:=v) (w:=u)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr xv,SimpleGraph.dist_eq_one_iff_adj.mpr vu] at d
    have lo := hc.one_lt_dist_of_ne_of_not_adj xu.symm n
    have eq : G.dist x u=2 := by omega
    have eu : u∈E G x := (mem_E G).mpr (by rw [eq])
    have nuY : u∉Y := fun uy=>disjoint_left.mp dis hu uy
    have nt : u∉Base G Y a b x := by
      intro h
      rcases mem_insert.mp h with e|h
      · exact xu e
      rcases mem_union.mp h with h|h
      · exact bX ((mem_flag.mp h).1 ▸ hu)
      · exact nuY (mem_filter.mp h).1
    have nr : u∉Remote G Y a p := fun h=>nuY (mem_filter.mp h).1
    exact he ⟨u,mem_sdiff.mpr ⟨eu,fun m=>(mem_union.mp m).elim nt nr⟩⟩
  have any {u v : V} (q : G.Walk u v) (inside : ∀ t∈q.support,t∈X) (start : u=x ∨ G.Adj x u) :
      v=x ∨ G.Adj x v := by
    induction q with
    | nil => exact start
    | @cons u v w uv q ih =>
      apply ih (fun t tm=>inside t (by simp [tm]))
      rcases start with rfl|xu
      · exact .inr uv
      · by_cases e : v=x
        · exact .inl e
        · by_cases h : G.Adj x v
          · exact .inr h
          · exact (all v (inside v (by simp)) e h u xu uv).elim
  obtain ⟨z,zX,ne,n⟩ := notUniversal
  obtain ⟨q,inside⟩ := joins x xX z zX
  exact (any q inside (.inl rfl)).elim ne n

theorem near_edge_bound_with_gain (hc : G.Connected) {a b x p : V}
    (ap : G.Adj a p) (ax : G.Adj a x) (dab : G.dist a b=3)
    (X Y : Finset V) (xX : x∈X) (pY : p∈Y) (bX : b∉X) (bY : b∉Y)
    (dis : Disjoint X Y) (cover : ∀ w : V,w=a ∨ w=b ∨ w∈X ∨ w∈Y)
    (noEdge : ∀ u∈X,∀ v∈Y,¬G.Adj u v) (near : G.dist b x=2)
    (joins : ∀ u∈X,∀ v∈X,∃ q : G.Walk u v,∀ t∈q.support,t∈X)
    (d : ℕ) (ba : (E G a).card≤d+1) (bp : (E G p).card≤d+1) (bx : (E G x).card≤d+1) :
    Fintype.card V + (BFlag x (∃ z∈X,z≠x ∧ ¬G.Adj x z)).card +
        (BFlag p (Bad G Y a b p).Nonempty).card ≤
      3*d + (BFlag b (G.dist b p=3)).card +
      (XOdd G X a b p).card + (Bad G Y a b p).card := by
  classical
  have identity := near_edge_identity_of_cut hc ap ax dab X Y xX pY bX bY dis cover noEdge near
  have closed : ∀ u∈Y,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈Y := by
    intro u uy v e
    rcases cover v with rfl|rfl|vx|vy
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact (noEdge v vx u uy e.symm).elim
    · exact .inr (.inr vy)
  have gX : (BFlag x (∃ z∈X,z≠x ∧ ¬G.Adj x z)).card ≤ (Extra G Y a b x p).card := by
    rw [card_flag]
    split
    · rename_i yes
      exact card_pos.mpr (near_extra_witness hc X Y xX bX dis joins yes)
    · exact Nat.zero_le _
  have gP : (BFlag p (Bad G Y a b p).Nonempty).card ≤
      (E G a∩E G p).card + (Missing G Y a p).card := by
    rw [card_flag]
    split
    · rename_i yes
      rcases bad_witness hc ap dab Y closed yes with h|h
      · have := card_pos.mpr h
        omega
      · have := card_pos.mpr h
        omega
    · exact Nat.zero_le _
  omega

#print axioms near_edge_bound_with_gain
#print axioms near_edge_identity_of_cut
#print axioms bad_witness
end Graffiti189.AdamEdge
