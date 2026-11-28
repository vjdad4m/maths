import AdamEdgeTPartition189

namespace Graffiti189.AdamEdge
open Finset SimpleGraph
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem tight_far_even_low [DecidableRel G.Adj] (hc : G.Connected) {a b m : V}
    (dab : G.dist a b=3) (Y : Finset V)
    (closed : ∀ u∈Y,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈Y)
    (partition : Y=Ports G Y a ∪ Ports G Y b ∪ {m})
    (ta : Two G Y a ⊆ {m})
    (am : G.dist a m=2) (bm : G.dist b m=2)
    (d : ℕ) (ports : (Ports G Y b).card+1=d)
    {w : V} (wp : w∈Ports G Y b) (we : w∈E G a) :
    G.degree w < d := by
  have ⟨wy,bw⟩ : w∈Y ∧ G.Adj b w := by simpa [Ports] using wp
  have bw1 := SimpleGraph.dist_eq_one_iff_adj.mpr bw
  have aw := (mem_E G).mp we
  have nw : w≠m := by
    intro h
    rw [h,bm] at bw1
    omega
  have wa2 : G.dist a w≠2 := by
    intro e
    have h : w∈Two G Y a := by simp [Two,wy,e]
    exact nw (mem_singleton.mp (ta h))
  have wa0 : G.dist a w≠0 := dist_ne_zero_iff_ne_and_reachable.mpr
    ⟨by intro e; rw [←e,G.dist_comm (u:=b) (v:=a),dab] at bw1; omega, hc a w⟩
  have wa4 : 4≤G.dist a w := by omega
  have sub : G.neighborFinset w ⊆ insert b ((Ports G Y b).erase w) := by
    intro v vm
    have wv := (G.mem_neighborFinset w v).mp vm
    have av := hc.dist_triangle (u:=a) (v:=v) (w:=w)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr wv.symm] at av
    rcases closed w wy v wv with va|vb|vy
    · rw [va,SimpleGraph.dist_self] at av
      omega
    · exact mem_insert.mpr (.inl vb)
    rw [partition] at vy
    rcases mem_union.mp vy with portsV|mid
    · rcases mem_union.mp portsV with vpa|vpb
      · have e : G.Adj a v := (show v∈Y ∧ G.Adj a v by simpa [Ports] using vpa).2
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr e] at av
        omega
      · exact mem_insert.mpr (.inr (mem_erase.mpr ⟨wv.symm.ne,vpb⟩))
    rw [mem_singleton.mp mid,am] at av
    omega
  have lt := card_le_card sub
  have le := card_insert_le b ((Ports G Y b).erase w)
  have pos := card_pos.mpr (show (Ports G Y b).Nonempty from ⟨w,wp⟩)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at lt
  rw [card_erase_of_mem wp] at le
  omega

theorem high_count_complement [DecidableRel G.Adj] (d : ℕ)
    (degree : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v)
    (X : Finset V) (A B : Finset V)
    (asub : A⊆X) (bsub : B⊆X)
    (fewA : A.card≤2) (fewB : B.card≤2) (sz : X.card=d) (dl : 6≤d)
    (low : ∀ w∈X,w∉A → w∉B → G.degree w<d) : False := by
  have s : A∪B⊆X := union_subset asub bsub
  have k := card_union_le A B
  let C := X \ (A∪B)
  have c := card_sdiff_add_card_eq_card s
  have c₂ : 2≤C.card := by
    change C.card+(A∪B).card=X.card at c
    omega
  obtain ⟨u,um,v,vm,uv⟩ := one_lt_card.mp (show 1<C.card by omega)
  have l (w : V) (wm : w∈C) : G.degree w<d := by
    obtain ⟨wx,n⟩ := mem_sdiff.mp wm
    exact low w wx (fun aw=>n (mem_union.mpr (.inl aw))) (fun bw=>n (mem_union.mpr (.inr bw)))
  have deg := degree u v uv
  have lu := l u um
  have lv := l v vm
  omega


theorem near_ports_at_most_two [DecidableRel G.Adj] (hc : G.Connected) {a b m : V}
    (dab : G.dist a b=3) (X Y : Finset V)
    (cover : ∀ w : V,w=a ∨ w=b ∨ w∈X ∨ w∈Y)
    (closed : ∀ u∈Y,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈Y)
    (partition : Y=Ports G Y a ∪ Ports G Y b ∪ {m})
    (ta : Two G Y a ⊆ {m}) (am : G.dist a m=2) (bm : G.dist b m=2)
    (d : ℕ) (ports : (Ports G Y b).card+1=d) (sz : X.card=d)
    (full : (E G a).card=d+1)
    (degree : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v) :
    (Ports G X a).card≤2 := by
  let L := (Ports G Y b)∩E G a
  have lsmall : L.card≤1 := by
    by_contra! contra
    obtain ⟨u,hu,v,hv,hne⟩ := one_lt_card.mp contra
    have low {w : V} (wm : w∈L) : G.degree w<d :=
      tight_far_even_low hc dab Y closed partition ta am bm d ports (mem_inter.mp wm).1 (mem_inter.mp wm).2
    have du := low hu
    have dv := low hv
    have deg := degree u v hne
    omega
  let A := Ports G X a
  have sub : E G a⊆insert a (insert m ((X \ A) ∪ L)) := by
    intro w wm
    have ev := (mem_E G).mp wm
    rcases cover w with wa|wb|wx|wy
    · exact mem_insert.mpr (.inl wa)
    · rw [wb,dab] at ev
      omega
    · have wn : w∉A := by
        intro wat
        have one := SimpleGraph.dist_eq_one_iff_adj.mpr (show w∈X ∧ G.Adj a w by simpa [A,Ports] using wat).2
        omega
      exact mem_insert.mpr (.inr (mem_insert.mpr (.inr (mem_union.mpr (.inl (mem_sdiff.mpr ⟨wx,wn⟩))))))
    rw [partition] at wy
    rcases mem_union.mp wy with pp|mid
    · rcases mem_union.mp pp with pa|pb
      · have one := SimpleGraph.dist_eq_one_iff_adj.mpr (show w∈Y ∧ G.Adj a w by simpa [Ports] using pa).2
        omega
      · exact mem_insert.mpr (.inr (mem_insert.mpr (.inr (mem_union.mpr (.inr (mem_inter.mpr ⟨pb,wm⟩))))))
    · exact mem_insert.mpr (.inr (mem_insert.mpr (.inl (mem_singleton.mp mid))))
  have h := card_le_card sub
  have i := card_insert_le a (insert m ((X \ A) ∪ L))
  have j := card_insert_le m ((X \ A) ∪ L)
  have k := card_union_le (X \ A) L
  have s := card_sdiff_add_card_eq_card (show A⊆X from by intro w h; exact (show w∈X ∧ G.Adj a w by simpa [A,Ports] using h).1)
  change A.card≤2
  omega

theorem near_nonport_low [DecidableRel G.Adj] {a b w : V} (X : Finset V)
    (wx : w∈X) (na : w∉Ports G X a) (nb : w∉Ports G X b)
    (closed : ∀ u∈X,∀ v,G.Adj u v → v=a ∨ v=b ∨ v∈X) :
    G.degree w < X.card := by
  have sub : G.neighborFinset w⊆X.erase w := by
    intro v vm
    have wv := (G.mem_neighborFinset w v).mp vm
    rcases closed w wx v wv with va|vb|vx
    · exact (na (by simp [Ports,wx,show G.Adj a w from va ▸ wv.symm])).elim
    · exact (nb (by simp [Ports,wx,show G.Adj b w from vb ▸ wv.symm])).elim
    exact mem_erase.mpr ⟨wv.symm.ne,vx⟩
  have h := card_le_card sub
  rw [SimpleGraph.card_neighborFinset_eq_degree,card_erase_of_mem wx] at h
  have pos := card_pos.mpr (show X.Nonempty from ⟨w,wx⟩)
  omega

#print axioms near_ports_at_most_two
#print axioms near_nonport_low
#print axioms tight_far_even_low
#print axioms high_count_complement
end Graffiti189.AdamEdge
