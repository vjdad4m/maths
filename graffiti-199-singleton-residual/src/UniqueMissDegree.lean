import InternalOmission
import UniqueMissSwap

open private forced_next from UniqueMissSwap
open private six_le_treeNumber_of_five_independent_neighbors from CubicEdgeCuts
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {X : Set V} {z r a b x : V}

/-- If a port misses at most one ordinary vertex on this shore, that vertex
is cubic and shares the other two ports with the singleton. -/
theorem SingletonCut.unique_miss_degree_and_contacts (F : SingletonCut G X z r a b)
    (no : ¬ Traceable G) (P : PathOn G {v | v ≠ z})
    (almost : ∀ w ∈ X, ¬ G.Adj r w → w = x) :
    x ∈ X ∧ ¬ G.Adj r x ∧ G.Adj x a ∧ G.Adj x b ∧ G.degree x = 3 := by
  classical
  obtain ⟨w,mem,off⟩ := F.misses_flank no P (Finset.mem_insert_self r _)
  have wX := F.flanks_in_shore no P w mem
  obtain rfl := almost w wX off
  have wx : w ≠ z := fun e => F.zX (e ▸ wX)
  have wz : ¬ G.Adj w z := fun e => F.offX w ((F.cut.2 w).mp e.symm) wX
  have lo := degree_of_small_deletion_preconnected (G := G) (by have := F.conn.1; omega : 4 ≤ Fintype.card V)
    (fun D hD => (F.conn.2 D hD).preconnected) w
  have many : 1 < (G.neighborFinset w).card := by rw [G.card_neighborFinset_eq_degree]; omega
  obtain ⟨u,um,v,vm,uv⟩ := Finset.one_lt_card.mp many
  have wu := (G.mem_neighborFinset w u).mp um
  have wv := (G.mem_neighborFinset w v).mp vm
  obtain ⟨Q,L,p,q,R,split⟩ := exists_internal_path P wx
    (show u ≠ z from fun e => wz (e ▸ wu)) (show v ≠ z from fun e => wz (e ▸ wv)) wu wv uv
  have wq : G.Adj w q := List.chain'_iff_forall_rel_of_append_cons_cons.mp Q.chain
    (show Q.vertices = (L ++ [p]) ++ w :: q :: R by simpa using split)
  have pw : G.Adj p w := List.chain'_iff_forall_rel_of_append_cons_cons.mp Q.chain split
  have qPort := (F.cut.2 q).mp (forced_next F no almost Q (L := L ++ [p]) (R := R) (by simpa using split))
  let rev : PathOn G {v | v ≠ z} := ⟨Q.vertices.reverse,by simpa using Q.nonempty,
    List.chain'_reverse.mpr (Q.chain.imp (fun _ _ e => e.symm)), List.nodup_reverse.mpr Q.nodup,
    fun v => by simpa using Q.covers v⟩
  have pPort := (F.cut.2 p).mp (forced_next F no almost rev (L := R.reverse ++ [q]) (R := L.reverse)
    (by change Q.vertices.reverse = _; simp [split,List.reverse_append,List.reverse_cons,List.append_assoc]))
  have p0 : p ≠ r := fun e => off (e ▸ pw)
  have q0 : q ≠ r := fun e => off (e ▸ wq.symm)
  have nd : (p :: w :: q :: R).Nodup := (List.nodup_append.mp (split ▸ Q.nodup)).2.1
  have pq : p ≠ q := fun e => (List.nodup_cons.mp nd).1 (by simp [e])
  simp only [Finset.mem_insert,Finset.mem_singleton] at pPort qPort
  obtain ⟨wa,wb⟩ : G.Adj w a ∧ G.Adj w b := by
    rcases pPort.resolve_left p0 with hp|hp <;> rcases qPort.resolve_left q0 with hq|hq
    · exact (pq (hp.trans hq.symm)).elim
    · exact ⟨hp ▸ pw.symm,hq ▸ wq⟩
    · exact ⟨hq ▸ wq,hp ▸ pw.symm⟩
    · exact (pq (hp.trans hq.symm)).elim
  refine ⟨wX,off,wa,wb,?_⟩
  obtain ⟨S,_⟩ := F.exchange_unique_miss no almost P
  have count := S.terminalQuartet_card no
  have on (t : V) (ht : t ∈ S.terminalQuartet) (tr : t ≠ r) : G.Adj r t := by
    rcases F.cover t with tX|tz|rt|ta|tb
    · by_contra miss
      exact S.omitted_off_terminalQuartet ((almost t tX miss) ▸ ht)
    · exact tz ▸ ((F.cut.2 r).mpr (by simp)).symm
    · contradiction
    · exact (S.no_edge_from_omitted_to_terminalQuartet no t ht (ta ▸ wa)).elim
    · exact (S.no_edge_from_omitted_to_terminalQuartet no t ht (tb ▸ wb)).elim
  have rOff : r ∉ S.terminalQuartet := by
    intro rr
    obtain ⟨v,vm,vr⟩ := Finset.exists_ne_of_one_lt_card (by omega : 1 < S.terminalQuartet.card) r
    exact S.terminalQuartet_independent no r rr v vm (on v vm vr)
  by_contra bad
  have five : 5 ≤ S.terminalQuartet.card := by omega
  have six := six_le_treeNumber_of_five_independent_neighbors S.terminalQuartet r five
    (fun t ht => on t ht (fun e => rOff (e ▸ ht))) (S.terminalQuartet_independent no)
  exact (Nat.not_succ_le_self 5) (six.trans F.budget)

#print axioms SingletonCut.unique_miss_degree_and_contacts
end Graffiti199Depleted.Catalogue.Incomplete
