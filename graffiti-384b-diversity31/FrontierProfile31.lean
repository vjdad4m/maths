import FrontierSample31

namespace Graffiti384b.Frontier31
open Finset SimpleGraph
open private Prune.outside_zero from Prune384b
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem coverage : types G⊆insert 0 ((nonleaves G).image (trianglesAt G)) := by
  intro s sm
  obtain ⟨v,_,rfl⟩ := mem_image.mp sm
  by_cases m : v∈nonleaves G
  · exact mem_insert_of_mem (mem_image_of_mem _ m)
  · exact mem_insert.mpr (Or.inl (Prune.outside_zero G m))

theorem enough (t : (types G).card=31) : 30≤(nonleaves G).card := by
  have c := (card_le_card (coverage G)).trans (card_insert_le ..)
  have im := card_image_le (s:=nonleaves G) (f:=trianglesAt G)
  omega

/-- A density violation can occur only at degree at least four. -/
private theorem small (v : V) (dv : G.degree v<4) : trianglesAt G v≤RankTable.cap (G.degree v) 3 := by
  have h := Repair.triangles_le_choose G v
  have eq : (G.degree v).choose 2=RankTable.cap (G.degree v) 3 := by
    exact (show ∀ d : Fin 4,d.val.choose 2=RankTable.cap d.val 3 by decide) ⟨_,dv⟩
  exact h.trans_eq eq

/-- At 31 or more nonleaves every failure has a center of degree four
through eight exceeding its tripartite Turán triangle bound. -/
theorem dense_center (t : (types G).card=31) (q : 31≤(nonleaves G).card) (bad : bound G<gamma G) :
    ∃ v,4≤G.degree v ∧ G.degree v≤8 ∧ RankTable.cap (G.degree v) 3<trianglesAt G v := by
  classical
  by_contra! no
  apply (not_lt_of_ge (sampled G (flag:=0) (Or.inl rfl) t q ?_ (by intro h; contradiction))) bad
  intro v vd
  by_cases d : 4≤G.degree v
  · exact no v d vd
  · exact small G v (by omega)

theorem free_cap (free : G.CliqueFree 5) (v : V) (d : G.degree v≤9) :
    trianglesAt G v≤RankTable.cap (G.degree v) 3 := by
  have c := RankTable.cap_table ⟨G.degree v,by omega⟩ ⟨3,by decide⟩ (by decide)
  exact (RankTuran.local_turan G 3 (by decide) free v).trans_eq c

/-- The obstruction under the local triangle cap needs specific degrees and triangle counts on
the original graph, including graphs with arbitrarily many leaves. -/
theorem profile (t : (types G).card=31) (cap : ∀ v,G.degree v≤9 → trianglesAt G v≤RankTable.cap (G.degree v) 3) (bad : bound G<gamma G) :
    (nonleaves G).card=30 ∧ (∃ u,G.degree u=3 ∧ trianglesAt G u=2) ∧
      ∃ x,G.degree x=4 ∧ trianglesAt G x=5 := by
  classical
  have lo := enough G t
  refine ⟨?_,?_,?_⟩
  · by_contra! ne
    obtain ⟨v,_,vd,h⟩ := dense_center G t (by omega) bad
    exact (not_lt_of_ge (cap v (by omega))) h
  · by_contra! no
    apply (not_lt_of_ge (sampled G (flag:=3) (Or.inr (Or.inl rfl)) t lo ?_ ?_)) bad
    · exact fun v vd => cap v vd
    · exact fun _ v d => no v d
  · by_contra! no
    apply (not_lt_of_ge (sampled G (flag:=4) (Or.inr (Or.inr rfl)) t lo ?_ ?_)) bad
    · exact fun v vd => cap v vd
    · exact fun _ v d => no v d

/-- All nonleaves realize distinct positive counts at the extremal quota. -/
theorem positive_types (t : (types G).card=31) (q : (nonleaves G).card=30) :
    Set.InjOn (trianglesAt G) (nonleaves G : Set V) ∧ ∀ v∈nonleaves G,0<trianglesAt G v := by
  classical
  let I := (nonleaves G).image (trianglesAt G)
  have cap : (types G).card≤(insert 0 I).card := card_le_card (coverage G)
  have ub : I.card≤(nonleaves G).card := card_image_le
  have step := card_insert_le 0 I
  have eq : I.card=(nonleaves G).card := by omega
  refine ⟨card_image_iff.mp eq,?_⟩
  intro v vm; by_contra! zero
  have m : 0∈I := (show trianglesAt G v=0 by omega) ▸ mem_image_of_mem (trianglesAt G) vm
  rw [insert_eq_of_mem m] at cap; omega

/-- A failure satisfying the local triangle cap reduces to an induced 31-vertex failure
where all triangle counts are distinct. -/
theorem induced (hc : G.Connected) (hn : 2<Fintype.card V) (t : (types G).card=31)
    (cap : ∀ v,G.degree v≤9 → trianglesAt G v≤RankTable.cap (G.degree v) 3) (bad : bound G<gamma G) :
    ∃ S : Finset V,S.card=31 ∧ (G.induce (S:Set V)).Connected ∧ types (G.induce (S:Set V))=types G ∧
      bound (G.induce (S:Set V))<gamma (G.induce (S:Set V)) := by
  obtain ⟨q,_,_⟩ := profile G t cap bad
  obtain ⟨S,_,sizeBound,_,conn,same,fail⟩ := Prune.prune_failure G hc hn bad
  have lower : (types (G.induce (S:Set V))).card≤S.card := by
    simpa [types] using (card_image_le (s:=(univ:Finset S)) (f:=trianglesAt (G.induce (S:Set V))))
  rw [same,t] at lower
  exact ⟨S,by omega,conn,same,fail⟩

end Graffiti384b.Frontier31
#print axioms Graffiti384b.Frontier31.enough
#print axioms Graffiti384b.Frontier31.dense_center
#print axioms Graffiti384b.Frontier31.profile
#print axioms Graffiti384b.Frontier31.positive_types
#print axioms Graffiti384b.Frontier31.induced
