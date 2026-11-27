import FullObstruction33

namespace Graffiti384b.ForcedCubics
open Finset SimpleGraph HighEar
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Four vertices inducing five edges form a diamond. -/
def IsDiamond (D : Finset V) : Prop := D.card=4 ∧ (pairs G D).card=5

private theorem neighborhood_pair {u v : V} (us : trianglesAt G u=2) (du : G.degree u=3)
    (vs : trianglesAt G v=3) (dv : G.degree v=3) (sep : ¬G.Adj u v)
    (few : (G.neighborFinset u∩G.neighborFinset v).card≤1) :
    ∃ D K : Finset V,IsDiamond G D ∧ G.IsNClique 4 K ∧ (D∩K).card≤1 := by
  classical
  let A := G.neighborFinset u
  let B := G.neighborFinset v
  let D := insert u A
  let K := insert v B
  have ua : u∉A := G.not_mem_neighborFinset_self _
  have vb : v∉B := G.not_mem_neighborFinset_self _
  have fourD : D.card=4 := by simp [D,A,du]
  have fourK : K.card=4 := by simp [K,B,dv]
  have all : A.filter (G.Adj u)=A := filter_true_of_mem (fun w wm => (G.mem_neighborFinset ..).mp wm)
  have count := pairs_insert G ua
  change (pairs G D).card=(pairs G A).card+(A.filter (G.Adj u)).card at count
  change (pairs G A).card=2 at us
  have sa : A.card=3 := (card_neighborFinset_eq_degree ..).trans du
  have d : IsDiamond G D := ⟨fourD,by rw [count,all,sa,us]⟩
  have k : G.IsNClique 4 K := by
    refine ⟨?_,fourK⟩
    intro a am b bm ab
    rcases mem_insert.mp am with rfl|an <;> rcases mem_insert.mp bm with rfl|bn
    · exact (ab rfl).elim
    · exact (G.mem_neighborFinset ..).mp bn
    · exact ((G.mem_neighborFinset ..).mp an).symm
    · exact EarAnchor.full_neighbors G dv vs ((G.mem_neighborFinset ..).mp an) ((G.mem_neighborFinset ..).mp bn) ab
  have uv : u≠v := by intro eq; subst u; change trianglesAt G v=2 at us; omega
  have smaller : D∩K⊆A∩B := by
    intro w wm
    obtain ⟨wd,wk⟩ := mem_inter.mp wm
    rcases mem_insert.mp wd with rfl|wa
    · rcases mem_insert.mp wk with eq|ub
      · exact (uv eq).elim
      · exact (sep ((G.mem_neighborFinset ..).mp ub).symm).elim
    · rcases mem_insert.mp wk with rfl|wb
      · exact (sep ((G.mem_neighborFinset ..).mp wa)).elim
      · exact mem_inter.mpr ⟨wa,wb⟩
  exact ⟨D,K,d,k,(card_le_card smaller).trans few⟩

private theorem induced_pairs {S : Finset V} (D : Finset S) :
    (pairs G (D.map (Function.Embedding.subtype _))).card=(pairs (G.induce (S:Set V)) D).card := by
  classical
  let h : S ↪ V := Function.Embedding.subtype _
  let J := G.induce (S:Set V)
  have eq : pairs G (D.map h)=(pairs J D).map (mapEmbedding h).toEmbedding := by
    ext E; constructor
    · intro em
      obtain ⟨x,xm,y,ym,xy,rfl⟩ := (pair_mem G).mp em
      obtain ⟨a,am,rfl⟩ := mem_map.mp xm
      obtain ⟨b,bm,rfl⟩ := mem_map.mp ym
      refine mem_map.mpr ⟨{a,b},(pair_mem J).mpr ⟨a,am,b,bm,xy,rfl⟩,?_⟩
      change ({a,b}:Finset S).map h={h a,h b}
      simp
    · intro em
      obtain ⟨F,fm,rfl⟩ := mem_map.mp em
      obtain ⟨a,am,b,bm,ab,rfl⟩ := (pair_mem J).mp fm
      change ({a,b}:Finset S).map h∈pairs G (D.map h)
      exact (pair_mem G).mpr ⟨h a,mem_map.mpr ⟨_,am,rfl⟩,h b,mem_map.mpr ⟨_,bm,rfl⟩,ab,by simp⟩
  exact (congrArg card eq).trans (card_map ..)

/-- Any diversity-33 failure, at any order, contains an induced diamond
and a four-clique meeting in at most one vertex. -/
theorem motif_pair (conn : G.Connected) (hn : 2<Fintype.card V) (t : (types G).card=33)
    (bad : bound G<gamma G) :
    ∃ D K : Finset V,IsDiamond G D ∧ G.IsNClique 4 K ∧ (D∩K).card≤1 := by
  classical
  obtain ⟨s,sz,hc,same,_,_,⟨z,zero,_⟩,fail⟩ := OneEar.diversity33_failure G conn hn bad t
  let J := G.induce (s : Set V)
  obtain ⟨u,v,us,du,_,vs,dv,_,sep,few,_⟩ := full_obstruction J ((Fintype.card_coe s).trans sz)
    ((congrArg card same).trans t) hc fail zero
  obtain ⟨D,K,diamond,cl,small⟩ := neighborhood_pair J us du vs dv sep few
  let h : s ↪ V := Function.Embedding.subtype _
  refine ⟨D.map h,K.map h,⟨(card_map ..).trans diamond.1,(induced_pairs G D).trans diamond.2⟩,
    cl.map.mono (G.spanningCoe_induce_le (s:=(s:Set V))),?_⟩
  rwa [←map_inter,card_map]

theorem diamond_free_bound (conn : G.Connected) (hn : 2<Fintype.card V) (t : (types G).card=33)
    (free : ∀ D,¬IsDiamond G D) : gamma G≤bound G := by
  apply Nat.le_of_not_gt; intro fail
  obtain ⟨D,_,h,_,_⟩ := motif_pair G conn hn t fail
  exact free D h

end Graffiti384b.ForcedCubics
#print axioms Graffiti384b.ForcedCubics.motif_pair
#print axioms Graffiti384b.ForcedCubics.diamond_free_bound
