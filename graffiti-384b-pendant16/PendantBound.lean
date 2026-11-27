import PendantSample
namespace Graffiti384b.Pendant16
open Finset SimpleGraph
open private FiniteRange.bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Two safe fixed omissions and fourteen credited high vertices suffice at order 33.
The sample contains nine of the twenty-six ranked vertices. -/
theorem pool_bound (n : Fintype.card V=33) (X O A : Finset V) (sz : X.card=26)
    (os : O.card=2) (sep : Disjoint X O) (sa : Disjoint X A)
    (safe : ∀ v∈O,2≤nbr G v (X∪O)ᶜ) (away : ∀ v∈X,∀ w∈O,¬G.Adj v w)
    (inj : Set.InjOn (trianglesAt G) (X:Set V)) (lo : ∀ v∈X,2≤trianglesAt G v)
    (hits : 14≤(X.filter (fun v => 0<nbr G v A)).card) : gamma G≤17 := by
  classical
  let K := X.powersetCard 9
  let B := FiniteRange.bad G X
  have cap := ranked G X A sz sa inj lo
  have trans : (∑ s∈K,(B s).card) = ∑ v∈X,(K.filter (fun s => v∈B s)).card := by
    have inc (s : Finset V) : B s⊆X := (filter_subset ..).trans sdiff_subset
    calc _ = ∑ s∈K,∑ v∈X,if v∈B s then 1 else 0 := by
              simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (inc _)]
         _ = _ := by rw [sum_comm]; simp [sum_boole]
  by_contra! bad
  have each (s : Finset V) (sm : s∈K) : 4≤(B s).card := by
    have tr := trial G X O s sep safe away
    obtain ⟨sub,k⟩ := mem_powersetCard.mp sm
    rw [card_sdiff sub,sz,k,os,n] at tr
    change 4≤(FiniteRange.bad G X s).card; omega
  have mass := sum_le_sum each
  rw [sum_const,smul_eq_mul,trans] at mass
  have size : K.card=3124550 := by dsimp [K]; rw [card_powersetCard,sz,Nat.choose_eq_fast_choose]; decide
  rw [size] at mass
  change (∑ v∈X,(K.filter (fun s => v∈B s)).card)+_≤_ at cap
  omega

/-- Exclude the pendant triangle found by Weighted29.pendant_at_sixteen.
No incidence between the attachment vertex and the ear anchors is required. -/
theorem pendant_bound (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (W : Finset V) (wdef : W=(insert e ({a,b}:Finset V))ᶜ)
    (hits : 16≤(W.filter (fun i => 0<nbr G i {a,b})).card)
    {u v z : V} (uw : u∈W) (vw : v∈W) (zw : z∈W)
    (un : G.neighborFinset u={v,z}) (vn : G.neighborFinset v={u,z}) :
    gamma G≤bound G := by
  classical
  by_contra! bad
  obtain ⟨hs,_⟩ := Cover31.residual G t q bad
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by omega)
  let A : Finset V := {a,b}
  let J : Finset V := insert z A
  let O : Finset V := {e,v}
  have out {i : V} (iw : i∈W) : i≠e ∧ i∉A := by
    simpa [wdef,A,not_or] using iw
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  have uv : G.Adj u v := (G.mem_neighborFinset ..).mp (un ▸ mem_insert_self ..)
  have uz : G.Adj u z := (G.mem_neighborFinset ..).mp (un ▸ mem_insert_of_mem (mem_singleton_self _))
  have vz : G.Adj v z := (G.mem_neighborFinset ..).mp (vn ▸ mem_insert_of_mem (mem_singleton_self _))
  have low {i : V} (di : G.degree i=2) : i∉high G := by
    intro m; have := (mem_filter.mp m).2; omega
  have eh := low (show G.degree e=2 by rw [←card_neighborFinset_eq_degree,ear,card_pair ab])
  have uh := low (show G.degree u=2 by rw [←card_neighborFinset_eq_degree,un,card_pair vz.ne])
  have vh := low (show G.degree v=2 by rw [←card_neighborFinset_eq_degree,vn,card_pair uz.ne])
  have js : J.card≤3 := (card_insert_le ..).trans (by rw [show A.card=2 from card_pair ab])
  have room := le_card_sdiff J (high G)
  obtain ⟨X,sub,sz⟩ := exists_subset_card_eq (show 26≤((high G)\J).card by omega)
  have xh : X⊆high G := sub.trans sdiff_subset
  have xj {i : V} (im : i∈X) : i∉J := (mem_sdiff.mp (sub im)).2
  have xa {i : V} (im : i∈X) : i∉A := fun m => xj im (mem_insert_of_mem m)
  have xw : X⊆W := by
    intro i im
    rw [wdef]; exact mem_compl.mpr (fun m => (mem_insert.mp m).elim (fun eq => eh (eq ▸ xh im)) (xa im))
  have so : Disjoint X O := disjoint_left.mpr (by
    intro i im io; rcases mem_insert.mp io with rfl|p
    · exact eh (xh im)
    · exact vh (mem_singleton.mp p ▸ xh im))
  have sa : Disjoint X A := disjoint_left.mpr (fun _ im => xa im)
  have af {i : V} (ia : i∈A) : i∈(X∪O)ᶜ := by
    apply mem_compl.mpr; intro m
    rcases mem_union.mp m with ix|io
    · exact xa ix ia
    · rcases mem_insert.mp io with rfl|p
      · simp [A,ea.ne,eb.ne] at ia
      · exact (out vw).2 (mem_singleton.mp p ▸ ia)
  have uf : u∈(X∪O)ᶜ := by
    simp only [mem_compl,mem_union,mem_insert,mem_singleton,not_or,O]
    exact ⟨fun m => uh (xh m),(out uw).1,uv.ne⟩
  have zf : z∈(X∪O)ᶜ := by
    simp only [mem_compl,mem_union,mem_insert,mem_singleton,not_or,O]
    exact ⟨fun m => xj m (mem_insert_self ..),(out zw).1,vz.ne.symm⟩
  have safe (i : V) (io : i∈O) : 2≤nbr G i (X∪O)ᶜ := by
    rcases mem_insert.mp io with rfl|p
    · exact PinnedColor34.two G ab ea eb (af (mem_insert_self ..)) (af (mem_insert_of_mem (mem_singleton_self _)))
    · rw [mem_singleton.mp p]; exact PinnedColor34.two G uz.ne uv.symm vz uf zf
  have away (i : V) (ix : i∈X) (w : V) (wo : w∈O) (iw : G.Adj i w) : False := by
    have m := (G.mem_neighborFinset ..).mpr iw.symm
    rcases mem_insert.mp wo with rfl|p
    · rw [ear] at m; exact xa ix m
    · rw [mem_singleton.mp p,vn] at m
      rcases mem_insert.mp m with rfl|h
      · exact uh (xh ix)
      · exact xj ix (mem_singleton.mp h ▸ mem_insert_self ..)
  let hit := fun i => 0<nbr G i A
  have off {i j : V} (nn : G.neighborFinset i={j,z}) (jw : j∈W) : ¬hit i := by
    intro pos; obtain ⟨c,cm⟩ := card_pos.mp pos
    obtain ⟨ca,ic⟩ := mem_filter.mp cm
    have ck := nn ▸ (G.mem_neighborFinset ..).mpr ic
    rcases mem_insert.mp ck with rfl|p
    · exact (out jw).2 ca
    · exact (out zw).2 (mem_singleton.mp p ▸ ca)
  have ws : W.card=30 := by
    rw [wdef,card_compl,card_insert_of_not_mem (by simp [ea.ne,eb.ne]),card_pair ab,n]
  have pairSub : ({u,v}:Finset V)⊆W\X := insert_subset
    (mem_sdiff.mpr ⟨uw,fun m => uh (xh m)⟩) (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨vw,fun m => vh (xh m)⟩))
  have excess : W.filter hit\X.filter hit ⊆ (W\X)\{u,v} := by
    intro i im
    obtain ⟨ih,nx⟩ := mem_sdiff.mp im
    obtain ⟨iw,h⟩ := mem_filter.mp ih
    refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨iw,fun ix => nx (mem_filter.mpr ⟨ix,h⟩)⟩,?_⟩
    intro p; rcases mem_insert.mp p with rfl|p
    · exact off un vw h
    · exact off vn uw (mem_singleton.mp p ▸ h)
  have ex := card_le_card excess
  rw [card_sdiff pairSub,card_sdiff xw,ws,sz,card_pair uv.ne] at ex
  have ct := le_card_sdiff (X.filter hit) (W.filter hit)
  change 16≤(W.filter hit).card at hits
  have hx : 14≤(X.filter hit).card := by omega
  have zcap := pool_bound G n X O A sz (card_pair (out vw).1.symm) so sa safe away
    (inj.mono (show (X:Set V)⊆high G from xh)) (fun i im => floor i (xh im)) hx
  rw [bound,t,n] at bad; omega


/-- In a counterexample every adjacent degree-two pair forces the exterior
anchor-hit count down to at most fifteen. The pair can occur anywhere. -/
theorem adjacent_cap (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e}) (W : Finset V)
    (wdef : W=(insert e ({a,b}:Finset V))ᶜ) {u v : V} (uv : G.Adj u v)
    (du : G.degree u=2) (dv : G.degree v=2) (bad : bound G<gamma G) :
    (W.filter (fun i => 0<nbr G i {a,b})).card≤15 := by
  by_contra! hits
  have low := (Weighted29.low_anchors G n q t ear ab thin W wdef bad).1
  have ha : 3≤G.degree a := by by_contra! h; have := low (Or.inl (by omega)); omega
  have hb : 3≤G.degree b := by by_contra! h; have := low (Or.inr (by omega)); omega
  have off {i : V} (di : G.degree i=2) : i∉({a,b}:Finset V) := by
    intro m; rcases mem_insert.mp m with rfl|p
    · omega
    · have eq := mem_singleton.mp p; subst i; omega
  have exterior {i j : V} (ij : G.Adj i j) (di : G.degree i=2) (dj : G.degree j=2) : i∈W := by
    rw [wdef]; apply mem_compl.mpr; intro m
    rcases mem_insert.mp m with rfl|ia
    · exact off dj (ear ▸ (G.mem_neighborFinset ..).mpr ij)
    · exact off di ia
  have uw := exterior uv du dv
  have vw := exterior uv.symm dv du
  obtain ⟨z,zw,un,vn⟩ := Weighted29.pendant_at_sixteen G n q t ear ab thin W wdef bad hits uw vw uv du dv
  exact (not_lt_of_ge (pendant_bound G n q t ear ab W wdef hits uw vw zw un vn)) bad

end Graffiti384b.Pendant16
#print axioms Graffiti384b.Pendant16.pool_bound
#print axioms Graffiti384b.Pendant16.pendant_bound
#print axioms Graffiti384b.Pendant16.adjacent_cap
