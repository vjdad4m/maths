import AttachmentReserve
import AdjacentFrame
namespace Graffiti384b.Adjacent15
open Finset SimpleGraph
open private Repair.nbr_add from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An exterior high vertex left out of a 26-vertex exterior pool has at
most four neighbors outside it. One can always reserve such a high vertex. -/
theorem exterior_reserve (n : Fintype.card V=33) (hs : (high G).card=29)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e}) (W X : Finset V)
    (wdef : W=(insert e ({a,b}:Finset V))ᶜ) (xw : X⊆W) (sz : X.card=26) :
    ∃ c∈high G,c∉X ∧ c∉({a,b}:Finset V) ∧ G.degree c≤nbr G c X+4 := by
  classical
  let A : Finset V := {a,b}
  have size := card_union_le X A
  have az : A.card=2 := card_pair ab
  have room := le_card_sdiff (X∪A) (high G)
  obtain ⟨c,cm⟩ := card_pos.mp (show 0<((high G)\(X∪A)).card by omega)
  obtain ⟨ch,ca⟩ := mem_sdiff.mp cm
  have cx : c∉X := fun h => ca (mem_union_left _ h)
  have na : c∉A := fun h => ca (mem_union_right _ h)
  have dg : 3≤G.degree c := (mem_filter.mp ch).2
  have de : G.degree e=2 := by rw [←card_neighborFinset_eq_degree,ear,card_pair ab]
  have ce : c≠e := by intro h; subst c; omega
  have cw : c∈W := by rw [wdef]; exact mem_compl.mpr (fun h => (mem_insert.mp h).elim ce na)
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  have ws : W.card=30 := by rw [wdef,card_compl,card_insert_of_not_mem (by simp [ea.ne,eb.ne]),card_pair ab,n]
  obtain ⟨one,deg⟩ := PortRepair29.thin_degrees G ear thin c (wdef ▸ cw)
  rw [←wdef] at deg
  have split := Repair.nbr_add G c (show Disjoint (W\X) X from disjoint_left.mpr (fun _ m => (mem_sdiff.mp m).2))
  rw [sdiff_union_of_subset xw] at split
  have cap : nbr G c (W\X)≤3 := by
    have sub : (W\X).filter (G.Adj c)⊆(W\X).erase c := by
      intro i im; obtain ⟨iw,ci⟩ := mem_filter.mp im
      exact mem_erase.mpr ⟨ci.ne.symm,iw⟩
    have count := card_le_card sub
    rwa [card_erase_of_mem (mem_sdiff.mpr ⟨cw,cx⟩),card_sdiff xw,ws,sz] at count
  exact ⟨c,ch,cx,na,by omega⟩

/-- Every exterior vertex that is low or equals the reserved attachment is outside the sample.
Uncredited vertices among these four increase the number of credited pool vertices. -/
theorem supported (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e}) (W : Finset V) (wdef : W=(insert e ({a,b}:Finset V))ᶜ)
    {u v z : V} (B : Finset V) (bw : B⊆W)
    (omitted : ∀ i∈B,i=z ∨ G.degree i≤2) (no : ∀ i∈B,¬0<nbr G i {a,b})
    (hits : 17≤(W.filter (fun i => 0<nbr G i {a,b})).card+B.card)
    (uw : u∈W) (vw : v∈W) (zw : z∈W) (uv : G.Adj u v) (uz : u≠z)
    (du : G.degree u=2) (dv : G.degree v=2) (vn : G.neighborFinset v={u,z})
    (bad : bound G<gamma G) : False := by
  classical
  obtain ⟨hs,_⟩ := Cover31.residual G t q bad
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by omega)
  let A : Finset V := {a,b}
  let J : Finset V := insert z A
  let O : Finset V := {e,v}
  have out {i : V} (iw : i∈W) : i≠e ∧ i∉A := by
    simpa [wdef,A,not_or] using iw
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  have vz : G.Adj v z := (G.mem_neighborFinset ..).mp (vn ▸ mem_insert_of_mem (mem_singleton_self _))
  have low {i : V} (di : G.degree i=2) : i∉high G := by
    intro m; have := (mem_filter.mp m).2; omega
  have eh := low (show G.degree e=2 by rw [←card_neighborFinset_eq_degree,ear,card_pair ab])
  have uh := low du
  have vh := low dv
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
    · rw [mem_singleton.mp p]; exact PinnedColor34.two G uz uv.symm vz uf zf
  have away (i : V) (ix : i∈X) (w : V) (wo : w∈O) (iw : G.Adj i w) : False := by
    have m := (G.mem_neighborFinset ..).mpr iw.symm
    rcases mem_insert.mp wo with rfl|p
    · rw [ear] at m; exact xa ix m
    · rw [mem_singleton.mp p,vn] at m
      rcases mem_insert.mp m with rfl|h
      · exact uh (xh ix)
      · exact xj ix (mem_singleton.mp h ▸ mem_insert_self ..)
  let hit := fun i => 0<nbr G i A
  have ws : W.card=30 := by
    rw [wdef,card_compl,card_insert_of_not_mem (by simp [ea.ne,eb.ne]),card_pair ab,n]
  have bsub : B⊆W\X := by
    intro i im
    refine mem_sdiff.mpr ⟨bw im,fun ix => ?_⟩
    rcases omitted i im with rfl|small
    · exact xj ix (mem_insert_self ..)
    · have large : 3≤G.degree i := (mem_filter.mp (xh ix)).2; omega
  have excess : W.filter hit\X.filter hit ⊆ (W\X)\B := by
    intro i im
    obtain ⟨ih,nx⟩ := mem_sdiff.mp im
    obtain ⟨iw,h⟩ := mem_filter.mp ih
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨iw,fun ix => nx (mem_filter.mpr ⟨ix,h⟩)⟩,fun ib => no i ib h⟩
  have ex := card_le_card excess
  have small := card_le_card bsub
  rw [card_sdiff bsub,card_sdiff xw,ws,sz] at ex
  rw [card_sdiff xw,ws,sz] at small
  have ct := le_card_sdiff (X.filter hit) (W.filter hit)
  change 17≤(W.filter hit).card+B.card at hits
  have hx : 13≤(X.filter hit).card := by omega
  obtain ⟨c,ch,cx,ca,oc⟩ := exterior_reserve G n hs ear ab thin W X wdef xw sz
  have ih : insert c X ⊆ high G := insert_subset ch xh
  have cap := pool G n X O A sz (card_pair (out vw).1.symm) so sa safe away cx ca
    (inj.mono (show ((insert c X : Finset V):Set V)⊆high G from ih))
    (fun i im => floor i (ih im)) oc hx
  rw [bound,t,n] at bad; omega

/-- At order 33 and diversity 31 with 32 nonleaves, adjacent degree-two
vertices bound the contact count of every thin ear by fourteen in a failure. -/
theorem adjacent_cap (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e}) (W : Finset V)
    (wdef : W=(insert e ({a,b}:Finset V))ᶜ) {u v : V} (uv : G.Adj u v)
    (du : G.degree u=2) (dv : G.degree v=2) (bad : bound G<gamma G) :
    (W.filter (fun i => 0<nbr G i {a,b})).card≤14 := by
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
  have noV : ¬0<nbr G v {a,b} := by
    intro p; have := Weighted29.anchored_pair G n q t ear ab thin W wdef uw vw uv du dv p bad; omega
  have noU : ¬0<nbr G u {a,b} := by
    intro p; have := Weighted29.anchored_pair G n q t ear ab thin W wdef vw uw uv.symm dv du p bad; omega
  obtain ⟨z,zm,zu⟩ := exists_mem_ne (s:=G.neighborFinset v) (by rw [card_neighborFinset_eq_degree,dv]; decide) u
  have vz := (G.mem_neighborFinset ..).mp zm
  have zw : z∈W := by
    rw [wdef]; apply mem_compl.mpr; intro m
    rcases mem_insert.mp m with rfl|za
    · exact mem_compl.mp (wdef ▸ vw) (mem_insert_of_mem (ear ▸ (G.mem_neighborFinset ..).mpr vz.symm))
    · exact noV (card_pos.mpr ⟨z,mem_filter.mpr ⟨za,vz⟩⟩)
  have sub : {u,z}⊆G.neighborFinset v := insert_subset ((G.mem_neighborFinset ..).mpr uv.symm) (singleton_subset_iff.mpr zm)
  have vn := (eq_of_subset_of_card_le sub (by rw [card_pair zu.symm,card_neighborFinset_eq_degree,dv])).symm
  exact supported G n q t ear ab thin W wdef {u,v}
    (insert_subset uw (singleton_subset_iff.mpr vw))
    (by intro i im; rcases mem_insert.mp im with rfl|p
        · exact Or.inr du.le
        · exact Or.inr (mem_singleton.mp p ▸ dv.le))
    (by intro i im; rcases mem_insert.mp im with rfl|p
        · exact noU
        · rw [mem_singleton.mp p]; exact noV)
    (by rw [card_pair uv.ne]; omega) uw vw zw uv zu.symm du dv vn bad


/-- Every degree-two vertex in an adjacent-pair counterexample has a thin
neighbor pair, and all its exterior contact counts are at most fourteen. -/
theorem all_ears (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {u v : V} (uv : G.Adj u v) (du : G.degree u=2) (dv : G.degree v=2)
    (bad : bound G<gamma G) {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b) :
    G.neighborFinset a∩G.neighborFinset b={e} ∧
    ((insert e ({a,b}:Finset V))ᶜ.filter (fun i => 0<nbr G i {a,b})).card≤14 := by
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  have thin : G.neighborFinset a∩G.neighborFinset b={e} := by
    apply Subset.antisymm _ (singleton_subset_iff.mpr (mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr ea.symm,(G.mem_neighborFinset ..).mpr eb.symm⟩))
    intro x xm; by_contra off
    have ax := (G.mem_neighborFinset ..).mp (mem_inter.mp xm).1
    have bx := (G.mem_neighborFinset ..).mp (mem_inter.mp xm).2
    have sq : Squares29.Opposite G e x := ⟨by rw [←card_neighborFinset_eq_degree,ear,card_pair ab],
      fun eq => off (mem_singleton.mpr eq.symm),by
        rw [ear]; exact insert_subset ((G.mem_neighborFinset ..).mpr ax.symm)
          (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr bx.symm))⟩
    exact (not_lt_of_ge (exact_of_square G sq du dv uv)) bad
  exact ⟨thin,adjacent_cap G n q t ear ab thin _ rfl uv du dv bad⟩

end Graffiti384b.Adjacent15
#print axioms Graffiti384b.Adjacent15.exterior_reserve
#print axioms Graffiti384b.Adjacent15.adjacent_cap
#print axioms Graffiti384b.Adjacent15.supported
#print axioms Graffiti384b.Adjacent15.all_ears
