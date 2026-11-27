import ThreeReservedRanks
import AdjacentFront
namespace Graffiti384b.AdjacentFull
open Finset SimpleGraph Adjacent15
open private Repair.linkEdges Repair.edge_info from Repair384b
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Apart from one possible triangle, every pair of adjacent neighbors is in P. -/
private theorem score_cap (v : V) (P edge : Finset V) (k : ℕ) (size : nbr G v P≤k)
    (outside : ∀ i j,G.Adj v i → G.Adj v j → G.Adj i j → i∉P → ({i,j}:Finset V)=edge) :
    trianglesAt G v≤1+k.choose 2 := by
  classical
  have cover : Repair.linkEdges G v⊆insert edge ((P.filter (G.Adj v)).powersetCard 2) := by
    intro p pm
    obtain ⟨sub,sz,cl⟩ := Repair.edge_info G pm
    obtain ⟨i,j,ij,eq⟩ := card_eq_two.mp sz
    have im : i∈p := eq ▸ mem_insert_self ..
    have jm : j∈p := eq ▸ mem_insert_of_mem (mem_singleton_self _)
    have vi := (G.mem_neighborFinset ..).mp (sub im)
    have vj := (G.mem_neighborFinset ..).mp (sub jm)
    have adj := cl i im j jm ij
    by_cases ip : i∈P
    · by_cases jp : j∈P
      · apply mem_insert_of_mem; apply mem_powersetCard.mpr
        refine ⟨?_,sz⟩
        rw [eq]; exact insert_subset (mem_filter.mpr ⟨ip,vi⟩) (singleton_subset_iff.mpr (mem_filter.mpr ⟨jp,vj⟩))
      · exact mem_insert.mpr (Or.inl (eq.trans ((pair_comm ..).trans (outside j i vj vi adj.symm jp))))
    · exact mem_insert.mpr (Or.inl (eq.trans (outside i j vi vj adj ip)))
  have cap := (card_le_card cover).trans (card_insert_le ..)
  rw [card_powersetCard] at cap
  change trianglesAt G v≤(nbr G v P).choose 2+1 at cap
  have mono := Nat.choose_le_choose 2 size
  omega

private theorem profile_impossible (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {u v f a b z l : V} (uv : G.Adj u v) (du : G.degree u=2) (dv : G.degree v=2)
    (uf : u≠f) (vf : v≠f) (ear : G.neighborFinset f={a,b}) (ab : a≠b)
    (vz : G.Adj v z) (zu : z≠u) (dl : G.degree l≤1) (bad : bound G<gamma G) : False := by
  classical
  let A : Finset V := {a,b}
  let W := (insert f A)ᶜ
  have df : G.degree f=2 := by rw [←card_neighborFinset_eq_degree,ear,card_pair ab]
  have fa (i : V) (ia : i∈A) : G.Adj f i := (G.mem_neighborFinset ..).mp (ear ▸ ia)
  have anchors (i : V) (ia : i∈A) : 3≤G.degree i := by
    by_contra! low
    exact (not_lt_of_ge (two_steps G uf.symm df du (fa i ia) (by omega) uv dv.le vf)) bad
  have out {i : V} (ne : i≠f) (na : i∉A) : i∈W := mem_compl.mpr (fun h => (mem_insert.mp h).elim ne na)
  have uw : u∈W := out uf (fun h => by have := anchors u h; omega)
  have vw : v∈W := out vf (fun h => by have := anchors v h; omega)
  have hz : 3≤G.degree z := by
    by_contra! low
    exact (not_lt_of_ge (two_steps G uv.ne du dv uv dv.le vz (by omega) zu)) bad
  have zw : z∈W := out (show z≠f by intro eq; subst z; omega) (fun za =>
      (not_lt_of_ge (shared_anchor G uv vz (fa z za) uf vf du dv df)) bad)
  have lw : l∈W := out (show l≠f by intro eq; subst l; omega) (fun h => by have := anchors l h; omega)
  have peers {i j : V} (ij : G.Adj i j) (di : G.degree i=2) (dj : G.degree j=2)
      (nf : i≠f) (mf : j≠f) : ¬0<nbr G j A := by
    intro h; obtain ⟨k,km⟩ := card_pos.mp h
    obtain ⟨ka,jk⟩ := mem_filter.mp km
    exact (not_lt_of_ge (shared_anchor G ij jk (fa k ka) nf mf di dj df)) bad

  obtain ⟨hs,_⟩ := Cover31.residual G t q bad
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by omega)
  let J := insert z A
  let X := high G\J
  let O : Finset V := {f,v}
  have za : z∉A := fun h => mem_compl.mp zw (mem_insert_of_mem h)
  have jh : J⊆high G := insert_subset (mem_filter.mpr ⟨mem_univ _,hz⟩)
    (fun i m => mem_filter.mpr ⟨mem_univ _,anchors i m⟩)
  have az : A.card=2 := card_pair ab
  have xs : X.card=26 := by dsimp only [X]; rw [card_sdiff jh,hs,show J.card=3 by dsimp only [J]; rw [card_insert_of_not_mem za,az]]
  have xh : X⊆high G := sdiff_subset
  have xj {i : V} (ix : i∈X) : i∉J := (mem_sdiff.mp ix).2
  have low {i : V} (d : G.degree i≤2) : i∉X := by
    intro ix; have h : 3≤G.degree i := (mem_filter.mp (xh ix)).2; omega
  have xm : X⊆W := fun i ix => out (fun eq => low df.le (eq ▸ ix)) (fun p => xj ix (mem_insert_of_mem p))
  have vn : G.neighborFinset v={u,z} := by
    have sub : {u,z}⊆G.neighborFinset v := insert_subset ((G.mem_neighborFinset ..).mpr uv.symm)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr vz))
    exact (eq_of_subset_of_card_le sub (by rw [card_pair zu.symm,card_neighborFinset_eq_degree,dv])).symm
  have so : Disjoint X O := disjoint_left.mpr (by
    intro i ix io
    rcases mem_insert.mp io with rfl|p
    · exact low df.le ix
    · exact low dv.le (mem_singleton.mp p ▸ ix))
  have af {i : V} (ia : i∈A) : i∈(X∪O)ᶜ := mem_compl.mpr (fun m => by
    rcases mem_union.mp m with ix|io
    · exact xj ix (mem_insert_of_mem ia)
    · have hh := anchors i ia
      rcases mem_insert.mp io with rfl|p
      · omega
      · rw [mem_singleton.mp p] at hh; omega)
  have ufixed : u∈(X∪O)ᶜ := by simp [O,low du.le,uf,uv.ne]
  have zfixed : z∈(X∪O)ᶜ := by
    have zx : z∉X := fun m => xj (i:=z) m (mem_insert_self ..)
    have zf : z≠f := fun eq => by subst z; omega
    simp [O,zx,zf,vz.ne.symm]
  have safe (i : V) (io : i∈O) : 2≤nbr G i (X∪O)ᶜ := by
    rcases mem_insert.mp io with rfl|p
    · exact PinnedColor34.two G ab (fa a (mem_insert_self ..)) (fa b (mem_insert_of_mem (mem_singleton_self _)))
        (af (mem_insert_self ..)) (af (mem_insert_of_mem (mem_singleton_self _)))
    · rw [mem_singleton.mp p]; exact PinnedColor34.two G zu.symm uv.symm vz ufixed zfixed
  have away (i : V) (ix : i∈X) (w : V) (wo : w∈O) (iw : G.Adj i w) : False := by
    have m := (G.mem_neighborFinset ..).mpr iw.symm
    rcases mem_insert.mp wo with rfl|p
    · rw [ear] at m; exact xj ix (mem_insert_of_mem m)
    · rw [mem_singleton.mp p,vn] at m
      rcases mem_insert.mp m with rfl|eq
      · exact low du.le ix
      · exact xj ix (mem_singleton.mp eq ▸ mem_insert_self ..)
  let D : Finset V := {z,l}
  let U := ({u,v}:Finset V)∪D
  have zl : z≠l := by intro h; subst z; omega
  have zs : D.card=2 := card_pair zl
  have sep : Disjoint ({u,v}:Finset V) D := disjoint_left.mpr (by
    intro i p m
    have left : i=u ∨ i=v := by simpa using p
    have right : i=z ∨ i=l := by simpa [D] using m
    rcases left with rfl|rfl <;> rcases right with h|h <;> subst_vars <;> omega)
  have ds : U.card=4 := by dsimp only [U]; rw [card_union_of_disjoint sep,card_pair uv.ne,zs]
  have sub : U⊆W\X := union_subset
    (insert_subset (mem_sdiff.mpr ⟨uw,low du.le⟩) (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨vw,low dv.le⟩)))
    (insert_subset (mem_sdiff.mpr ⟨zw,fun m => xj m (mem_insert_self ..)⟩)
      (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨lw,low (by omega)⟩)))
  have ff : f∉A := fun m => (fa f m).ne rfl
  have ws : W.card=30 := by dsimp only [W]; rw [card_compl,card_insert_of_not_mem ff,az,n]
  have eqU : W\X=U := (eq_of_subset_of_card_le sub (by rw [card_sdiff xm,ws,xs,ds])).symm

  let K : Finset V := {a,b,z}
  have kj : K=J := by ext i; simp [K,J,A]; tauto
  let hits := X.filter (fun i => 0<nbr G i K)
  let m := hits.card
  let x := nbr G a X
  let y := nbr G b X
  have th := (Adjacent15.all_ears G n q t uv du dv bad ear ab).1
  have plus {k : V} (kk : k∈K) : X.filter (G.Adj k)⊆hits := by
    intro i im; exact mem_filter.mpr ⟨(mem_filter.mp im).1,card_pos.mpr ⟨k,mem_filter.mpr ⟨kk,(mem_filter.mp im).2.symm⟩⟩⟩
  have sepAB : Disjoint (X.filter (G.Adj a)) (X.filter (G.Adj b)) := disjoint_left.mpr (by
    intro i am bm
    have cm : i∈G.neighborFinset a∩G.neighborFinset b := mem_inter.mpr
      ⟨(G.mem_neighborFinset ..).mpr (mem_filter.mp am).2,(G.mem_neighborFinset ..).mpr (mem_filter.mp bm).2⟩
    rw [th,mem_singleton] at cm; exact low df.le (cm ▸ (mem_filter.mp am).1))
  have xy : x+y≤m := by
    have ct := card_le_card (union_subset (plus (show a∈K by simp [K])) (plus (show b∈K by simp [K])))
    rwa [card_union_of_disjoint sepAB] at ct
  have zc : nbr G z X≤m := card_le_card (plus (show z∈K by simp [K]))
  have noLeaf {c i j : V} (ci : G.Adj c i) (cj : G.Adj c j) (ij : G.Adj i j) : i≠l := by
    intro eq; subst i
    have sub : {c,j}⊆G.neighborFinset l := insert_subset ((G.mem_neighborFinset ..).mpr ci.symm)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr ij))
    have count := card_le_card sub
    rw [card_pair cj.ne,card_neighborFinset_eq_degree] at count; omega
  have exterior {i : V} (iw : i∈W) (ix : i∉X) : i=u ∨ i=v ∨ i=z ∨ i=l := by
    have iu : i∈U := eqU ▸ mem_sdiff.mpr ⟨iw,ix⟩
    simp only [U,D,mem_union,mem_insert,mem_singleton] at iu
    rcases iu with (h|h)|(h|h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have anchor {p r : V} (order : ({p,r}:Finset V)=A) :
      trianglesAt G p≤1+(nbr G p X+1).choose 2 := by
    have thin := (Adjacent15.all_ears G n q t uv du dv bad (ear.trans order.symm) (by
      intro eq; subst r; have := congrArg card order; simp [az] at this)).1
    have pin : p∈A := order ▸ mem_insert_self ..
    have size : nbr G p (X∪{z})≤nbr G p X+1 := by
      unfold nbr; rw [filter_union]
      exact (card_union_le ..).trans (Nat.add_le_add_left ((card_le_card (filter_subset ..)).trans_eq (card_singleton z)) _)
    apply score_cap G p (X∪{z}) {r,f} _ size
    intro i j pi pj ij off
    have ix : i∉X := fun h => off (mem_union_left _ h)
    have iz : i≠z := fun eq => off (mem_union_right _ (mem_singleton.mpr eq))
    by_cases ir : i=r
    · subst i
      have jm : j∈G.neighborFinset p∩G.neighborFinset r := mem_inter.mpr
        ⟨(G.mem_neighborFinset ..).mpr pj,(G.mem_neighborFinset ..).mpr ij⟩
      rw [thin,mem_singleton] at jm; rw [jm]
    by_cases ie : i=f
    · subst i
      have jm := (G.mem_neighborFinset ..).mpr ij
      rw [ear.trans order.symm,mem_insert,mem_singleton] at jm
      rw [jm.resolve_left pj.ne.symm,pair_comm]
    have iw := out ie (fun m => by rw [←order,mem_insert,mem_singleton] at m; exact m.elim pi.ne.symm ir)
    have h : 0<nbr G i A := card_pos.mpr ⟨p,mem_filter.mpr ⟨pin,pi.symm⟩⟩
    exact False.elim ((exterior iw ix).elim (fun eq => peers uv.symm dv du vf uf (eq ▸ h))
      (fun m => m.elim (fun eq => peers uv du dv uf vf (eq ▸ h)) (fun m => m.elim iz (noLeaf pi pj ij))))
  have sa := anchor (p:=a) (r:=b) rfl
  have sb := anchor (p:=b) (r:=a) (pair_comm ..)
  have sc : trianglesAt G z≤1+(m+1).choose 2 := by
    have one := (PortRepair29.thin_degrees G ear th z zw).1
    have size : nbr G z (X∪A)≤m+1 := by
      unfold nbr; rw [filter_union]
      exact (card_union_le ..).trans (Nat.add_le_add zc one)
    apply score_cap G z (X∪A) {u,v} _ size
    intro i j zi zj ij off
    have ix : i∉X := fun h => off (mem_union_left _ h)
    have ia : i∉A := fun h => off (mem_union_right _ h)
    have ie : i≠f := by
      intro eq; subst i
      have zm := (G.mem_neighborFinset ..).mpr zi.symm
      rw [ear] at zm; exact za zm
    rcases exterior (out ie ia) ix with rfl|rfl|eq|eq
    · have su : {v,z}⊆G.neighborFinset i := insert_subset ((G.mem_neighborFinset ..).mpr uv)
        (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr zi.symm))
      have un := (eq_of_subset_of_card_le su (by rw [card_pair vz.ne,card_neighborFinset_eq_degree,du])).symm
      have jm := (G.mem_neighborFinset ..).mpr ij
      rw [un,mem_insert,mem_singleton] at jm; rw [jm.resolve_right zj.ne.symm]
    · have jm := (G.mem_neighborFinset ..).mpr ij
      rw [vn,mem_insert,mem_singleton] at jm; rw [jm.resolve_right zj.ne.symm,pair_comm]
    · exact False.elim (zi.ne eq.symm)
    · exact False.elim (noLeaf zi zj ij eq)
  have jx : Disjoint X K := disjoint_left.mpr (fun _ xm wm => xj xm (kj ▸ wm))
  have hx : insert a (insert b (insert z X)) ⊆ high G := insert_subset
    (mem_filter.mpr ⟨mem_univ _,anchors a (mem_insert_self ..)⟩) (insert_subset
      (mem_filter.mpr ⟨mem_univ _,anchors b (mem_insert_of_mem (mem_singleton_self _))⟩)
      (insert_subset (mem_filter.mpr ⟨mem_univ _,hz⟩) xh))
  have az' : a≠z := fun eq => za (eq ▸ mem_insert_self ..)
  have bz' : b≠z := fun eq => za (eq ▸ mem_insert_of_mem (mem_singleton_self _))
  have cap := exact_pool G n X O ab az' bz' xs (card_pair vf.symm) so safe away xh jx
    (inj.mono (show ((insert a (insert b (insert z X)):Finset V):Set V)⊆high G from hx))
    (fun i im => floor i (hx im)) x y m xy rfl sa sb sc
  rw [bound,t,n] at bad; omega

/-- Complete adjacent-pair branch of the order-33, diversity-31, 32-nonleaf
case of Graffiti.pc #384b. No condition on the number of anchor contacts. -/
theorem exact (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {u v : V} (uv : G.Adj u v) (du : G.degree u=2) (dv : G.degree v=2) : gamma G≤bound G := by
  classical
  by_contra! bad
  obtain ⟨_,ts⟩ := Cover31.residual G t q bad
  have rest := le_card_sdiff ({u,v}:Finset V) (LowSample.twos G)
  rw [ts,card_pair uv.ne] at rest
  obtain ⟨f,fm⟩ := card_pos.mp (show 0<((LowSample.twos G)\{u,v}).card by omega)
  obtain ⟨ft,fo⟩ := mem_sdiff.mp fm
  have df := LowSample.two_degree G ft
  have uf : u≠f := fun eq => fo (mem_insert.mpr (Or.inl eq.symm))
  have vf : v≠f := fun eq => fo (mem_insert_of_mem (mem_singleton.mpr eq.symm))
  obtain ⟨a,b,ab,ear⟩ := card_eq_two.mp ((card_neighborFinset_eq_degree ..).trans df)
  obtain ⟨z,zm,zu⟩ := exists_mem_ne (s:=G.neighborFinset v) (by rw [card_neighborFinset_eq_degree,dv]; decide) u
  have size : (nonleaves G)ᶜ.card=1 := by rw [card_compl,n,q]
  obtain ⟨l,lm⟩ := card_pos.mp (show 0<(nonleaves G)ᶜ.card by omega)
  have dl : G.degree l≤1 := by by_contra! large; exact mem_compl.mp lm (mem_filter.mpr ⟨mem_univ _,by omega⟩)
  exact profile_impossible G n q t uv du dv uf vf ear ab ((G.mem_neighborFinset ..).mp zm) zu dl bad

end Graffiti384b.AdjacentFull
#print axioms Graffiti384b.AdjacentFull.exact
