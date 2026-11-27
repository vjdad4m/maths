import CliquePool
import AdjacentFront
namespace Graffiti384b.Adjacent12
open Finset SimpleGraph Adjacent15
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The two different contact counts, measured at the third ear and at one
endpoint of the adjacent pair. Either endpoint can play the latter role. -/
theorem contact_profile (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {u v f a b z l : V} (uv : G.Adj u v) (du : G.degree u=2) (dv : G.degree v=2)
    (uf : u≠f) (vf : v≠f) (ear : G.neighborFinset f={a,b}) (ab : a≠b)
    (vz : G.Adj v z) (zu : z≠u) (dl : G.degree l≤1) (bad : bound G<gamma G) :
    let A : Finset V := {a,b}
    let W := (insert f A)ᶜ
    let H := (insert v ({u,z}:Finset V))ᶜ
    (W.filter (fun i => 0<nbr G i A)).card+(({z,l}:Finset V).filter (fun i => nbr G i A=0)).card≤11 ∧
    (H.filter (fun i => 0<nbr G i {u,z})).card+(if G.Adj u z then 1 else 0)+
      (if G.Adj z l then 0 else 1)≤11+nbr G z A := by
  classical
  let A : Finset V := {a,b}
  let W := (insert f A)ᶜ
  let H := (insert v ({u,z}:Finset V))ᶜ
  change _ ∧ (H.filter _).card+_+_≤11+nbr G z A
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
  have budget : (X.filter (fun i => 0<nbr G i J)).card≤9 := by
    apply Nat.le_of_not_gt; intro many
    have cap := Graffiti384b.Adjacent12.pool G n X O J xs (card_pair vf.symm) so (disjoint_left.mpr (fun _ m => xj m)) safe away
      xh (inj.mono (show (X:Set V)⊆high G from xh)) (fun i im => floor i (xh im)) many
    rw [bound,t,n] at bad; omega
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
  let hit := fun i => 0<nbr G i A
  have qx : (X.filter hit).card≤9 := (card_le_card (show X.filter hit⊆X.filter (fun i => 0<nbr G i J) from by
    intro i m
    exact mem_filter.mpr ⟨(mem_filter.mp m).1,(mem_filter.mp m).2.trans_le (card_le_card (filter_subset_filter _ (subset_insert ..)))⟩)).trans budget
  have zcount : nbr G z X≤9 := (card_le_card (show X.filter (G.Adj z)⊆X.filter (fun i => 0<nbr G i J) from by
    intro i m
    exact mem_filter.mpr ⟨(mem_filter.mp m).1,card_pos.mpr ⟨z,mem_filter.mpr ⟨mem_insert_self ..,(mem_filter.mp m).2.symm⟩⟩⟩)).trans budget
  constructor
  · have diff : W.filter hit\X.filter hit⊆D.filter hit := by
      intro i m
      obtain ⟨ih,nx⟩ := mem_sdiff.mp m
      obtain ⟨iw,h⟩ := mem_filter.mp ih
      have iwX : i∈W\X := mem_sdiff.mpr ⟨iw,fun ix => nx (mem_filter.mpr ⟨ix,h⟩)⟩
      have iu := eqU ▸ iwX
      refine mem_filter.mpr ⟨(mem_union.mp iu).resolve_left ?_,h⟩
      intro p; rcases mem_insert.mp p with rfl|k
      · exact peers uv.symm dv du vf uf h
      · exact peers uv du dv uf vf (mem_singleton.mp k ▸ h)
    have extra := card_le_card diff
    have ct := le_card_sdiff (X.filter hit) (W.filter hit)
    have both := filter_card_add_filter_neg_card_eq_card (s:=D) hit
    have miss : (D.filter (fun i => ¬hit i))=D.filter (fun i => nbr G i A=0) := by ext; simp [hit]
    rw [miss,zs] at both
    change (W.filter hit).card+(D.filter (fun i => nbr G i A=0)).card≤11
    omega
  · let VU := H.filter (G.Adj u)
    have remove : ∀ i∈H,i≠v ∧ i≠u ∧ i≠z := by
      intro i ih; simpa [H,not_or] using ih
    have uc : VU.card+(if G.Adj u z then 1 else 0)≤1 := by
      have vv : v∈G.neighborFinset u := (G.mem_neighborFinset ..).mpr uv
      have usub : VU⊆(G.neighborFinset u).erase v := fun i m =>
        mem_erase.mpr ⟨(remove i (mem_filter.mp m).1).1,(G.mem_neighborFinset ..).mpr (mem_filter.mp m).2⟩
      by_cases uz : G.Adj u z
      · have ze : z∈(G.neighborFinset u).erase v := mem_erase.mpr ⟨vz.ne.symm,(G.mem_neighborFinset ..).mpr uz⟩
        have lim := card_le_card (show VU⊆((G.neighborFinset u).erase v).erase z from
          fun i m => mem_erase.mpr ⟨(remove i (mem_filter.mp m).1).2.2,usub m⟩)
        rw [card_erase_of_mem ze,card_erase_of_mem vv,card_neighborFinset_eq_degree,du] at lim
        rw [if_pos uz]; omega
      · have lim := card_le_card usub
        rw [card_erase_of_mem vv,card_neighborFinset_eq_degree,du] at lim
        rw [if_neg uz]; omega
    let T := (X.filter (G.Adj z)∪A.filter (G.Adj z))∪({l}:Finset V).filter (G.Adj z)
    have znotf : ¬G.Adj z f := fun h => by
      have m := (G.mem_neighborFinset ..).mpr h.symm
      rw [ear] at m; exact za m
    have subHits : H.filter (fun i => 0<nbr G i {u,z})⊆VU∪T := by
      intro i im; obtain ⟨ih,c⟩ := mem_filter.mp im
      obtain ⟨j,jm⟩ := card_pos.mp c
      obtain ⟨jp,ij⟩ := mem_filter.mp jm
      rcases mem_insert.mp jp with rfl|p
      · exact mem_union_left _ (mem_filter.mpr ⟨ih,ij.symm⟩)
      rw [mem_singleton.mp p] at ij
      apply mem_union_right
      by_cases ix : i∈X
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨ix,ij.symm⟩))
      by_cases ia : i∈A
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨ia,ij.symm⟩))
      have iw := out (i:=i) (fun eq => znotf (eq ▸ ij.symm)) ia
      have iu : i∈U := eqU ▸ mem_sdiff.mpr ⟨iw,ix⟩
      have outside := remove i ih
      have il : i=l := by simpa [U,D,outside.1,outside.2.1,outside.2.2] using iu
      exact mem_union_right _ (mem_filter.mpr ⟨mem_singleton.mpr il,ij.symm⟩)
    have hm := (card_le_card subHits).trans (card_union_le ..)
    have tc := card_union_le (X.filter (G.Adj z)∪A.filter (G.Adj z)) (({l}:Finset V).filter (G.Adj z))
    have xc := card_union_le (X.filter (G.Adj z)) (A.filter (G.Adj z))
    change T.card≤_ at tc
    change (X.filter (G.Adj z)∪A.filter (G.Adj z)).card≤nbr G z X+nbr G z A at xc
    change _≤VU.card+T.card at hm
    by_cases edge : G.Adj z l <;> simp [filter_singleton,edge] at tc ⊢ <;> omega

end Graffiti384b.Adjacent12
#print axioms Graffiti384b.Adjacent12.contact_profile
