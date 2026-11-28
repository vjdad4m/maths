import UpperThirteen
namespace Graffiti384b.OddStars.MatchingSide
open Finset SimpleGraph ShorePairs
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The mates of the two distinguished vertices are isolated within the
four ordinary vertices. Only the other two ordinary vertices can be adjacent. -/
theorem mates {A : Finset V} {u v : V} (uv : u≠v) (ua : u∈A) (va : v∈A)
    (sep : ¬G.Adj u v) (thin : ∀x∈A,nbr G x A≤1)
    (um : nbr G u A=1) (vm : nbr G v A=1) :
    let U := A\{u,v}
    ∃p∈U,∃t∈U,p≠t ∧ G.Adj p u ∧ G.Adj t v ∧
      pairs G U⊆(U\{p,t}).powersetCard 2 := by
  classical
  let U := A\{u,v}
  have pick {a : V} (e : nbr G a A=1) : ∃p∈A,G.Adj a p := by
    obtain ⟨p,pm⟩ := card_pos.mp (show 0<(A.filter (G.Adj a)).card from by change 0<nbr G a A; omega)
    exact ⟨p,(mem_filter.mp pm).1,(mem_filter.mp pm).2⟩
  obtain ⟨p,pa,up⟩ := pick um
  obtain ⟨t,ta,vt⟩ := pick vm
  have pu : p∈U := mem_sdiff.mpr ⟨pa,by simp only [mem_insert,mem_singleton]; exact fun h => h.elim up.ne.symm (fun e => sep (e ▸ up))⟩
  have tu : t∈U := mem_sdiff.mpr ⟨ta,by simp only [mem_insert,mem_singleton]; exact fun h => h.elim (fun e => sep (e ▸ vt.symm)) vt.ne.symm⟩
  have unique {a b c : V} (h : a∈A) (hb : b∈A) (hc : c∈A) (ab : G.Adj a b) (ac : G.Adj a c) : b=c :=
    card_le_one.mp (thin a h) b (mem_filter.mpr ⟨hb,ab⟩) c (mem_filter.mpr ⟨hc,ac⟩)
  have pt : p≠t := fun e => uv (unique pa ua va up.symm (e.symm ▸ vt.symm))
  have exclude {i j : V} (im : i∈U) (jm : j∈U) (ij : G.Adj i j) : i∈U\{p,t} := by
    refine mem_sdiff.mpr ⟨im,?_⟩
    simp only [mem_insert,mem_singleton]
    rintro (rfl|rfl)
    · have e := unique pa (mem_sdiff.mp jm).1 ua ij up.symm
      exact (mem_sdiff.mp jm).2 (e ▸ mem_insert_self ..)
    · have e := unique ta (mem_sdiff.mp jm).1 va ij vt.symm
      exact (mem_sdiff.mp jm).2 (e ▸ mem_insert_of_mem (mem_singleton_self _))
  refine ⟨p,pu,t,tu,pt,up.symm,vt.symm,?_⟩
  intro k km
  obtain ⟨i,im,j,jm,ij,rfl⟩ := (pair_mem G).mp km
  exact mem_powersetCard.mpr ⟨insert_subset (exclude im jm ij) (singleton_subset_iff.mpr (exclude jm im ij.symm)),card_pair ij.ne⟩

/-- With at most one same-side neighbor, the score of b is at most the
number of edges on its ordinary opposite neighbors plus their cardinality. -/
theorem link_cap {A B U : Finset V} {b : V} (cover : G.neighborFinset b⊆A∪B)
    (dis : Disjoint A B) (ordinary : G.neighborFinset b∩A⊆U) (thin : nbr G b B≤1) :
    let R := G.neighborFinset b∩A
    trianglesAt G b≤(pairs G U).card+R.card := by
  classical
  let N := G.neighborFinset b
  let R := N∩A
  let L := N∩B
  have eq : R∪L=N := by
    ext w
    constructor
    · intro h; exact (mem_union.mp h).elim (fun m => (mem_inter.mp m).1) (fun m => (mem_inter.mp m).1)
    · intro h
      exact (mem_union.mp (cover h)).elim (fun a => mem_union_left _ (mem_inter.mpr ⟨h,a⟩))
        (fun a => mem_union_right _ (mem_inter.mpr ⟨h,a⟩))
  have mono : pairs G R⊆pairs G U := by
    intro k km
    obtain ⟨i,im,j,jm,e,rfl⟩ := (pair_mem G).mp km
    exact (pair_mem G).mpr ⟨i,ordinary im,j,ordinary jm,e,rfl⟩
  have low : L.card≤1 := by
    have eq : L=B.filter (G.Adj b) := by ext w; simp [L,N,and_comm]
    change (B.filter (G.Adj b)).card≤1 at thin
    rwa [eq]
  have score : trianglesAt G b=(pairs G N).card := rfl
  have em := card_le_card mono
  by_cases empty : L=∅
  · rw [empty,union_empty] at eq
    rw [←eq] at score
    change trianglesAt G b≤(pairs G U).card+R.card; omega
  obtain ⟨w,wL⟩ := card_eq_one.mp (by have := card_pos.mpr (nonempty_iff_ne_empty.mpr empty); omega : L.card=1)
  have wb := (mem_inter.mp (show w∈L from wL ▸ mem_singleton_self _)).2
  have out : w∉R := fun m => disjoint_left.mp dis (mem_inter.mp m).2 wb
  have n : N=insert w R := by rw [wL] at eq; rw [←eq]; ext y; simp; tauto
  rw [n,pairs_insert G out] at score
  have ub : nbr G w R≤R.card := card_filter_le ..
  change trianglesAt G b≤(pairs G U).card+R.card
  omega

/-- At half-size six, a score of five outside both cubic neighborhoods
forces a common neighbor of all four ordinary vertices and a mate for each. -/
theorem six_contact {A B : Finset V} (six : A.card=6) (dis : Disjoint A B)
    {u v : V} (uv : u≠v) (ua : u∈A) (va : v∈A) (sep : ¬G.Adj u v)
    (thin : ∀x∈A,nbr G x A≤1) (um : nbr G u A=1) (vm : nbr G v A=1)
    {b : V} (cover : G.neighborFinset b⊆A∪B) (outside : G.neighborFinset b∩A⊆A\{u,v})
    (other : nbr G b B≤1) (score : 5≤trianglesAt G b) :
    let U := A\{u,v}
    (pairs G U).card≤1 ∧ (∀x∈U,∃y∈A,G.Adj x y) ∧ ∀x∈U,G.Adj b x := by
  classical
  let U := A\{u,v}
  have ca : {u,v}⊆A := insert_subset ua (singleton_subset_iff.mpr va)
  have uc : U.card=4 := by dsimp [U]; rw [card_sdiff ca,six,card_pair uv]
  obtain ⟨p,pu,t,tu,pt,up,vt,allP⟩ := mates G uv ua va sep thin um vm
  let K := U\{p,t}
  have pc : {p,t}⊆U := insert_subset pu (singleton_subset_iff.mpr tu)
  have kc : K.card=2 := by dsimp [K]; rw [card_sdiff pc,uc,card_pair pt]
  have cap := card_le_card allP
  change (pairs G U).card≤(K.powersetCard 2).card at cap
  rw [card_powersetCard,kc] at cap
  have c : Nat.choose 2 2=1 := by decide
  let R := G.neighborFinset b∩A
  have link := link_cap G cover dis outside other
  change trianglesAt G b≤(pairs G U).card+R.card at link
  have rc := card_le_card outside
  change R.card≤U.card at rc
  have full : R=U := eq_of_subset_of_card_le outside (by omega)
  have non : (pairs G U).Nonempty := card_pos.mp (by omega)
  obtain ⟨z,zm⟩ := non
  obtain ⟨i,im,j,jm,ij,eq⟩ := (pair_mem G).mp zm
  have zK : z=K := eq_of_subset_of_card_le (mem_powersetCard.mp (allP zm)).1 (by rw [kc,(mem_powersetCard.mp (allP zm)).2])
  refine ⟨(show (pairs G U).card≤1 by omega),?_,?_⟩
  · intro x xm
    by_cases k : x∈K
    · have h : x∈({i,j}:Finset V) := eq ▸ zK.symm ▸ k
      rcases (by simpa only [mem_insert,mem_singleton] using h : x=i ∨ x=j) with rfl|rfl
      · exact ⟨j,(mem_sdiff.mp jm).1,ij⟩
      · exact ⟨i,(mem_sdiff.mp im).1,ij.symm⟩
    · have h : x∈({p,t}:Finset V) := by apply Classical.byContradiction; intro no; exact k (mem_sdiff.mpr ⟨xm,no⟩)
      rcases (by simpa only [mem_insert,mem_singleton] using h : x=p ∨ x=t) with rfl|rfl
      · exact ⟨u,ua,up⟩
      · exact ⟨v,va,vt⟩
  · intro x xm
    exact (G.mem_neighborFinset ..).mp (mem_inter.mp (show x∈R from full.symm ▸ xm)).1
end Graffiti384b.OddStars.MatchingSide
#print axioms Graffiti384b.OddStars.MatchingSide.mates
#print axioms Graffiti384b.OddStars.MatchingSide.link_cap
#print axioms Graffiti384b.OddStars.MatchingSide.six_contact
