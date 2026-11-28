import SmallPalette384b
import OddQuota384b

namespace Graffiti384b.SmallPalette
open Finset SimpleGraph
open private Prune.outside_zero from Prune384b

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def graphPalette {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset Nat :=
  (univ.filter fun v=>0<trianglesAt G v).image (trianglesAt G)

theorem graphPalette_transfer {n : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : Fin n ≃ V) (E : Rel n)
    (hs : ∀ i, score E i = trianglesAt G (e i)) : palette E = graphPalette G := by
  ext q
  constructor
  · intro hm
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hm
    exact mem_image.mpr ⟨e i, by simpa only [mem_filter,mem_univ,true_and,←hs i] using hi, (hs i).symm⟩
  · intro hm
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hm
    obtain ⟨i,rfl⟩ := e.surjective v
    exact mem_image.mpr ⟨i, by simpa only [mem_filter,mem_univ,true_and,hs i] using hv, hs i⟩

theorem two_large_scores {n : Nat} (small : 2≤n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (six : 6≤(graphPalette G).card) :
    ∃ x y : Fin n, x≠y ∧ 5≤trianglesAt G x ∧ 5≤trianglesAt G y := by
  let z : Fin n := ⟨0,by omega⟩
  obtain ⟨x,_,mx⟩ := exists_max_image (univ : Finset (Fin n)) (trianglesAt G) ⟨z,mem_univ _⟩
  let S := (univ : Finset (Fin n)).erase x
  have sz : S.card=n-1 := by simp [S]
  obtain ⟨y,hy,my⟩ := exists_max_image S (trianglesAt G) (card_pos.mp (by omega))
  have ne : x≠y := (mem_erase.mp hy).1.symm
  let I := Icc 1 (trianglesAt G y)
  have sub : graphPalette G ⊆ insert (trianglesAt G x) I := by
    intro q hq
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hq
    by_cases e : v=x
    · simp [e]
    · apply mem_insert_of_mem
      exact mem_Icc.mpr ⟨(mem_filter.mp hv).2, my _ (mem_erase.mpr ⟨e,mem_univ _⟩)⟩
  have q := card_le_card sub
  have ine := card_insert_le (trianglesAt G x) I
  have ic : I.card=trianglesAt G y := by simp [I,Nat.card_Icc]
  have y5 : 5≤trianglesAt G y := by omega
  exact ⟨x,y,ne,y5.trans (mx y (mem_univ _)),y5⟩

theorem four_degree {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {v : V} (s : 5≤trianglesAt G v) : 4≤G.degree v := by
  have t : trianglesAt G v≤(G.degree v).choose 2 := by
    unfold trianglesAt
    exact (card_filter_le _ _).trans_eq (by rw [card_powersetCard,card_neighborFinset_eq_degree])
  by_contra! hd
  have h := Nat.choose_le_choose 2 (show G.degree v≤3 by omega)
  have th : (3:Nat).choose 2=3 := by decide
  omega

def QuadOmit {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) : Prop :=
  S.card=4 ∧ ∀ v∈S,
    (∃ x y, x∉S ∧ y∉S ∧ x≠y ∧ G.Adj v x ∧ G.Adj v y) ∨
    (∀ w∈S, ¬ G.Adj v w)

theorem common_quad {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (ne : x≠y)
    (many : 4≤(G.neighborFinset x∩G.neighborFinset y).card) :
    ∃ S, QuadOmit G S := by
  obtain ⟨S,sub,sz⟩ := exists_subset_card_eq many
  have eo (v : V) (hv : v∈S) := mem_inter.mp (sub hv)
  have xn : x∉S := fun hx=>G.loopless x ((G.mem_neighborFinset _ _).mp (eo x hx).1)
  have yn : y∉S := fun hy=>G.loopless y ((G.mem_neighborFinset _ _).mp (eo y hy).2)
  exact ⟨S,sz,fun v hv=>Or.inl ⟨x,y,xn,yn,ne,
    ((G.mem_neighborFinset _ _).mp (eo v hv).1).symm,((G.mem_neighborFinset _ _).mp (eo v hv).2).symm⟩⟩

theorem effective_to_omit {n : Nat} {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (p : Fin n ↪ V) (E : Rel n)
    (fit : ∀ i j,E i j=true↔G.Adj (p i) (p j))
    {a b c d : Fin n} (eff : Effective E E a b c d) :
    QuadOmit G ((O4 a b c d).map p) := by
  refine ⟨by simpa using eff.1,?_⟩
  intro x hx
  obtain ⟨v,hv,rfl⟩ := mem_map.mp hx
  rcases eff.2 v hv with ⟨u,w,un,wn,ne,vu,vw⟩ | dis
  · apply Or.inl
    refine ⟨p u,p w,?_,?_,fun e=>ne (p.injective e),(fit _ _).mp vu,(fit _ _).mp vw⟩
    · intro h
      obtain ⟨j,hj,e⟩ := mem_map.mp h
      exact un (p.injective e ▸ hj)
    · intro h
      obtain ⟨j,hj,e⟩ := mem_map.mp h
      exact wn (p.injective e ▸ hj)
  · apply Or.inr
    intro w hw ad
    obtain ⟨u,hu,rfl⟩ := mem_map.mp hw
    have e := (fit _ _).mpr ad
    rw [dis u hu] at e
    contradiction

theorem lift_quad {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (h : QuadOmit G S) (nl : S⊆nonleaves G) : gamma G≤Fintype.card V-4 := by
  have sz : Sᶜ.card=Fintype.card V-4 := by rw [card_compl,h.1]
  refine Nat.sInf_le ⟨Sᶜ,?_,sz⟩
  intro v hv
  have vs : v∈S := by simpa using hv
  rcases h.2 v vs with ⟨x,y,xn,yn,ne,ax,ay⟩|dis
  · have sub : ({x,y}:Finset V)⊆Sᶜ.filter (G.Adj v) :=
      insert_subset (mem_filter.mpr ⟨mem_compl.mpr xn,ax⟩)
        (singleton_subset_iff.mpr (mem_filter.mpr ⟨mem_compl.mpr yn,ay⟩))
    simpa only [card_pair ne] using card_le_card sub
  · have sub : G.neighborFinset v⊆Sᶜ.filter (G.Adj v) := by
      intro w hw
      have a := (G.mem_neighborFinset _ _).mp hw
      exact mem_filter.mpr ⟨mem_compl.mpr (fun ws => dis _ ws a),a⟩
    have deg : 2≤G.degree v := (mem_filter.mp (nl vs)).2
    exact deg.trans ((card_neighborFinset_eq_degree G v) ▸ card_le_card sub)

private def links {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (w : W) :=
  ((H.neighborFinset w).powersetCard 2).filter
    (fun p => ∀ x ∈ p, ∀ y ∈ p, x ≠ y → H.Adj x y)

private theorem mem_links {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (w : W) (p : Finset W) :
    p∈links H w ↔ p.card=2 ∧ (∀ x∈p, H.Adj w x) ∧
      (∀ x∈p, ∀ y∈p, x≠y → H.Adj x y) := by
  simp only [links, mem_filter, mem_powersetCard, Finset.subset_iff, mem_neighborFinset]
  tauto

private theorem map_links {W X : Type*} [Fintype W] [Fintype X] [DecidableEq W] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj] (e : W ≃ X) (w : W) :
    (links (H.comap e) w).image (Finset.map e.toEmbedding) = links H (e w) := by
  ext p; constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    obtain ⟨two,nei,adj⟩ := (mem_links _ _ _).mp hq
    apply (mem_links _ _ _).mpr
    refine ⟨by simpa using two,?_,?_⟩
    · intro x hx
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      exact nei a ha
    · intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
      exact adj a ha b hb (fun h => hxy (congrArg e h))
  · intro hp
    obtain ⟨two,nei,adj⟩ := (mem_links _ _ _).mp hp
    have hm : (p.map e.symm.toEmbedding).map e.toEmbedding = p := by simp [Finset.map_map]
    refine mem_image.mpr ⟨p.map e.symm.toEmbedding,?_,hm⟩
    apply (mem_links _ _ _).mpr
    refine ⟨by simpa using two,?_,?_⟩
    · intro x hx
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      change H.Adj (e w) (e (e.symm a))
      simpa using nei a ha
    · intro x hx y hy hxy
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hy
      change H.Adj (e (e.symm a)) (e (e.symm b))
      simpa using adj a ha b hb (fun h => hxy (congrArg e.symm h))

theorem triangle_comap {W X : Type*} [Fintype W] [Fintype X] [DecidableEq W] [DecidableEq X]
    (H : SimpleGraph X) [DecidableRel H.Adj] (e : W ≃ X) (w : W) :
    trianglesAt (H.comap e) w = trianglesAt H (e w) := by
  change (links (H.comap e) w).card = (links H (e w)).card
  rw [← map_links H e w, card_image_of_injective _ (Finset.map_injective e.toEmbedding)]


theorem nonleaf_model {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n : Nat}
    (size : (nonleaves G).card=n) (div : 7≤(types G).card)
    (core : ∀ (H : SimpleGraph (Fin n)) (dh : DecidableRel H.Adj),
      letI := dh
      6≤(graphPalette H).card → ∃ S, QuadOmit H S) :
    gamma G≤Fintype.card V-4 := by
  let P := nonleaves G
  let H := G.induce (P : Set V)
  let e : Fin n ≃ P := (Fintype.equivFinOfCardEq (Fintype.card_coe P |>.trans size)).symm
  let J := H.comap (e : Fin n→P)
  let dj : DecidableRel J.Adj := inferInstanceAs (DecidableRel (H.comap (e : Fin n→P)).Adj)
  letI := dj
  have preserved (v : Fin n) : trianglesAt J v = trianglesAt G (e v).val := by
    change trianglesAt (H.comap e) v = _
    rw [triangle_comap]
    exact Prune.counts_preserved G P Subset.rfl (e v)
  have incl : types G ⊆ insert 0 (graphPalette J) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := mem_image.mp ha
    by_cases vp : v∈P
    · obtain ⟨u,eu⟩ := e.surjective ⟨v,vp⟩
      have eq : trianglesAt J u = trianglesAt G v := by simp [preserved u,eu]
      by_cases z : trianglesAt G v=0
      · simp [z]
      · apply mem_insert_of_mem
        exact mem_image.mpr ⟨u,mem_filter.mpr ⟨mem_univ _,by omega⟩,eq⟩
    · simp [Prune.outside_zero G vp]
  have le := card_le_card incl
  have le' := card_insert_le 0 (graphPalette J)
  obtain ⟨S,hs⟩ := core J dj (by omega)
  let f : Fin n ↪ V := e.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  have out (i j : Fin n) : J.Adj i j ↔ G.Adj (f i) (f j) := Iff.rfl
  let T := S.map f
  have bij (i : Fin n) : f i∈T ↔ i∈S := by simp [T]
  have q : QuadOmit G T := by
    refine ⟨by simpa [T] using hs.1,?_⟩
    intro v hv
    obtain ⟨i,ih,rfl⟩ := mem_map.mp hv
    rcases hs.2 i ih with ⟨a,b,an,bn,ne,ad,bd⟩|none
    · exact Or.inl ⟨f a,f b,fun h=>an ((bij a).mp h),
        fun h=>bn ((bij b).mp h),fun h=>ne (f.injective h),(out _ _).mp ad,(out _ _).mp bd⟩
    · apply Or.inr
      intro w hw a
      obtain ⟨j,jh,rfl⟩ := mem_map.mp hw
      exact none j jh ((out _ _).mpr a)
  exact lift_quad G T q (by
    intro v hv
    obtain ⟨i,_,rfl⟩ := mem_map.mp hv
    exact (e i).property)

theorem nonleaf_at_least_six {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (div : 7≤(types G).card) :
    6≤(nonleaves G).card := by
  have cover : types G⊆insert 0 ((nonleaves G).image (trianglesAt G)) := by
    intro a ha
    obtain ⟨v,_,rfl⟩ := mem_image.mp ha
    by_cases vp : v∈nonleaves G
    · exact mem_insert_of_mem (mem_image_of_mem _ vp)
    · simp [Prune.outside_zero G vp]
  have co := card_le_card cover
  have z := card_insert_le 0 ((nonleaves G).image (trianglesAt G))
  have i : ((nonleaves G).image (trianglesAt G)).card≤(nonleaves G).card := card_image_le
  omega

#print axioms nonleaf_model
end Graffiti384b.SmallPalette
