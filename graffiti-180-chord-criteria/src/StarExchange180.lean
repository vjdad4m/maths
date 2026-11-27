import Dominated180

set_option warningAsError true
namespace Assembly180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- Replace the parent of each graph neighbor of the root by the root.
The entire star becomes part of the tree and all other old leaves survive. -/
theorem full_star_exchange (T : SimpleGraph V) (sub : T ≤ G) (tr : T.IsTree)
    (hn : 1<Fintype.card V) (y : V) :
    ∃ K ≤ G, K.IsTree ∧ (∀ w, G.Adj y w → K.Adj y w) ∧
      ∀ v≠y, v∈leaves T → v∈leaves K := by
  classical
  let old (v : V) := if h : v≠y then (Graffiti169.exists_predecessor T tr.isConnected y v h).choose else y
  have spec (v : V) (ne : v≠y) : T.Adj v (old v) ∧ T.dist v y=T.dist (old v) y+1 := by
    simpa only [old,dif_pos ne] using (Graffiti169.exists_predecessor T tr.isConnected y v ne).choose_spec
  let p (v : V) := if G.Adj y v then y else old v
  have decrease (v : V) (ne : v≠y) : T.dist (p v) y < T.dist v y := by
    by_cases e : G.Adj y v
    · rw [show p v=y from if_pos e,dist_self]
      exact tr.isConnected.pos_dist_of_ne ne
    · rw [show p v=old v from if_neg e,(spec v ne).2]
      omega
  let K : SimpleGraph V :=
    { Adj := fun a b => (a≠y ∧ p a=b) ∨ (b≠y ∧ p b=a)
      symm := fun _ _ h => h.symm
      loopless := by
        rintro a (⟨ne,e⟩|⟨ne,e⟩) <;> have d := decrease a ne <;> rw [e] at d <;> omega }
  have conn : K.Connected := by
    apply (connected_iff_exists_forall_reachable _).mpr
    refine ⟨y,fun v => Reachable.symm ?_⟩
    induction d : T.dist v y using Nat.strong_induction_on generalizing v with
    | h k ih =>
      by_cases eq : v=y
      · subst v; exact .refl _
      · have e : K.Adj v (p v) := Or.inl ⟨eq,rfl⟩
        exact e.reachable.trans (ih _ (d ▸ decrease v eq) _ rfl)
  have tree : K.IsTree := by
    apply (isTree_iff_connected_and_card).mpr
    refine ⟨conn,le_antisymm ?_ conn.card_vert_le_card_edgeSet_add_one⟩
    let E := (univ.erase y).image (fun v => s(v,p v))
    have edges : K.edgeFinset ⊆ E := by
      intro e
      induction e using Sym2.ind with
      | _ a b =>
        intro h
        have h' : K.Adj a b := mem_edgeFinset.mp h
        rcases h' with ⟨ne,eq⟩|⟨ne,eq⟩
        · exact mem_image.mpr ⟨a,mem_erase.mpr ⟨ne,mem_univ _⟩,by rw [eq]⟩
        · exact mem_image.mpr ⟨b,mem_erase.mpr ⟨ne,mem_univ _⟩,by rw [eq,Sym2.eq_swap]⟩
    have bound := (card_le_card edges).trans card_image_le
    have count := card_erase_add_one (mem_univ y)
    rw [card_univ] at count
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← edgeFinset_card]
    omega
  have edge (v : V) (ne : v≠y) : G.Adj v (p v) := by
    by_cases e : G.Adj y v
    · exact (show p v=y from if_pos e) ▸ e.symm
    · exact (show p v=old v from if_neg e) ▸ sub (spec v ne).1
  refine ⟨K,?_,tree,fun w e => Or.inr ⟨e.ne.symm,if_pos e⟩,?_⟩
  · rintro a b (⟨ne,eq⟩|⟨ne,eq⟩)
    · exact eq ▸ edge a ne
    · exact eq ▸ (edge b ne).symm
  · intro v ne leaf
    have nochild (w : V) (ny : w≠y) (h : p w=v) : False := by
      by_cases e : G.Adj y w
      · rw [show p w=y from if_pos e] at h
        exact ne h.symm
      · rw [show p w=old w from if_neg e] at h
        have ew := (spec w ny).1
        rw [h] at ew
        have same := leaf_unique T leaf ew.symm (spec v ne).1
        have da := (spec v ne).2
        have db := (spec w ny).2
        rw [h] at db
        rw [← same] at da
        omega
    apply leaf_of_unique K conn hn
    intro a b ea eb
    have only {w} (h : K.Adj v w) : p v=w :=
      h.elim And.right (fun child => (nochild w child.1 child.2).elim)
    exact (only ea).symm.trans (only eb)

/-- An optimum with y internal exists exactly when y has two distinct
neighbors and its eligibility can be erased at zero cost. This also
handles vertices outside the marked set. -/
theorem internal_optimum_iff (hc : G.Connected) (hn : 1<Fintype.card V) (U : Finset V) (y : V) :
    (∃ K ≤ G, K.IsTree ∧ (U ∩ leaves K).card=weightedLeaves G U ∧ y∉leaves K) ↔
    (∃ a b, G.Adj y a ∧ G.Adj y b ∧ a≠b) ∧ weightedLeaves G (U.erase y)=weightedLeaves G U := by
  classical
  have mono : weightedLeaves G (U.erase y) ≤ weightedLeaves G U := by
    apply Finset.sup_le
    intro T ht
    exact (card_le_card (show U.erase y ∩ leaves T ⊆ U ∩ leaves T from fun _ h =>
      mem_inter.mpr ⟨mem_of_mem_erase (mem_inter.mp h).1,(mem_inter.mp h).2⟩)).trans
      (le_sup (f:=fun K => (U ∩ leaves K).card) ht)
  constructor
  · rintro ⟨K,ks,kt,eq,internal⟩
    refine ⟨?_,le_antisymm mono ?_⟩
    · apply Classical.byContradiction
      intro no
      exact internal (leaf_of_unique K kt.isConnected hn y (fun {a b} ea eb =>
        Classical.byContradiction (fun ne => no ⟨a,b,ks ea,ks eb,ne⟩)))
    · have bound : (U.erase y ∩ leaves K).card ≤ weightedLeaves G (U.erase y) :=
        le_sup (f:=fun T => (U.erase y ∩ leaves T).card) (mem_filter.mpr ⟨mem_univ _,ks,kt⟩)
      rwa [erase_inter,erase_eq_of_not_mem (fun h => internal (mem_inter.mp h).2),eq] at bound
  · rintro ⟨⟨a,b,ya,yb,ne⟩,same⟩
    obtain ⟨T,ts,tr,eq⟩ := tree_opt G hc (U.erase y)
    obtain ⟨K,ks,kt,star,keep⟩ := full_star_exchange G T ts tr hn y
    have sub : U.erase y ∩ leaves T ⊆ U ∩ leaves K := by
      intro v h
      obtain ⟨m,l⟩ := mem_inter.mp h
      exact mem_inter.mpr ⟨mem_of_mem_erase m,keep _ (mem_erase.mp m).1 l⟩
    have low := card_le_card sub
    rw [eq,same] at low
    refine ⟨K,ks,kt,le_antisymm ?_ low,fun yl => ne (leaf_unique K yl (star _ ya) (star _ yb))⟩
    exact le_sup (f:=fun J => (U ∩ leaves J).card) (mem_filter.mpr ⟨mem_univ _,ks,kt⟩)

#print axioms full_star_exchange
#print axioms internal_optimum_iff
end Assembly180
