import CorePayment180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The root and its partner form a connected dominating set. -/
def DomEdge (G : SimpleGraph V) (r y : V) : Prop :=
  G.Adj r y ∧ ∀ x,x≠r → x≠y → G.Adj x r ∨ G.Adj x y

theorem pair_pay (G : SimpleGraph V) {r y : V} (h : DomEdge G r y) (A P : Finset V)
    (pay : 1+(A∩P).card+(if r∈A∪P then 1 else 0)+(if y∈A∪P then 1 else 0)≤bipartiteNum G) :
    1+A.card+P.card≤weightedLeaves G (eligible A P r)+bipartiteNum G := by
  classical
  have con : Con G {r,y} := con_insert G (con_single G y) (mem_singleton_self _) h.1
  refine core_payment G r A P {r,y} con ?_ (Or.inl (mem_insert_self ..)) ?_
  · intro x out
    have nn : x≠r ∧ x≠y := by simpa using out
    rcases h.2 x nn.1 nn.2 with e|e
    · exact ⟨r,by simp,e⟩
    · exact ⟨y,by simp,e⟩
  · have count : ∀ S : Finset V,(S∩{r,y}).card=(if r∈S then 1 else 0)+(if y∈S then 1 else 0) := by
      intro S
      rw [inter_comm,←filter_mem_eq_inter]
      by_cases rr : r∈S <;> by_cases yy : y∈S <;> simp [filter_insert,filter_singleton,rr,yy,h.1.ne]
    rw [count]; omega

theorem universal_root (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (un : Universal G r) (p : Bool) : localBound G r (parity G r p) := by
  classical
  intro A ai
  have zero : parity G r false={r} := by
    ext x; by_cases eq : x=r
    · subst x; simp [dist_self]
    · simp [mem_parity,dist_eq_one_iff_adj.mpr (un x eq),eq]
  have cap := basic_bipartite G hn
  have rc (ra : r∈A) : A={r} := by
    ext x
    simp only [mem_singleton]
    exact ⟨fun h => Classical.byContradiction (fun ne => ai _ h _ ra ne (un x ne)),fun eq => eq ▸ ra⟩
  cases p with
  | false =>
    rw [zero]
    by_cases ra : r∈A
    · rw [rc ra]
      by_cases high : 3≤bipartiteNum G
      · apply universal_pay G un _ _ (Or.inl rfl); simpa using high
      · obtain ⟨y,ry⟩ := exists_adj G gc hn r
        have uy := rank_small_complete G gc hn (by omega) y
        apply universal_pay G uy _ _ (Or.inr (Or.inl (by simp)))
        simpa [ry.ne.symm] using cap
    · apply universal_pay G un _ _ (Or.inl rfl)
      simpa [inter_singleton_of_not_mem ra] using cap
  | true =>
    let P := parity G r true
    have rp : r∉P := by simp [P,dist_self]
    have si : Indep G (A∩P) := fun x hx y hy => ai x (mem_inter.mp hx).1 y (mem_inter.mp hy).1
    apply universal_pay G un A P (Or.inl rfl)
    by_cases ra : r∈A
    · rw [rc ra]; simpa [rp] using cap
    · have g := one_credit G si (u:=r) (by simp [rp])
      simp [ra,rp]; omega

theorem dom_odd (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    {r y : V} (h : DomEdge G r y) : localBound G r (parity G r true) := by
  classical
  by_cases un : Universal G r
  · exact universal_root G gc hn r un true
  obtain ⟨z,zr,absent⟩ : ∃ z,z≠r ∧ ¬G.Adj z r := by simpa [Universal] using un
  let P := parity G r true
  have rp : r∉P := by simp [P,dist_self]
  have two : G.dist z r=2 := by
    have zy := (h.2 z zr (fun eq => absent (eq ▸ h.1.symm))).resolve_left absent
    have up := gc.dist_triangle (u:=z) (v:=y) (w:=r)
    rw [dist_eq_one_iff_adj.mpr zy,dist_eq_one_iff_adj.mpr h.1.symm] at up
    have pos := gc.pos_dist_of_ne zr
    have ne := mt dist_eq_one_iff_adj.mp absent
    omega
  have zp : z∉P := by simp [P,mem_parity,two]
  have high : 3≤bipartiteNum G := by
    by_contra! low; exact un (rank_small_complete G gc hn low r)
  intro A ai
  have si : Indep G (A∩P) := fun x hx y hy => ai x (mem_inter.mp hx).1 y (mem_inter.mp hy).1
  apply pair_pay G h A P
  by_cases ra : r∈A
  · have empty : A∩P=∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro x hx
      have ap := (mem_inter.mp hx).2
      have ne : x≠r := fun eq => rp (eq ▸ ap)
      have non : ¬G.Adj x r := ai _ (mem_inter.mp hx).1 _ ra ne
      have xy := (h.2 x ne (fun eq => non (eq ▸ h.1.symm))).resolve_left non
      have up := gc.dist_triangle (u:=x) (v:=y) (w:=r)
      rw [dist_eq_one_iff_adj.mpr xy,dist_eq_one_iff_adj.mpr h.1.symm] at up
      have diff := mt dist_eq_one_iff_adj.mp non
      have := gc.pos_dist_of_ne ne
      change x∈parity G r true at ap
      simp only [mem_parity,Bool.toNat_true] at ap
      omega
    rw [empty,card_empty]; split_ifs <;> omega
  · have b := pair_credit G si zr absent (by simp [zp]) (by simp [rp])
    simp only [mem_union,ra,rp,or_self,if_false,add_zero]
    split_ifs <;> omega

#print axioms universal_root
#print axioms dom_odd
end Minimal180.Substitution
