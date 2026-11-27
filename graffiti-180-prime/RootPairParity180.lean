import PinnedPrime180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem pinned_down (G : SimpleGraph V) (r : V) (p : Bool) (A B : Finset V) (ab : A⊆B)
    (up : Pinned G r p B (B∩parity G r p)) : Pinned G r p A (A∩parity G r p) := by
  classical
  let P := parity G r p
  let U := eligible A P r
  let W := eligible B P r
  obtain ⟨Z,col,keep,ok⟩ := up
  refine ⟨Z,col,?_,?_⟩
  · exact fun x xm => keep (mem_inter.mpr ⟨ab (mem_inter.mp xm).1,(mem_inter.mp xm).2⟩)
  · have inc : W\U⊆B\A := by
      intro x xm
      obtain ⟨wx,no⟩ := mem_sdiff.mp xm
      have w := eligible_iff.mp wx
      have xa : x∉A := by
        intro m; apply no (eligible_iff.mpr ⟨Or.inl m,?_⟩)
        by_cases xr : x=r
        · obtain ⟨_,rp⟩ := w.2.resolve_left (not_not.mpr xr)
          exact Or.inr ⟨xr ▸ m,rp⟩
        · exact Or.inl xr
      refine mem_sdiff.mpr ⟨?_,xa⟩
      by_contra xb
      have xp := w.1.resolve_left xb
      have xr : x≠r := by
        intro e
        obtain ⟨rb,_⟩ := w.2.resolve_left (not_not.mpr e)
        exact xb (e ▸ rb)
      exact no (eligible_iff.mpr ⟨Or.inr xp,Or.inl xr⟩)
    have bound := restrict_leaves G W U
    have size := card_le_card inc
    have cnt := card_sdiff_add_card_eq_card ab
    change 1+B.card+P.card≤weightedLeaves G W+Z.card at ok
    change 1+A.card+P.card≤weightedLeaves G U+Z.card
    omega

/-- A two-element root module in an induced-minimal failed pinned test
must be an adjacent true-twin pair, with odd parity. The twin away from
the root belongs to the independent marking. -/
theorem min_pair_odd (H : SimpleGraph V) (hc : H.Connected) (high : 2<Fintype.card V)
    (min : SmallerPinned H) (r y : V) (ry : r≠y) (hom : Homogeneous H {r,y}) (proper : ({r,y}:Finset V)≠univ)
    (p : Bool) (A : Finset V) (ai : Indep H A) (bad : ¬Pinned H r p A (A∩parity H r p)) :
    H.Adj r y ∧ p=true ∧ y∈A := by
  classical
  let M : Finset V := {r,y}
  have rm : r∈M := by simp [M]
  have ym : y∈M := by simp [M]
  have fat : 1<M.card := by simp [M,ry]
  have h := module_bags H M hom y ym
  have jc := quotient_connected H hc M hom y ym
  have ord := (quotient_order M y ym fat proper).1
  have mate := members_same M y y r ym rm
  have stuck (B : Finset V) (ii : Indep H B) (no : ¬Pinned H r p B (B∩parity H r p))
      (step : y∈B∩parity H r p → ∃ t∈B∩parity H r p,FalseTwins H y t) : False := by
    obtain ⟨con,large,small,ind,fail⟩ := h.pinDelete jc ord high B ii r y r ry.symm ry.symm mate p step no
    exact fail (min _ small large con _ p _ ind)
  have yd : y∈A∩parity H r p := by
    by_contra no
    exact stuck A ai bad (fun m => (no m).elim)
  have ya := (mem_inter.mp yd).1
  have par := (mem_parity H r y p).mp (mem_inter.mp yd).2
  have adj : H.Adj r y := by
    by_contra non
    have tw : FalseTwins H y r := by
      refine ⟨ry.symm,fun z => ?_⟩
      by_cases zr : z=r
      · subst z; simp [non,adj_comm]
      by_cases zy : z=y
      · subst z; simp [non]
      have out : z∉M := by simp [M,zr,zy]
      exact ⟨fun e => ((hom z out y ym r rm).mp e.symm).symm,fun e => ((hom z out y ym r rm).mpr e.symm).symm⟩
    have two : H.dist y r=2 := by simpa [mate,ry.symm,show ¬H.Adj y r from fun e => non e.symm] using h.metric jc ord y r
    have even : p=false := by rw [two] at par; cases p <;> simp_all
    have rp : r∈parity H r p := by simp [even,dist_self]
    have noEdge (z : V) (zm : z∈A) : ¬H.Adj r z := fun e =>
      let a := (tw.2 z).mpr e
      ai _ ya _ zm a.ne a
    have plus : Indep H (insert r A) := by
      intro a am b bm ne edge
      rcases mem_insert.mp am with ar|aa <;> rcases mem_insert.mp bm with br|ba
      · exact ne (ar.trans br.symm)
      · exact noEdge b ba (ar ▸ edge)
      · exact noEdge a aa (br ▸ edge.symm)
      · exact ai a aa b ba ne edge
    exact stuck (insert r A) plus (fun up => bad (pinned_down H r p A _ (subset_insert ..) up))
      (fun _ => ⟨r,mem_inter.mpr ⟨mem_insert_self ..,rp⟩,tw⟩)
  rw [dist_eq_one_iff_adj.mpr adj.symm] at par
  exact ⟨adj,by cases p <;> simp_all,ya⟩

#print axioms pinned_down
#print axioms min_pair_odd
end Minimal180.Substitution
