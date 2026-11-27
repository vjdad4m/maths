import ResidualArms33

namespace Graffiti384b.ResidualShore
open Finset SimpleGraph OneEar
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
open private AnchorParity.initialPart from ParityAnchor33

private def snoc {v a b c : V} {n : ℕ} (s : Route G v a b n) (bc : G.Adj b c)
    (cv : c≠v) (fresh : ∀ i≤n,s.atIdx i≠c) : Route G v a c (n+1) where
  atIdx i := if i≤n then s.atIdx i else c
  start := by simp [s.start]
  finish := by simp
  step i hi := by
    rw [if_pos (by omega)]
    by_cases h : i<n
    · rw [if_pos (by omega)]; exact s.step i h
    · have eq : i=n := by omega
      subst i; simpa [s.finish] using bc
  unique i hi j hj h := by
    by_cases il : i≤n <;> by_cases jl : j≤n
    · rw [if_pos il,if_pos jl] at h; exact s.unique _ il _ jl h
    · rw [if_pos il,if_neg jl] at h; exact (fresh i il h).elim
    · rw [if_neg il,if_pos jl] at h; exact (fresh j jl h.symm).elim
    · omega
  avoid i hi := by split <;> first | exact cv | exact s.avoid i (by omega)

omit [DecidableEq V] in
private theorem longest {v r : V} {S : Finset V} (vs : v∉S) (rm : r∈S)
    (start : ∃ x∈S,G.Adj r x) :
    ∃ n,∃ t,∃ s : Route G v r t n, 0<n ∧ (∀ i≤n,s.atIdx i∈S) ∧
      ∀ y∈S,G.Adj t y → ∃ i<n,s.atIdx i=y := by
  classical
  let possible (n : ℕ) := ∃ t,∃ s : Route G v r t n,∀ i≤n,s.atIdx i∈S
  let O := (range (Fintype.card V+1)).filter possible
  have bound {n : ℕ} {t : V} (s : Route G v r t n) : n<Fintype.card V := by
    let f (i : Fin (n+1)) := s.atIdx i.val
    have inj : Function.Injective f := fun i j eq => Fin.ext (s.unique _ (by omega) _ (by omega) eq)
    have h := Fintype.card_le_of_injective f inj; rw [Fintype.card_fin] at h; omega
  obtain ⟨x,xm,rx⟩ := start
  let zero : Route G v r r 0 := ⟨fun _ => r,rfl,rfl,by omega,by omega,fun _ _ eq => vs (eq ▸ rm)⟩
  let one := snoc G zero rx (fun eq => vs (eq ▸ xm)) (fun _ _ => rx.ne)
  have oneMem : 1∈O := mem_filter.mpr ⟨mem_range.mpr (by have := bound one; omega),x,one,by
    intro i hi
    change (if i≤0 then r else x)∈S
    split <;> assumption⟩
  let n := O.max' ⟨1,oneMem⟩
  have existsn := (mem_filter.mp (max'_mem O ⟨1,oneMem⟩)).2
  obtain ⟨t,s,inside⟩ := existsn
  refine ⟨n,t,s,by have := le_max' O 1 oneMem; omega,inside,?_⟩
  intro y ym ty
  apply Classical.byContradiction; intro no
  have fresh (i : ℕ) (hi : i≤n) : s.atIdx i≠y := by
    intro eq; by_cases lt : i<n
    · exact no ⟨i,lt,eq⟩
    · have en : i=n := by omega
      subst i; exact ty.ne (s.finish.symm.trans eq)
  let ext := snoc G s ty (fun eq => vs (eq ▸ ym)) fresh
  have longer : n+1∈O := mem_filter.mpr ⟨mem_range.mpr (by have := bound ext; omega),y,ext,by
    intro i hi; change (if i≤n then s.atIdx i else y)∈S
    split <;> first | exact ym | exact inside i (by assumption)⟩
  have le : n+1≤n := le_max' O _ longer; omega

/-- A component incident to one ear endpoint supplies pins rooted there.
Any missing neighbor of an internal vertex must be the other endpoint.
Odd parity of the routes between the endpoints resolves that boundary loss. -/
theorem shore_arm {v r b : V} {S : Finset V} (vs : v∉S) (bs : b∉S) (bv : b≠v)
    (rm : r∈S) (start : ∃ x∈S,G.Adj r x)
    (closed : ∀ t∈S,t≠r → ∀ y,G.Adj t y → y∈S ∨ y=b)
    (minimum : ∀ t∈S,t≠r → 3≤G.degree t)
    (odd : ∀ l,Route G v r b l → l%2=1) : ∃ P Q,Arm G r S P Q := by
  classical
  obtain ⟨n,t,s,pos,inside,endp⟩ := longest G vs rm start
  have tr : t≠r := fun eq => by
    have h := s.unique n le_rfl 0 (by omega) (s.finish.trans (eq.trans s.start.symm)); omega
  have tm : t∈S := s.finish ▸ inside n le_rfl
  let I := (range n).filter (fun i => G.Adj t (s.atIdx i))
  have idx {i : ℕ} (im : i∈I) : i<n ∧ G.Adj t (s.atIdx i) :=
    ⟨mem_range.mp (mem_filter.mp im).1,(mem_filter.mp im).2⟩
  have inI {y : V} (ym : y∈S) (ty : G.Adj t y) : y∈I.image s.atIdx := by
    obtain ⟨i,il,eq⟩ := endp y ym ty
    exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr il,eq ▸ ty⟩,eq⟩
  have deg := minimum t tm tr
  have size := card_image_le (s:=I) (f:=s.atIdx)
  have pair : ∃ i∈I,∃ j∈I,i≠j ∧ i%2=j%2 := by
    by_cases adj : G.Adj t b
    · have sub : G.neighborFinset t⊆insert b (I.image s.atIdx) := by
        intro y my; have ty := (G.mem_neighborFinset _ _).mp my
        exact (closed t tm tr y ty).elim (fun m => mem_insert_of_mem (inI m ty)) (fun eq => eq ▸ mem_insert_self ..)
      have upper := card_le_card sub; rw [card_neighborFinset_eq_degree] at upper
      have h := card_insert_le b (I.image s.atIdx)
      obtain ⟨i,im,j,jm,ne⟩ := one_lt_card.mp (show 1<I.card by omega)
      have oddIndex (k : ℕ) (km : k∈I) : k%2=1 := by
        obtain ⟨kn,tk⟩ := idx km
        let pre := AnchorParity.initialPart s k (by omega)
        let tip := snoc G pre tk.symm (s.finish ▸ s.avoid n le_rfl) (by
          intro u hu eq
          have := s.unique u (by omega) n le_rfl (eq.trans s.finish.symm); omega)
        let walk := snoc G tip adj bv (by
          intro u hu eq; apply bs
          change (if u≤k then s.atIdx u else t)=b at eq
          rw [← eq]; split <;> first | exact tm | exact inside u (by omega))
        have val := odd (k+1+1) walk; omega
      exact ⟨i,im,j,jm,ne,(oddIndex i im).trans (oddIndex j jm).symm⟩
    · have sub : G.neighborFinset t⊆I.image s.atIdx := by
        intro y my; have ty := (G.mem_neighborFinset _ _).mp my
        exact inI ((closed t tm tr y ty).resolve_right (fun eq => adj (eq ▸ ty))) ty
      have upper := card_le_card sub; rw [card_neighborFinset_eq_degree] at upper
      exact exists_ne_map_eq_of_card_lt_of_maps_to (f:=fun k : ℕ => k%2) (t:=range 2)
        (by rw [card_range]; omega) (fun k _ => mem_range.mpr (Nat.mod_lt k (by decide)))
  obtain ⟨i,im,j,jm,ne,same⟩ := pair
  rcases lt_or_gt_of_ne ne with lt|gt
  · exact fork_arm G s lt (idx jm).1 same (idx im).2 (idx jm).2 inside
  · exact fork_arm G s gt (idx im).1 same.symm (idx jm).2 (idx im).2 inside

end Graffiti384b.ResidualShore
#print axioms Graffiti384b.ResidualShore.shore_arm
