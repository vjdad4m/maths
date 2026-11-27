import CubicPairReduction
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
variable {X : Set V} {z r a b : V}

def PrivateMissContact (G : SimpleGraph V) (X : Set V) (r : V) (u q : V) : Prop :=
  q ∈ X ∧ G.Adj r q ∧ G.Adj u q ∧ ∀ w ∈ Noncontacts G X r, G.Adj w q → w = u

private def missSuffix {I : Type*} (c d : I → V) (v : I → V) (t : I) : List I → List V
  | [] => [c t,v t]
  | j :: J => c j :: v j :: d j :: missSuffix c d v t J

omit [Fintype V] [DecidableEq V] in
private theorem mem_missSuffix {I : Type*} {c d v : I → V} {t : I} {w : V} (J : List I) :
    w ∈ missSuffix c d v t J ↔ w=c t ∨ w=v t ∨ ∃ j ∈ J, w=c j ∨ w=v j ∨ w=d j := by
  induction J with
  | nil => simp [missSuffix]
  | cons j J ih =>
    change w ∈ c j :: v j :: d j :: missSuffix c d v t J ↔ _
    rw [List.exists_mem_cons_iff]
    simp only [List.mem_cons,ih]
    simp only [or_assoc,or_left_comm,or_comm]

omit [Fintype V] [DecidableEq V] in
private theorem first_suffix {I : Type*} (c d v : I → V) (t : I) (J : List I) {w : V}
    (hw : w ∈ (missSuffix c d v t J).head?) : ∃ j ∈ t :: J, w = c j := by
  cases J with
  | nil => exact ⟨t,by simp,by simpa [missSuffix] using hw.symm⟩
  | cons j J => exact ⟨j,by simp,by simpa [missSuffix] using hw.symm⟩

omit [Fintype V] [DecidableEq V] in
private theorem last_suffix {I : Type*} (c d v : I → V) (t : I) (J : List I) :
    (missSuffix c d v t J).getLast? = some (v t) := by
  induction J with
  | nil => rfl
  | cons j J ih =>
    simp only [missSuffix,List.getLast?_cons_cons,List.getLast?_cons,ih,Option.getD_some]

/-- Choose two ordinary contacts for each miss from its own group. Completeness
between different groups permits concatenation in any order. -/
theorem SingletonCut.traceable_of_linked_miss_groups (F : SingletonCut G X z r a b)
    (K : Noncontacts G X r → Set V)
    (onGroup : ∀ i : Noncontacts G X r, ∀ q ∈ K i, q ∈ X ∧ G.Adj r q ∧ G.Adj i.val q)
    (wide : ∀ i, ∃ c ∈ K i, ∃ d ∈ K i, c ≠ d)
    (linked : ∀ i j, i ≠ j → ∀ u ∈ K i, ∀ w ∈ K j, G.Adj u w)
    {s t : V} (sm : s ∈ Noncontacts G X r) (tm : t ∈ Noncontacts G X r) (st : s ≠ t)
    (sa : G.Adj a s) (tb : G.Adj t b) : Traceable G := by
  classical
  let I := Noncontacts G X r
  let v : I → V := Subtype.val
  let mark (i : I) (q : V) := q ∈ X ∧ G.Adj r q ∧ G.Adj i.val q ∧ q ∈ K i
  choose c cK d dK different using wide
  have marks (i : I) (q : V) (qK : q ∈ K i) : mark i q := ⟨(onGroup i q qK).1,(onGroup i q qK).2.1,(onGroup i q qK).2.2,qK⟩
  have ci (i : I) := marks i _ (cK i)
  have di (i : I) := marks i _ (dK i)
  let l : I := ⟨s,sm⟩
  let k : I := ⟨t,tm⟩
  have lk : l ≠ k := fun eq => st (congrArg v eq)
  have cross {i j : I} (ij : i ≠ j) {u w : V}
      (ui : mark i u) (wj : mark j w) : G.Adj u w :=
    linked i j ij u ui.2.2.2 w wj.2.2.2
  have vc {i j : I} {q : V} (qj : mark j q) : v i ≠ q :=
    fun eq => i.property.2 (show G.Adj r (v i) by rw [eq]; exact qj.2.1)
  have outside {i j : I} (ij : i ≠ j) {u w : V}
      (ui : mark i u) (wj : mark j w) : u ≠ w :=
    (cross ij ui wj).ne
  let J := ((Finset.univ.erase l).erase k).toList
  have memJ (i : I) : i ∈ J ↔ i ≠ k ∧ i ≠ l := by simp [J]
  have jnd : J.Nodup := Finset.nodup_toList _
  have build (T : List I) (nd : T.Nodup) (off : k ∉ T) :
      (missSuffix c d v k T).Chain' G.Adj ∧ (missSuffix c d v k T).Nodup := by
    induction T with
    | nil => simp [missSuffix,List.chain'_cons,(show G.Adj (c k) (v k) from (ci k).2.2.1.symm),(vc (i:=k) (ci k)).symm]
    | cons j T ih =>
      have jk : j ≠ k := fun e => off (by simp [e])
      have jT := (List.nodup_cons.mp nd).1
      obtain ⟨tail,tn⟩ := ih (List.nodup_cons.mp nd).2 (fun h => off (List.mem_cons_of_mem _ h))
      have ej {q : V} (qj : mark j q) : q ∉ missSuffix c d v k T := by
        intro h
        rcases (mem_missSuffix T).mp h with h|h|⟨i,it,h|h|h⟩
        · exact outside jk qj (ci k) h
        · exact vc (i:=k) qj h.symm
        · exact outside (i:=j) (j:=i) (fun e => jT (e.symm ▸ it)) qj (ci i) h
        · exact vc (i:=i) qj h.symm
        · exact outside (i:=j) (j:=i) (fun e => jT (e.symm ▸ it)) qj (di i) h
      have oj : v j ∉ missSuffix c d v k T := by
        intro h
        rcases (mem_missSuffix T).mp h with h|h|⟨i,it,h|h|h⟩
        · exact vc (ci k) h
        · exact jk (Subtype.ext h)
        · exact vc (ci i) h
        · exact jT ((show j = i from Subtype.ext h).symm ▸ it)
        · exact vc (di i) h
      have next : (d j :: missSuffix c d v k T).Chain' G.Adj := tail.cons' (by
        intro w hw
        obtain ⟨i,im,rfl⟩ := first_suffix c d v k T hw
        exact cross (fun e => (List.mem_cons.mp im).elim (fun h => jk (e.trans h)) (fun h => jT (e.symm ▸ h))) (di j) (ci i))
      constructor
      · exact List.chain'_cons.mpr ⟨(ci j).2.2.1.symm,List.chain'_cons.mpr ⟨(di j).2.2.1,next⟩⟩
      · simp [missSuffix,(vc (i:=j) (ci j)).symm,vc (i:=j) (di j),different j,ej (ci j),ej (di j),oj,tn]
  have kJ : k ∉ J := fun h => ((memJ k).mp h).1 rfl
  obtain ⟨chain,nd⟩ := build J jnd kJ
  let U := missSuffix c d v k J
  let W := s :: c l :: U
  let M := {w : V | w ∈ W}
  have oni {i : I} (im : i ∈ J) : i ≠ l := ((memJ _).mp im).2
  have offLeft {q : V} (ql : mark l q) : q ∉ U := by
    intro h
    rcases (mem_missSuffix J).mp h with h|h|⟨i,it,h|h|h⟩
    · exact outside lk ql (ci k) h
    · exact vc (i:=k) ql h.symm
    · exact outside (oni it).symm ql (ci i) h
    · exact vc (i:=i) ql h.symm
    · exact outside (oni it).symm ql (di i) h
  have so : s ∉ U := by
    intro h
    rcases (mem_missSuffix J).mp h with h|h|⟨i,it,h|h|h⟩
    · exact vc (i:=l) (ci k) h
    · exact st h
    · exact vc (i:=l) (ci i) h
    · exact oni it (Subtype.ext h.symm)
    · exact vc (i:=l) (di i) h
  have first : (c l :: U).Chain' G.Adj := chain.cons' (by
    intro w hw
    obtain ⟨i,im,rfl⟩ := first_suffix c d v k J hw
    exact cross (fun e => (List.mem_cons.mp im).elim (fun h => lk (e.trans h)) (fun h => oni h e.symm)) (ci l) (ci i))
  have sc : s ≠ c l := vc (i:=l) (ci l)
  have ds : d l ≠ s := (vc (i:=l) (di l)).symm
  let P : PathOn G M := ⟨W,by simp [W],List.chain'_cons.mpr ⟨(ci l).2.2.1,first⟩,
    by simp [W,so,offLeft (ci l),sc,nd,U],fun _ => Iff.rfl⟩
  have sub : M ⊆ X := by
    intro w hw
    rcases List.mem_cons.mp hw with h|h
    · exact h.symm ▸ sm.1
    rcases List.mem_cons.mp h with h|h
    · exact h.symm ▸ (ci l).1
    rcases (mem_missSuffix J).mp h with h|h|⟨i,_,h|h|h⟩
    · exact h.symm ▸ (ci k).1
    · exact h.symm ▸ tm.1
    · exact h.symm ▸ (ci i).1
    · exact h.symm ▸ i.property.1
    · exact h.symm ▸ (di i).1
  have on (w : V) (hw : w ∈ X \ M) : G.Adj r w := by
    apply Classical.byContradiction
    intro n
    let i : I := ⟨w,hw.1,n⟩
    apply hw.2
    change w ∈ s :: c l :: U
    by_cases e : i=l
    · exact List.mem_cons.mpr (Or.inl (congrArg v e))
    apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
    apply (mem_missSuffix J).mpr
    by_cases f : i=k
    · exact Or.inr (Or.inl (congrArg v f))
    · exact Or.inr (Or.inr ⟨i,(memJ _).mpr ⟨f,e⟩,Or.inr (Or.inl rfl)⟩)
  have spare : d l ∉ M := by
    change d l ∉ s :: c l :: U
    simp [ds,(different l).symm,offLeft (di l)]
  have last : P.last = t := by
    have eq : P.vertices.getLast? = some t := by
      change (s :: c l :: U).getLast? = some (v k)
      simp only [List.getLast?_cons_cons,List.getLast?_cons,U,last_suffix,Option.getD_some]
    rw [List.getLast?_eq_getLast P.nonempty] at eq
    exact Option.some.inj eq
  exact F.traceable_of_reserved_edge sub on P sa (last.symm ▸ tb) (A:=[]) (B:=U) rfl sm.2
    ⟨d l,⟨(di l).1,spare⟩,(di l).2.2.1⟩ (Or.inl (ci l).2.1)

/-- Independent misses of arbitrary cardinality admit a spanning splice when
two distinct misses meet the outside ports and each miss has two ordinary
contacts private to it among all misses. -/
theorem SingletonCut.traceable_of_two_private_contacts_per_miss (F : SingletonCut G X z r a b)
    (ind : (Noncontacts G X r).Pairwise (fun u v => ¬ G.Adj u v))
    (wide : ∀ u ∈ Noncontacts G X r, ∃ q h : V, q ≠ h ∧ PrivateMissContact G X r u q ∧ PrivateMissContact G X r u h)
    {s t : V} (sm : s ∈ Noncontacts G X r) (tm : t ∈ Noncontacts G X r) (st : s ≠ t)
    (sa : G.Adj a s) (tb : G.Adj t b) : Traceable G := by
  classical
  let K (i : Noncontacts G X r) := {q | PrivateMissContact G X r i.val q}
  apply F.traceable_of_linked_miss_groups K (fun _ _ h => ⟨h.1,h.2.1,h.2.2.1⟩) ?_ ?_ sm tm st sa tb
  · intro i
    obtain ⟨q,h,qh,qi,hi⟩ := wide i.val i.property
    exact ⟨q,qi,h,hi,qh⟩
  · intro i j ij u ui w wj
    exact F.exclusive_contacts_complete i.property.1 j.property.1 (fun e => ij (Subtype.ext e)) i.property.2 j.property.2
      (ind i.property j.property (fun e => ij (Subtype.ext e))) ui.1 wj.1 ui.2.1 wj.2.1 ui.2.2.1
      (fun e => ij (Subtype.ext (ui.2.2.2 _ j.property e).symm)) wj.2.2.1
      (fun e => ij (Subtype.ext (wj.2.2.2 _ i.property e)))

#print axioms SingletonCut.traceable_of_linked_miss_groups
#print axioms SingletonCut.traceable_of_two_private_contacts_per_miss
end Graffiti199Depleted.Catalogue.Incomplete



