import P8ModelLift133
import Mathlib.Data.Fin.VecNotation

namespace Graffiti133Eighth
open SimpleGraph Graffiti133 Graffiti133NoFive Graffiti133P8Heawood Finset
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
private abbrev Ring : Fin 8 → Fin 8 → Prop := Cyclic
def OctWide (i j : Fin 8) : Prop := j=i+3 ∨ j=i+4 ∨ j=i+5
instance : DecidableRel OctWide := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
private def One (i k : Fin 8) : Bool := decide (k=i)
private def Two (i j k : Fin 8) : Bool := decide (k=i ∨ k=j)
private lemma common : ∀ i j : Fin 8, i≠j → ¬Ring i j → ¬OctWide i j →
    ∃ k,Ring i k ∧ Ring j k := by decide
private lemma noTri : ∀ i j k : Fin 8, Ring i j → Ring i k → Ring j k → False := by decide
private lemma sides : ∀ i j : Fin 8, Ring i j → j=i+1 ∨ j=i+7 := by decide
private def plus (i : Fin 8) : Fin 8 → Fin 9 :=
  ![Fin.last 8,i.castSucc,(i+1).castSucc,(i+2).castSucc,(i+3).castSucc,
    (i+4).castSucc,(i+5).castSucc,(i+6).castSucc]
private def minus (i : Fin 8) : Fin 8 → Fin 9 :=
  ![Fin.last 8,i.castSucc,(i+7).castSucc,(i+6).castSucc,(i+5).castSucc,
    (i+4).castSucc,(i+3).castSucc,(i+2).castSucc]
private lemma p1 : ∀ i, (Cert.eight (plus i)).Valid (ext Ring (One i)) False := by decide
private lemma p2 : ∀ i, (Cert.eight (minus i)).Valid (ext Ring (Two i (i+1))) False := by decide
private lemma p3 : ∀ i, (Cert.eight (plus i)).Valid (ext Ring (Two i (i+7))) False := by decide

variable {V : Type*} [Fintype V] {G : SimpleGraph V}
private def wideModel (H : Hole G 8) : Model G (@Cyclic 8) :=
  ⟨H.c,H.inj,fun i j => (H.adj i j).symm⟩
theorem outside_octagon_wide_pair (H : Hole G 8) (h4 : FourCycleFree G)
    (h8 : ¬∃ p : Fin 8 → V, InducedPath G p)
    {x : V} (out : Outside H.c x) (contact : ∃ i, G.Adj x (H.c i)) :
    ∃ i j, OctWide i j ∧ G.Adj x (H.c i) ∧ G.Adj x (H.c j) := by
  classical
  apply Classical.byContradiction
  intro no
  let M := wideModel H
  let b := M.contacts x
  have tr (i) : b i=true ↔ G.Adj x (H.c i) := M.contacts_true x i
  have narrow (i j : Fin 8) (ij : i≠j) (ai : b i=true) (aj : b j=true) : Ring i j := by
    by_contra ni
    obtain ⟨k,ik,jk⟩ := common i j ij ni (fun w => no ⟨i,j,w,(tr _).mp ai,(tr _).mp aj⟩)
    exact out k (h4 _ _ _ _ (H.inj.ne ij) ((tr _).mp ai).symm ((tr _).mp aj).symm
      ((H.adj _ _).mpr ik) ((H.adj _ _).mpr jk))
  have rule (p : Fin 8 → Fin 9) (ok : (Cert.eight p).Valid (ext Ring b) False) : False := by
    let N := M.extend x out tr
    have inj : InjectiveFin p := ok.1
    exact h8 ⟨N.f ∘ p,N.inj.comp (fun {_ _} => inj _ _),
      fun i j lt => (N.adj _ _).symm.trans (ok.2 i j lt)⟩
  obtain ⟨i,ei⟩ := contact
  have bi := (tr i).mpr ei
  by_cases other : ∃ j, i≠j ∧ b j=true
  · obtain ⟨j,ij,bj⟩ := other
    have all (k) (hk : b k=true) : k=i ∨ k=j := by
      by_contra ne
      push_neg at ne
      exact noTri i j k (narrow i j ij bi bj)
        (narrow i k ne.1.symm bi hk) (narrow j k ne.2.symm bj hk)
    have eq : b=Two i j := by
      funext k
      by_cases hk : k=i ∨ k=j
      · rw [show Two i j k=true by simp [Two,hk]]
        rcases hk with rfl | rfl <;> assumption
      · cases bk : b k
        · simp [Two,hk]
        · exact (hk (all _ bk)).elim
    rcases sides i j (narrow i j ij bi bj) with h | h
    · apply rule (minus i)
      rw [eq,h]
      exact p2 i
    · apply rule (plus i)
      rw [eq,h]
      exact p3 i
  · have eq : b=One i := by
      funext k
      by_cases h : k=i
      · simpa [One,h] using (h.symm ▸ bi : b k=true)
      · cases hk : b k
        · simp [One,h]
        · exact (other ⟨k,fun e => h e.symm,hk⟩).elim
    apply rule (plus i)
    rw [eq]
    exact p1 i

private def Reach {n : ℕ} (R : Fin n → Fin n → Prop) : ℕ → Fin n → Fin n → Prop
| 0,i,j => i=j
| k+1,i,j => i=j ∨ ∃ u,R i u ∧ Reach R k u j
private instance {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] (k : ℕ) :
    DecidableRel (Reach R k) := by
  induction k with
  | zero => intro i j; exact inferInstanceAs (Decidable (i=j))
  | succ k ih =>
    intro i j
    letI : DecidableRel (Reach R k) := ih
    exact inferInstanceAs (Decidable (i=j ∨ ∃ u,R i u ∧ Reach R k u j))
private lemma shortcut : ∀ i j : Fin 8, OctWide i j → ∀ k : Fin 8,
    Reach (ext Ring (Two i j)) 3 i.castSucc k.castSucc := by decide
private lemma close_site : ∀ c i j : Fin 8, OctWide i j → Reach Ring 2 c i ∨ Reach Ring 2 c j := by decide

private theorem dist_le_reach {n : ℕ} {R : Fin n → Fin n → Prop} (f : Fin n → V)
    (edges : ∀ i j, R i j → G.Adj (f i) (f j)) (hc : G.Connected)
    {k : ℕ} {i j : Fin n} (p : Reach R k i j) : G.dist (f i) (f j) ≤ k := by
  induction k generalizing i j with
  | zero =>
    change i=j at p
    subst j
    simp
  | succ k ih =>
    change i=j ∨ ∃ u,R i u ∧ Reach R k u j at p
    rcases p with rfl | ⟨u,e,r⟩
    · simp [dist_self]
    · have old := ih r
      have tri := hc.dist_triangle (u:=f i) (v:=f u) (w:=f j)
      rw [dist_eq_one_iff_adj.mpr (edges _ _ e)] at tri
      omega

private theorem ext_subset {a b : Fin 8 → Bool}
    (sub : ∀ i,a i=true → b i=true) (i j : Fin 9) :
    ext Ring a i j → ext Ring b i j := by
  refine Fin.lastCases ?_ (fun k => ?_) i <;> refine Fin.lastCases ?_ (fun l => ?_) j
  · intro no
    exact (ext_last Ring a no).elim
  · simpa only [ext_to_old] using sub l
  · simpa only [ext_from_old] using sub k
  · simp

private theorem radius_bound (G : SimpleGraph V) (v : V) {k : ℕ} (h : ∀ w,G.dist v w ≤ k) :
    Graffiti133.radius G ≤ k := by
  classical
  unfold Graffiti133.radius
  have hm : Finset.univ.sup (G.dist v) ∈ Finset.univ.image (fun u => Finset.univ.sup (G.dist u)) :=
    Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  have hl := Finset.min_le hm
  have ht : Finset.univ.sup (G.dist v) ≤ k := Finset.sup_le_iff.mpr (fun w _ => h w)
  cases hmin : (Finset.univ.image (fun u => Finset.univ.sup (G.dist u))).min with
  | top => exact Nat.zero_le _
  | coe d => exact (show d ≤ Finset.univ.sup (G.dist v) by simpa [hmin] using hl).trans ht

theorem radius_le_three_or_spans_of_dominating_octagon_allow_five (H : Hole G 8) (hc : G.Connected)
    (h4 : FourCycleFree G) (h8 : ¬∃ p : Fin 8 → V, InducedPath G p)
    (dom : ∀ x, Outside H.c x → ∃ i, G.Adj x (H.c i)) :
    Graffiti133.radius G ≤ 3 ∨ Function.Surjective H.c := by
  classical
  by_cases sur : Function.Surjective H.c
  · exact Or.inr sur
  have fresh : ∃ x, Outside H.c x := by
    by_contra none
    apply sur
    intro x
    by_contra bad
    exact none ⟨x,fun i ei => bad ⟨i,ei.symm⟩⟩
  obtain ⟨x,out⟩ := fresh
  obtain ⟨i,j,wide,e1,e2⟩ := outside_octagon_wide_pair H h4 h8 out (dom x out)
  let M := wideModel H
  let N := M.extend x out (M.contacts_true x)
  have sub (k : Fin 8) (e : Two i j k=true) : M.contacts x k=true := by
    rcases (show k=i ∨ k=j by simpa [Two] using e) with rfl | rfl
    · exact (M.contacts_true _ _).mpr e1
    · exact (M.contacts_true _ _).mpr e2
  apply Or.inl
  apply radius_bound G (H.c i)
  intro v
  by_cases on : ∃ j, H.c j=v
  · obtain ⟨k,rfl⟩ := on
    have le := dist_le_reach N.f (fun a b e => (N.adj a b).mp (ext_subset sub a b e)) hc (shortcut i j wide k)
    simpa [N,M,wideModel] using le
  · have outv : Outside H.c v := fun j e => on ⟨j,e.symm⟩
    obtain ⟨a,b,ab,ea,eb⟩ := outside_octagon_wide_pair H h4 h8 outv (dom v outv)
    have close (t : Fin 8) (p : Reach Ring 2 i t) (e : G.Adj v (H.c t)) : G.dist (H.c i) v ≤ 3 := by
      have le := dist_le_reach H.c (fun a b => (H.adj a b).mpr) hc p
      have tri := hc.dist_triangle (u:=H.c i) (v:=H.c t) (w:=v)
      rw [dist_eq_one_iff_adj.mpr e.symm] at tri
      omega
    rcases close_site i a b ab with l | r
    · exact close a l ea
    · exact close b r eb

#print axioms outside_octagon_wide_pair
#print axioms radius_le_three_or_spans_of_dominating_octagon_allow_five
end Graffiti133Eighth
