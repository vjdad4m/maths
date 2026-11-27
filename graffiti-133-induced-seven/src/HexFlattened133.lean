import HexFrameGeneral133
import C7OnlyMain


/- Original module: HexFar133 -/

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133RevisitSix Graffiti133NoFive Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

private theorem prepend_keep {k : ℕ} (hk : 0 < k) {p : Fin k → V} (hp : InducedPath G p)
    (x : V) (off : ∀ i, x ≠ p i) (h0 : G.Adj x (p ⟨0,hk⟩))
    (tail : ∀ i : Fin k, 0 < i.val → ¬G.Adj x (p i)) :
    ∃ q : Fin (k+1) → V, InducedPath G q ∧ q ⟨0,by omega⟩=x ∧
      (∀ i : Fin (k+1), 0 < i.val → ∃ j, q i=p j) := by
  obtain ⟨q,hq,h0,ht⟩ := prepend_induced_with_positions hk hp x off h0 tail
  exact ⟨q,hq,h0,fun i hi => ⟨_,ht i hi⟩⟩

private theorem tail_union {k : ℕ} (hk : 0 < k) {p : Fin k → V} {x : V}
    (head : p ⟨0,hk⟩=x) (Q : V → Prop) (rest : ∀ i, 0 < i.val → Q (p i)) :
    ∀ i, p i=x ∨ Q (p i) := by
  intro i
  by_cases h : i.val = 0
  · have eq : i = ⟨0,hk⟩ := Fin.ext h
    exact Or.inl (eq.symm ▸ head)
  · exact Or.inr (rest i (Nat.pos_of_ne_zero h))

private theorem far_not_opp {x y : V} {i : Fin 3} (hx : F.Opp x i) (hy : F.Far y) :
    y ≠ x := by
  intro eq
  exact hy.2 (frontInd i) (eq.symm ▸ (hx.2 _).mpr (Or.inl rfl))

/-- At an antipodal frontier vertex, a far induced P3 starting at one of
its neighbors must also contact its middle vertex. -/
theorem far_P3_middle {x a b c : V} {i : Fin 3} (hx : F.Opp x i)
    (ha : F.Far a) (hb : F.Far b) (hc : F.Far c)
    (xa : G.Adj x a) (ab : G.Adj a b) (bc : G.Adj b c)
    (ac : ¬G.Adj a c) (acne : a ≠ c) : G.Adj x b := by
  classical
  apply Classical.byContradiction
  intro nxb
  have nxc : ¬G.Adj x c := by
    intro xc
    exact acne (F.h4 x b a c (F.far_not_opp hx hb).symm xa ab.symm xc bc)
  obtain ⟨p,hp,h0,ht⟩ := F.rooted4 hx
  change p (0:Fin 4)=x at h0
  have hpAll (i : Fin 4) : p i = x ∨ ∃ j, p i = F.c j :=
    tail_union (by decide) h0 (fun v => ∃ j, v=F.c j) ht i
  have offA (i : Fin 4) : a ≠ p i := by
    intro eq
    rcases hpAll i with ex | ⟨j,ej⟩
    · exact (F.far_not_opp hx ha) (eq.trans ex)
    · exact ha.1 j (eq.trans ej)
  have aTail (i : Fin 4) (hi : 0 < i.val) : ¬G.Adj a (p i) := by
    obtain ⟨j,hj⟩ := ht i hi
    exact fun e => ha.2 j (hj ▸ e)
  obtain ⟨q,hq,q0,qt⟩ := prepend_keep (by decide) hp a offA (h0.symm ▸ xa.symm) aTail
  change q (0:Fin 5)=a at q0
  have qAll := tail_union (by decide) q0 (fun v => ∃ j, v=p j) qt
  have offB (i : Fin 5) : b ≠ q i := by
    intro eq
    rcases qAll i with ea | ⟨j,ej⟩
    · exact ab.ne (eq.trans ea).symm
    · have h := eq.trans ej
      rcases hpAll j with ex | ⟨k,ek⟩
      · exact (F.far_not_opp hx hb) (h.trans ex)
      · exact hb.1 k (h.trans ek)
  have bTail (i : Fin 5) (hi : 0 < i.val) : ¬G.Adj b (q i) := by
    intro h
    obtain ⟨j,hj⟩ := qt i hi
    have h' : G.Adj b (p j) := hj ▸ h
    rcases hpAll j with ex | ⟨k,ek⟩
    · exact nxb (ex ▸ h'.symm)
    · exact hb.2 k (ek ▸ h')
  obtain ⟨r,hr,r0,rt⟩ := prepend_keep (by decide) hq b offB (q0.symm ▸ ab.symm) bTail
  change r (0:Fin 6)=b at r0
  have rAll := tail_union (by decide) r0 (fun v => ∃ j, v=q j) rt
  have offC (i : Fin 6) : c ≠ r i := by
    intro eq
    rcases rAll i with eb | ⟨j,ej⟩
    · exact bc.ne (eq.trans eb).symm
    · have h := eq.trans ej
      rcases qAll j with ea | ⟨k,ek⟩
      · exact acne (h.trans ea).symm
      · have h' := h.trans ek
        rcases hpAll k with ex | ⟨l,el⟩
        · exact (F.far_not_opp hx hc) (h'.trans ex)
        · exact hc.1 l (h'.trans el)
  have cTail (i : Fin 6) (hi : 0 < i.val) : ¬G.Adj c (r i) := by
    intro h
    obtain ⟨j,hj⟩ := rt i hi
    have h' : G.Adj c (q j) := hj ▸ h
    rcases qAll j with ea | ⟨k,ek⟩
    · exact ac (ea ▸ h'.symm)
    · have h'' : G.Adj c (p k) := ek ▸ h'
      rcases hpAll k with ex | ⟨l,el⟩
      · exact nxc (ex ▸ h''.symm)
      · exact hc.2 l (el ▸ h'')
  obtain ⟨s,hs,_,_⟩ := prepend_keep (by decide) hr c offC (r0.symm ▸ bc.symm) cTail
  exact F.no7 ⟨s,hs⟩

private theorem independent_pair (x : V) (h : 2 ≤ localIndependence G x) :
    ∃ y z, y ≠ z ∧ G.Adj x y ∧ G.Adj x z ∧ ¬G.Adj y z := by
  classical
  obtain ⟨A,hA,hc⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
  obtain ⟨y,hy,z,hz,hD⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  exact ⟨y,z,hD,hN _ hy,hN _ hz,hI _ hy _ hz⟩

include F in
private theorem side_neighbor {x y : V} (e : G.Adj x y) (h : 2 ≤ localIndependence G x) :
    ∃ z, G.Adj x z ∧ y ≠ z ∧ ¬G.Adj y z := by
  obtain ⟨a,b,ab,ha,hb,nab⟩ := independent_pair x h
  by_cases ay : a=y
  · exact ⟨b,hb,ay ▸ ab,ay ▸ nab⟩
  by_cases by' : b=y
  · exact ⟨a,ha,(by' ▸ ab).symm,fun e => nab (by' ▸ e.symm)⟩
  by_cases ey : G.Adj y a
  · have hB : ¬G.Adj y b := fun e' => ab (F.h4 x y a b e.ne ha ey hb e')
    exact ⟨b,hb,fun e => by' e.symm,hB⟩
  · exact ⟨a,ha,fun e => ay e.symm,ey⟩

theorem far_neighbor_opp {x y : V} (hy : F.Far y) (ey : G.Adj x y)
    (hx : ¬ F.Far x) : ∃ i, F.Opp x i := by
  classical
  have out : Outside F.c x := fun i e => hy.2 i ((e ▸ ey).symm)
  have nh : ∃ i, G.Adj x (F.c i) := by
    apply Classical.byContradiction
    intro no
    exact hx ⟨out,fun i e => no ⟨i,e⟩⟩
  exact F.far_edge_opposite ⟨out,nh⟩ hy ey

/-- In the min-local-two core, every far vertex meets the antipodal frontier. -/
theorem far_has_opp (hc : G.Connected) (hmin : ∀ v, 2 ≤ localIndependence G v) :
    ∀ v, F.Far v → ∃ x i, F.Opp x i ∧ G.Adj x v := by
  classical
  let prop (v : V) : Prop := F.Far v → ∃ x i, F.Opp x i ∧ G.Adj x v
  have step (a b : V) (e : G.Adj a b) (hA : prop a) : prop b := by
    intro hb
    by_cases ha : F.Far a
    · obtain ⟨x,i,hx,xa⟩ := hA ha
      by_cases got : G.Adj x b
      · exact ⟨x,i,hx,got⟩
      · obtain ⟨c,bc,ane,nac⟩ := F.side_neighbor e.symm (hmin b)
        by_cases hh : F.Far c
        · exact (got (F.far_P3_middle hx ha hb hh xa e bc nac ane)).elim
        · obtain ⟨j,hj⟩ := F.far_neighbor_opp hb bc.symm hh
          exact ⟨c,j,hj,bc.symm⟩
    · obtain ⟨i,hi⟩ := F.far_neighbor_opp hb e ha
      exact ⟨a,i,hi,e⟩
  intro v
  obtain ⟨p⟩ := hc (F.c 0) v
  have hwalk {a b : V} (p : G.Walk a b) (ha : prop a) : prop b := by
    induction p with
    | nil => exact ha
    | cons e p ih => exact ih (step _ _ e ha)
  exact hwalk p (fun h => (h.1 0 rfl).elim)

private lemma anti_ne : ∀ i : Fin 3, frontInd i ≠ frontInd i+3 := by decide

theorem opp_unique {x y : V} {i : Fin 3} (hx : F.Opp x i) (hy : F.Opp y i) : x=y := by
  exact F.h4 (F.c (frontInd i)) (F.c (frontInd i+3)) x y
    (F.inj.ne (anti_ne i)) ((hx.2 _).mpr (Or.inl rfl)).symm ((hx.2 _).mpr (Or.inr rfl)).symm
    ((hy.2 _).mpr (Or.inl rfl)).symm ((hy.2 _).mpr (Or.inr rfl)).symm

private lemma opp_adj_site : ∀ i j : Fin 3, i ≠ j →
    ∃ a b : Fin 6, (a=frontInd i ∨ a=frontInd i+3) ∧
      (b=frontInd j ∨ b=frontInd j+3) ∧ Cyclic a b := by decide

theorem opp_independent {x y : V} {i j : Fin 3} (hx : F.Opp x i) (hy : F.Opp y j) :
    ¬ G.Adj x y := by
  by_cases he : i=j
  · have e := F.opp_unique hx (he.symm ▸ hy)
    exact fun h => h.ne e
  · obtain ⟨a,b,ha,hb,ee⟩ := opp_adj_site i j he
    exact fun e => F.contact_forbid hx.1 hy.1 e ((hx.2 _).mpr ha) ((hy.2 _).mpr hb) ee

#print axioms far_has_opp
#print axioms opp_independent
end Frame
end Graffiti133Hex

/- Original module: HexSmall133 -/

namespace Graffiti133Hex
open SimpleGraph Graffiti133 Graffiti133NoFive
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

def SmallRel {k : ℕ} (B : Fin k → Fin 6 → Bool) (E : Fin k → Fin k → Bool)
    (x y : Fin (6+k)) : Prop :=
  if hx : x.val < 6 then
    if hy : y.val < 6 then Cyclic ⟨x.val,hx⟩ ⟨y.val,hy⟩
    else B ⟨y.val-6,by omega⟩ ⟨x.val,hx⟩ = true
  else if hy : y.val < 6 then B ⟨x.val-6,by omega⟩ ⟨y.val,hy⟩ = true
  else E ⟨x.val-6,by omega⟩ ⟨y.val-6,by omega⟩ = true

noncomputable instance {k : ℕ} (B : Fin k → Fin 6 → Bool) (E : Fin k → Fin k → Bool) :
    DecidableRel (SmallRel B E) := by
  intro i j
  unfold SmallRel
  split <;> split <;> infer_instance

inductive SmallCert (n : ℕ)
| four (i j a b : Fin n)
| path (p : Fin 7 → Fin n)

def CertTrue {n : ℕ} (R : Fin n → Fin n → Prop) : SmallCert n → Prop
| .four i j a b => i ≠ j ∧ a ≠ b ∧ R i a ∧ R j a ∧ R i b ∧ R j b
| .path p => (∀ i j, p i = p j → i = j) ∧ ∀ i j, i < j → (R (p i) (p j) ↔ i.val+1=j.val)

noncomputable instance {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] :
    DecidablePred (CertTrue R) := by
  intro e
  cases e <;> unfold CertTrue <;> infer_instance

namespace Frame
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

theorem reject_small {k : ℕ} {B : Fin k → Fin 6 → Bool} {E : Fin k → Fin k → Bool}
    (e : Fin k → V) (inj : Function.Injective e) (off : ∀ i, Outside F.c (e i))
    (hB : ∀ u j, B u j=true ↔ G.Adj (e u) (F.c j))
    (hE : ∀ u v, E u v=true ↔ G.Adj (e u) (e v))
    (cert : SmallCert (6+k)) (checked : CertTrue (SmallRel B E) cert) : False := by
  let g (i : Fin (6+k)) : V :=
    if hi : i.val < 6 then F.c ⟨i.val,hi⟩ else e ⟨i.val-6,by omega⟩
  have ginj : Function.Injective g := by
    intro a b eq
    by_cases hA : a.val < 6 <;> by_cases hB : b.val < 6
    · have he := F.inj (show F.c ⟨a.val,hA⟩ = F.c ⟨b.val,hB⟩ by
        simpa only [g,dif_pos hA,dif_pos hB] using eq)
      exact Fin.ext (congrArg (fun z : Fin 6 => z.val) he)
    · exact (off ⟨b.val-6,by omega⟩ ⟨a.val,hA⟩
        (by simpa only [g,dif_pos hA,dif_neg hB] using eq.symm)).elim
    · exact (off ⟨a.val-6,by omega⟩ ⟨b.val,hB⟩
        (by simpa only [g,dif_neg hA,dif_pos hB] using eq)).elim
    · have he := inj (show e ⟨a.val-6,by omega⟩ = e ⟨b.val-6,by omega⟩ by
        simpa only [g,dif_neg hA,dif_neg hB] using eq)
      apply Fin.ext
      have hh := congrArg (fun z : Fin k => z.val) he
      change a.val-6=b.val-6 at hh
      omega
  have lift (a b : Fin (6+k)) : G.Adj (g a) (g b) ↔ SmallRel B E a b := by
    by_cases hA : a.val < 6 <;> by_cases hD : b.val < 6
    · simpa only [g,SmallRel,dif_pos hA,dif_pos hD] using F.adj ⟨a.val,hA⟩ ⟨b.val,hD⟩
    · simpa only [g,SmallRel,dif_pos hA,dif_neg hD,G.adj_comm] using (hB ⟨b.val-6,by omega⟩ ⟨a.val,hA⟩).symm
    · simpa only [g,SmallRel,dif_neg hA,dif_pos hD] using (hB ⟨a.val-6,by omega⟩ ⟨b.val,hD⟩).symm
    · simpa only [g,SmallRel,dif_neg hA,dif_neg hD] using (hE ⟨a.val-6,by omega⟩ ⟨b.val-6,by omega⟩).symm
  cases cert with
  | four i j a b =>
    obtain ⟨ne,nb,ia,ja,ib,jb⟩ := checked
    exact nb (ginj (F.h4 _ _ _ _ (fun h => ne (ginj h)) ((lift _ _).mpr ia)
      ((lift _ _).mpr ja) ((lift _ _).mpr ib) ((lift _ _).mpr jb)))
  | path p =>
    obtain ⟨hi,he⟩ := checked
    exact F.no7 ⟨g ∘ p,ginj.comp hi,fun i j ht => (lift _ _).trans (he i j ht)⟩

/-- The fifteen contact shapes relative to an induced hexagon. -/
def contact (t : Fin 15) (i : Fin 6) : Prop :=
  if h : t.val < 6 then i = (⟨t.val,h⟩ : Fin 6)
  else if h' : t.val < 12 then i = (⟨t.val-6,by omega⟩ : Fin 6) ∨
    i = (⟨t.val-6,by omega⟩ : Fin 6)+1
  else i = (⟨t.val-12,by have := t.isLt; omega⟩ : Fin 6) ∨
    i = (⟨t.val-12,by have := t.isLt; omega⟩ : Fin 6)+3

noncomputable instance (t : Fin 15) : DecidablePred (contact t) := by
  intro i
  unfold contact
  split
  · infer_instance
  · split <;> infer_instance

noncomputable def contactsB (t : Fin 15) (i : Fin 6) : Bool := decide (contact t i)

theorem profile_exists {x : V} (h : F.Near x) :
    ∃ t, ∀ i, contactsB t i=true ↔ G.Adj x (F.c i) := by
  classical
  rcases F.classify h with a | b | c
  · obtain ⟨i,hi⟩ := a
    use ⟨i.val,by have := i.isLt; omega⟩
    intro j
    have he := i.isLt
    simp [contactsB,contact,he,hi.2]
  · obtain ⟨i,hi⟩ := b
    use ⟨i.val+6,by have := i.isLt; omega⟩
    intro j
    have hL : ¬i.val+6<6 := by omega
    have hU : i.val+6<12 := by have := i.isLt; omega
    have hi' : (⟨i.val+6-6,by omega⟩ : Fin 6)=i := Fin.ext (by simp)
    simp [contactsB,contact,hL,hU,hi',hi.2]
  · obtain ⟨i,hi⟩ := c
    use ⟨i.val+12,by have := i.isLt; omega⟩
    intro j
    have hL : ¬i.val+12<6 := by omega
    have hU : ¬i.val+12<12 := by omega
    have hi' : (⟨i.val+12-12,by have := i.isLt; omega⟩ : Fin 6)=frontInd i := Fin.ext (by simp [frontInd])
    rw [contactsB,decide_eq_true_eq,contact,dif_neg hL,dif_neg hU,hi']
    exact (hi.2 j).symm

#print axioms reject_small
end Frame
end Graffiti133Hex

/- Original module: HexFarCount133 -/

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

private noncomputable def oppB (i : Fin 4) : Fin 6 → Bool :=
  if h : i.val<3 then contactsB ⟨12+i.val,by omega⟩ else fun _ => false

private def oppE (k : Fin 3) (i j : Fin 4) : Bool :=
  decide ((i=3 ∧ j.val<3 ∧ j.val≠k.val) ∨ (j=3 ∧ i.val<3 ∧ i.val≠k.val))

private def pathThree (k : Fin 3) : Fin 7 → Fin 10 := match k.val with
| 0 => ![0,6,3,2,8,9,7]
| 1 => ![1,7,4,3,6,9,8]
| _ => ![2,8,5,0,6,9,7]

private lemma checkedThree : ∀ k : Fin 3, CertTrue (SmallRel oppB (oppE k)) (.path (pathThree k)) := by
  decide

private lemma oppB_spec : ∀ a : Fin 3, ∀ j : Fin 6,
    oppB (a.castLE (by decide)) j=true ↔ j=frontInd a ∨ j=frontInd a+3 := by decide

/-- With all three antipodal profiles present, a far vertex cannot see
exactly two of them. Each of the three patterns has an explicit induced P7. -/
theorem far_forbid_two_of_three {x : V} (hx : F.Far x)
    (o : Fin 3 → V) (ho : ∀ i, F.Opp (o i) i)
    (k : Fin 3) (hA : ∀ i, G.Adj x (o i) ↔ i ≠ k) :
    False := by
  classical
  let e (i : Fin 4) := if h : i.val<3 then o ⟨i.val,h⟩ else x
  have eo (i : Fin 3) : e (i.castLE (by decide)) = o i := by simp [e,i.isLt]
  have ex : e 3=x := rfl
  have decomp : ∀ i : Fin 4, (∃ a : Fin 3, i=a.castLE (by decide)) ∨ i=3 := by decide
  have oinj : Function.Injective o := by
    intro i j eq
    have hh : G.Adj (o j) (F.c (frontInd i)) := eq ▸ ((ho i).2 _).mpr (Or.inl rfl)
    have key : ∀ i j : Fin 3, frontInd i=frontInd j ∨ frontInd i=frontInd j+3 → i=j := by decide
    exact key i j ((ho j).2 _ |>.mp hh)
  have noX (i : Fin 3) : x ≠ o i := by
    intro eq
    exact hx.2 (frontInd i) (eq.symm ▸ ((ho i).2 _ |>.mpr (Or.inl rfl)))
  have einj : Function.Injective e := by
    intro a b eq
    rcases decomp a with ⟨i,rfl⟩ | rfl <;> rcases decomp b with ⟨j,rfl⟩ | rfl
    · rw [eo,eo] at eq
      exact congrArg (Fin.castLE (by decide : 3≤4)) (oinj eq)
    · rw [eo,ex] at eq
      exact (noX _ eq.symm).elim
    · rw [ex,eo] at eq
      exact (noX _ eq).elim
    · rfl
  have off (i : Fin 4) : Outside F.c (e i) := by
    rcases decomp i with ⟨j,rfl⟩ | rfl
    · rw [eo]
      exact (ho j).1
    · rw [ex]
      exact hx.1
  have hB (i : Fin 4) (j : Fin 6) : oppB i j=true ↔ G.Adj (e i) (F.c j) := by
    rcases decomp i with ⟨a,rfl⟩ | rfl
    · rw [eo]
      exact (oppB_spec _ _).trans ((ho a).2 _).symm
    · rw [ex]
      change false = true ↔ G.Adj x (F.c j)
      simp [hx.2 j]
  have hE (u v : Fin 4) : oppE k u v=true ↔ G.Adj (e u) (e v) := by
    rcases decomp u with ⟨a,rfl⟩ | rfl <;> rcases decomp v with ⟨b,rfl⟩ | rfl
    · rw [eo,eo]
      have n : ¬G.Adj (o a) (o b) := F.opp_independent (ho a) (ho b)
      have ne : ∀ a : Fin 3, a.castLE (of_decide_eq_true rfl : 3≤4) ≠ (3 : Fin 4) := by decide
      simp [oppE,ne,n]
    · rw [eo,ex,G.adj_comm,hA]
      have ht (a : Fin 3) : a.castLE (of_decide_eq_true rfl : 3≤4) ≠ (3 : Fin 4) :=
        (by decide : ∀ a : Fin 3, a.castLE (of_decide_eq_true rfl : 3≤4) ≠ (3 : Fin 4)) a
      simp [oppE,ht,a.isLt,Fin.ext_iff]
    · rw [ex,eo,hA]
      have ht (a : Fin 3) : a.castLE (of_decide_eq_true rfl : 3≤4) ≠ (3 : Fin 4) :=
        (by decide : ∀ a : Fin 3, a.castLE (of_decide_eq_true rfl : 3≤4) ≠ (3 : Fin 4)) a
      simp [oppE,ht,b.isLt,Fin.ext_iff]
    · rw [ex]
      have n : ¬((3 : Fin 4).val<3) := by decide
      simp [oppE,n,G.loopless]
  exact F.reject_small e einj off hB hE (.path (pathThree k)) (checkedThree k)

noncomputable def oppSet : Finset V := by
  classical exact Finset.univ.filter (fun x => ∃ i, F.Opp x i)

theorem mem_oppSet (v : V) : v ∈ F.oppSet ↔ ∃ i, F.Opp v i := by
  classical simp [oppSet]

noncomputable def oppNeighbors (v : V) : Finset V := by
  classical exact F.oppSet.filter (G.Adj v)

theorem mem_oppNeighbors (v x : V) : x ∈ F.oppNeighbors v ↔ x ∈ F.oppSet ∧ G.Adj v x := by
  classical simp [oppNeighbors]

private noncomputable def oppIndex (v : V) : Fin 3 := by
  classical exact if h : ∃ i, F.Opp v i then Classical.choose h else 0

private theorem oppIndex_valid {v : V} (hv : v ∈ F.oppSet) : F.Opp v (F.oppIndex v) := by
  classical
  have h := (F.mem_oppSet v).mp hv
  unfold oppIndex
  rw [dif_pos h]
  exact Classical.choose_spec h

private theorem oppIndex_inj : Set.InjOn F.oppIndex (↑F.oppSet : Set V) := by
  intro x hx y hy he
  exact F.opp_unique (F.oppIndex_valid hx) (he.symm ▸ F.oppIndex_valid hy)

theorem card_oppSet : F.oppSet.card ≤ 3 := by
  classical
  have h := Finset.card_le_card_of_injOn F.oppIndex
    (t:=(Finset.univ : Finset (Fin 3))) (fun _ _ => Finset.mem_univ _) F.oppIndex_inj
  simpa using h

private theorem all_opp_present (hC : F.oppSet.card=3) :
    ∃ o : Fin 3 → V, (∀ i, F.Opp (o i) i) ∧ ∀ x, x∈F.oppSet → ∃ i, o i=x := by
  classical
  have hc : (F.oppSet.image F.oppIndex).card=3 := by
    rw [Finset.card_image_of_injOn F.oppIndex_inj,hC]
  have eq : F.oppSet.image F.oppIndex = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hc])
  have choices (i : Fin 3) : ∃ x, F.Opp x i := by
    obtain ⟨x,hx,hi⟩ := Finset.mem_image.mp (show i ∈ F.oppSet.image F.oppIndex by simp [eq])
    exact ⟨x,hi ▸ F.oppIndex_valid hx⟩
  let o (i : Fin 3) := Classical.choose (choices i)
  have ho (i : Fin 3) : F.Opp (o i) i := Classical.choose_spec (choices i)
  refine ⟨o,ho,?_⟩
  intro x hx
  obtain ⟨j,hj⟩ := (F.mem_oppSet x).mp hx
  exact ⟨j,F.opp_unique (ho j) hj⟩

/-- A far vertex sees just one antipodal vertex or all antipodal vertices
when the local minimum is at least two. -/
theorem far_one_or_all (hc : G.Connected) (hmin : ∀ v, 2 ≤ localIndependence G v)
    {v : V} (hv : F.Far v) :
    (F.oppNeighbors v).card=1 ∨ F.oppNeighbors v=F.oppSet := by
  classical
  let N := F.oppNeighbors v
  have sub : N ⊆ F.oppSet := Finset.filter_subset _ _
  have cb := Finset.card_le_card sub
  have cf := F.card_oppSet
  obtain ⟨x,i,hi,e⟩ := F.far_has_opp hc hmin v hv
  have pos : 0 < N.card := Finset.card_pos.mpr
    ⟨x,(F.mem_oppNeighbors v x).mpr ⟨(F.mem_oppSet x).mpr ⟨i,hi⟩,e.symm⟩⟩
  by_cases hl : N.card = 1
  · exact Or.inl hl
  by_cases he : N=F.oppSet
  · exact Or.inr he
  have hlt : N.card < F.oppSet.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,he⟩)
  have h2 : N.card=2 := by omega
  have h3 : F.oppSet.card=3 := by omega
  obtain ⟨o,ho,cover⟩ := F.all_opp_present h3
  have hole : ∃ y, y∈F.oppSet ∧ y∉N := by
    apply Classical.byContradiction
    intro no
    exact he (Finset.Subset.antisymm sub (fun y hy => Classical.byContradiction
      (fun no' => no ⟨y,hy,no'⟩)))
  obtain ⟨y,hy,hyn⟩ := hole
  obtain ⟨k,ey⟩ := cover y hy
  have hNotK : ¬G.Adj v (o k) := by
    rw [ey]
    exact fun e' => hyn ((F.mem_oppNeighbors v y).mpr ⟨hy,e'⟩)
  have hAll (i : Fin 3) : G.Adj v (o i) ↔ i≠k := by
    refine ⟨fun e h => hNotK (h ▸ e),?_⟩
    intro hik
    apply Classical.byContradiction
    intro hNotI
    have oI : o i ∈ F.oppSet := (F.mem_oppSet _).mpr ⟨i,ho i⟩
    have ni : o i ∉ N := fun h => hNotI ((F.mem_oppNeighbors _ _).mp h).2
    have oK : o k ∈ F.oppSet := (F.mem_oppSet _).mpr ⟨k,ho k⟩
    have nk : o k ∉ N := fun h => hNotK ((F.mem_oppNeighbors _ _).mp h).2
    have oNe : o i ≠ o k := by
      intro he'
      have hh := (ho k).2 (frontInd i) |>.mp (he' ▸ (ho i).2 _ |>.mpr (Or.inl rfl))
      exact hik ((by decide : ∀ i k : Fin 3, frontInd i=frontInd k ∨ frontInd i=frontInd k+3 → i=k) i k hh)
    have addSub : insert (o i) (insert (o k) N) ⊆ F.oppSet :=
      Finset.insert_subset oI (Finset.insert_subset oK sub)
    have cc := Finset.card_le_card addSub
    rw [Finset.card_insert_of_not_mem (by simp [oNe,ni]),Finset.card_insert_of_not_mem nk] at cc
    omega
  exact (F.far_forbid_two_of_three hv o ho k hAll).elim

#print axioms far_one_or_all
end Frame
end Graffiti133Hex

/- Original module: HexFarBudget133 -/

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

theorem far_seat_bound (hc : G.Connected) (hm : ∀ r, 2 ≤ localIndependence G r)
    {v : V} (hv : F.Far v) :
    localIndependence G v ≤ max 2 (F.oppNeighbors v).card := by
  classical
  obtain ⟨A,hA,hcard⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  have farOr (a : V) (ha : a ∈ A) :
      F.Far a ∨ a ∈ F.oppNeighbors v := by
    by_cases ht : F.Far a
    · exact Or.inl ht
    · obtain ⟨i,hi⟩ := F.far_neighbor_opp hv (hN _ ha).symm ht
      exact Or.inr ((F.mem_oppNeighbors _ _).mpr ⟨(F.mem_oppSet _).mpr ⟨i,hi⟩,hN _ ha⟩)
  rcases F.far_one_or_all hc hm hv with hOne | hAll
  · let B := A.filter F.Far
    have hb : B.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨haA,haf⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbA,hbf⟩ := Finset.mem_filter.mp hb
      by_contra hne
      obtain ⟨o,i,hoi,hoa⟩ := F.far_has_opp hc hm a haf
      obtain ⟨p,j,hpj,hpb⟩ := F.far_has_opp hc hm b hbf
      have ov := F.far_P3_middle hoi haf hv hbf hoa (hN _ haA).symm (hN _ hbA) (hI _ haA _ hbA) hne
      have pv := F.far_P3_middle hpj hbf hv haf hpb (hN _ hbA).symm (hN _ haA)
        (hI _ hbA _ haA) (fun q => hne q.symm)
      have ho := (F.mem_oppNeighbors v o).mpr ⟨(F.mem_oppSet o).mpr ⟨i,hoi⟩,ov.symm⟩
      have hp := (F.mem_oppNeighbors v p).mpr ⟨(F.mem_oppSet p).mpr ⟨j,hpj⟩,pv.symm⟩
      have eq := Finset.card_le_one.mp (show (F.oppNeighbors v).card ≤ 1 by omega) o ho p hp
      have ne : v ≠ o := fun e => hv.2 (frontInd i) (e.symm ▸ (hoi.2 _).mpr (Or.inl rfl))
      exact hne (F.h4 v o a b ne (hN _ haA) hoa (hN _ hbA) (eq.symm ▸ hpb))
    have sub : A ⊆ B ∪ F.oppNeighbors v := by
      intro a ha
      exact Finset.mem_union.mpr ((farOr a ha).imp (fun h => Finset.mem_filter.mpr ⟨ha,h⟩) id)
    have hh := (Finset.card_le_card sub).trans (Finset.card_union_le B (F.oppNeighbors v))
    omega
  · have chooseSeat (a : V) (ha : a ∈ A) :
        ∃ o ∈ F.oppNeighbors v, a = o ∨ G.Adj a o := by
      rcases farOr a ha with hf | hn
      · obtain ⟨o,i,hoi,hoa⟩ := F.far_has_opp hc hm a hf
        exact ⟨o, hAll.symm ▸ (F.mem_oppSet o).mpr ⟨i,hoi⟩, Or.inr hoa.symm⟩
      · exact ⟨a,hn,Or.inl rfl⟩
    let seat (a : V) := if h : a∈A then Classical.choose (chooseSeat a h) else v
    have hs {a : V} (ha : a∈A) :
        seat a ∈ F.oppNeighbors v ∧ (a=seat a ∨ G.Adj a (seat a)) := by
      simp only [seat,dif_pos ha]
      exact Classical.choose_spec (chooseSeat a ha)
    have hinj : Set.InjOn seat (↑A : Set V) := by
      intro a ha b hb e
      rcases (hs ha).2 with ha' | ha' <;> rcases (hs hb).2 with hb' | hb'
      · exact ha'.trans (e.trans hb'.symm)
      · exfalso
        exact hI _ ha _ hb ((ha'.trans e).symm ▸ hb'.symm)
      · exfalso
        exact hI _ ha _ hb ((hb'.trans e.symm).symm ▸ ha')
      · have hsv : G.Adj v (seat a) := ((F.mem_oppNeighbors _ _).mp (hs ha).1).2
        exact F.h4 v (seat a) a b hsv.ne (hN _ ha) ha'.symm (hN _ hb) (e.symm ▸ hb'.symm)
    exact hcard ▸ (Finset.card_le_card_of_injOn seat (fun _ ha => (hs ha).1) hinj).trans (le_max_right _ _)

noncomputable def farSet : Finset V := by
  classical exact Finset.univ.filter F.Far

theorem mem_farSet (v : V) : v ∈ F.farSet ↔ F.Far v := by
  classical simp [farSet]

theorem far_global_budget (hc : G.Connected) (hm : ∀ r, 2 ≤ localIndependence G r) :
    (∑ r ∈ F.farSet, (localIndependence G r + (F.oppNeighbors r).card))
      ≤ 3 * F.farSet.card + 3 := by
  classical
  let K (r : V) := (F.oppNeighbors r).offDiag
  have hsub : F.farSet.biUnion K ⊆ F.oppSet.offDiag := by
    intro p hp
    obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨ha,hb,hn⟩ := Finset.mem_offDiag.mp hr
    exact Finset.mem_offDiag.mpr ⟨((F.mem_oppNeighbors _ _).mp ha).1,
      ((F.mem_oppNeighbors _ _).mp hb).1,hn⟩
  have hd : (↑F.farSet : Set V).PairwiseDisjoint K := by
    intro r _ s _ rs
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨ha,hb,hn⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨ha',hb',_⟩ := Finset.mem_offDiag.mp hq
    exact rs (F.h4 p.1 p.2 r s hn ((F.mem_oppNeighbors _ _).mp ha).2.symm
      ((F.mem_oppNeighbors _ _).mp hb).2.symm ((F.mem_oppNeighbors _ _).mp ha').2.symm
      ((F.mem_oppNeighbors _ _).mp hb').2.symm)
  have h6 : F.oppSet.offDiag.card ≤ 6 := by
    rw [Finset.offDiag_card]
    have h := F.card_oppSet
    have cases : F.oppSet.card=0 ∨ F.oppSet.card=1 ∨ F.oppSet.card=2 ∨ F.oppSet.card=3 := by omega
    rcases cases with z | z | z | z <;> rw [z] <;> decide
  have hK : (∑ r ∈ F.farSet, (K r).card) ≤ 6 := by
    rw [← Finset.card_biUnion hd]
    exact (Finset.card_le_card hsub).trans h6
  have step (r : V) (hr : r∈F.farSet) :
      2 * (localIndependence G r + (F.oppNeighbors r).card) ≤ 6 + (K r).card := by
    have hv := (F.mem_farSet r).mp hr
    have hs := F.far_seat_bound hc hm hv
    obtain ⟨x,i,hi,e⟩ := F.far_has_opp hc hm r hv
    have hp : 0 < (F.oppNeighbors r).card := Finset.card_pos.mpr
      ⟨x,(F.mem_oppNeighbors r x).mpr ⟨(F.mem_oppSet x).mpr ⟨i,hi⟩,e.symm⟩⟩
    have ht := (Finset.card_le_card (Finset.filter_subset (G.Adj r) F.oppSet)).trans F.card_oppSet
    change (F.oppNeighbors r).card ≤ 3 at ht
    dsimp [K]
    rw [Finset.offDiag_card]
    have cases : (F.oppNeighbors r).card=1 ∨ (F.oppNeighbors r).card=2 ∨
      (F.oppNeighbors r).card=3 := by omega
    rcases cases with z | z | z <;> rw [z] at hs ⊢ <;> norm_num at hs ⊢ <;> omega
  have hsum := Finset.sum_le_sum step
  simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul] at hsum ⊢
  omega

#print axioms far_global_budget
#print axioms far_seat_bound
end Frame
end Graffiti133Hex

/- Original module: HexLowBounds133 -/

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

theorem exists_cycle {x : V} (hx : ¬Outside F.c x) : ∃ i, x=F.c i := by
  by_contra! h
  exact hx h

private theorem find_near {y : V} (hy : Outside F.c y) (hn : ¬ F.Far y) : F.Near y := by
  refine ⟨hy,?_⟩
  by_contra! h
  exact hn ⟨hy,h⟩

private lemma double_seats : ∀ i j : Fin 6, ¬Cyclic i j → ¬Cyclic (i+1) j →
    j=i+3 ∨ j=i+4 := by decide

private lemma opp_seats : ∀ i : Fin 3, ∀ j : Fin 6,
    ¬Cyclic (frontInd i) j → ¬Cyclic (frontInd i+3) j →
    j=frontInd i ∨ j=frontInd i+3 := by decide

private lemma rooted_edge : ∀ i : Fin 6, Cyclic i (i+1) := by decide

theorem local_double_bound {x : V} {i : Fin 6} (hx : F.Double x i) :
    localIndependence G x ≤ 3 := by
  classical
  obtain ⟨A,hA,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let T : Finset (Fin 6) := {i,i+3,i+4}
  have seat (y : V) (hy : y∈A) : ∃ j ∈ T, y=F.c j ∨ G.Adj y (F.c j) := by
    have e := hN _ hy
    by_cases out : Outside F.c y
    · have near : F.Near y := F.find_near out (fun hf => by
        obtain ⟨a,ha⟩ := F.far_edge_opposite ⟨hx.1,⟨i,(hx.2 _).mpr (Or.inl rfl)⟩⟩ hf e
        have neq : ∀ o : Fin 3, ∀ j : Fin 6,
            (j=frontInd o ∨ j=frontInd o+3) →
            ¬(j+1=frontInd o ∨ j+1=frontInd o+3) := by decide
        exact neq a i ((ha.2 _).mp ((hx.2 _).mpr (Or.inl rfl)))
          ((ha.2 _).mp ((hx.2 _).mpr (Or.inr rfl))))
      obtain ⟨j,hj⟩ := near.2
      have hj1 := fun c => F.contact_forbid hx.1 out e ((hx.2 _).mpr (Or.inl rfl)) hj c
      have hj2 := fun c => F.contact_forbid hx.1 out e ((hx.2 _).mpr (Or.inr rfl)) hj c
      rcases double_seats i j hj1 hj2 with rfl | rfl
      · exact ⟨i+3,by simp [T],Or.inr hj⟩
      · exact ⟨i+4,by simp [T],Or.inr hj⟩
    · obtain ⟨j,rfl⟩ := F.exists_cycle out
      refine ⟨i,by simp [T],?_⟩
      rcases (hx.2 j).mp e with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ((F.adj _ _).mpr (rooted_edge i)).symm
  let f (y : V) := if h : y∈A then Classical.choose (seat y h) else i
  have hs {y : V} (h : y∈A) : f y∈T ∧ (y=F.c (f y) ∨ G.Adj y (F.c (f y))) := by
    simpa only [f,dif_pos h] using Classical.choose_spec (seat y h)
  have inj : Set.InjOn f (↑A : Set V) := by
    intro y hy z hz he
    exact F.stamp_uniq (hx.1 (f y)) (hN _ hy) (hN _ hz) (hI _ hy _ hz)
      (hs hy).2 (he.symm ▸ (hs hz).2)
  have hT : T.card ≤ 3 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ((Finset.card_insert_le _ _).trans (by simp)) 1)
  exact eq ▸ (Finset.card_le_card_of_injOn f (fun _ h => (hs h).1) inj).trans hT

noncomputable def farNeighbors (x : V) : Finset V := by
  classical exact F.farSet.filter (G.Adj x)

theorem local_opp_bound {x : V} {i : Fin 3} (hx : F.Opp x i) :
    localIndependence G x ≤ 2 + (F.farNeighbors x).card := by
  classical
  obtain ⟨A,hA,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let R := F.farNeighbors x
  let B := A \ R
  let T : Finset (Fin 6) := {frontInd i,frontInd i+3}
  have seat (y : V) (hy : y∈B) : ∃ j ∈ T, y=F.c j ∨ G.Adj y (F.c j) := by
    obtain ⟨hy,hn⟩ := Finset.mem_sdiff.mp hy
    have e := hN _ hy
    by_cases out : Outside F.c y
    · have near := F.find_near out (fun hf => hn (Finset.mem_filter.mpr ⟨(F.mem_farSet y).mpr hf,e⟩))
      obtain ⟨j,hj⟩ := near.2
      have hj1 := fun c => F.contact_forbid hx.1 out e ((hx.2 _).mpr (Or.inl rfl)) hj c
      have hj2 := fun c => F.contact_forbid hx.1 out e ((hx.2 _).mpr (Or.inr rfl)) hj c
      have ha := opp_seats i j hj1 hj2
      exact ⟨j,by simpa [T] using ha,Or.inr hj⟩
    · obtain ⟨j,rfl⟩ := F.exists_cycle out
      exact ⟨j,by simpa [T] using (hx.2 j).mp e,Or.inl rfl⟩
  let f (y : V) := if h : y∈B then Classical.choose (seat y h) else frontInd i
  have hs {y : V} (h : y∈B) : f y∈T ∧ (y=F.c (f y) ∨ G.Adj y (F.c (f y))) := by
    simpa only [f,dif_pos h] using Classical.choose_spec (seat y h)
  have inj : Set.InjOn f (↑B : Set V) := by
    intro y hy z hz he
    have hy' := (Finset.mem_sdiff.mp hy).1
    have hz' := (Finset.mem_sdiff.mp hz).1
    exact F.stamp_uniq (hx.1 _) (hN _ hy') (hN _ hz') (hI _ hy' _ hz')
      (hs hy).2 (he.symm ▸ (hs hz).2)
  have hT : T.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have hB := (Finset.card_le_card_of_injOn f (fun _ h => (hs h).1) inj).trans hT
  have hInt := Finset.card_le_card (show A ∩ R ⊆ R from Finset.inter_subset_right)
  have hC := Finset.card_sdiff_add_card_inter A R
  change B.card + (A ∩ R).card = A.card at hC
  change localIndependence G x ≤ 2 + R.card
  omega

noncomputable def singleSite (i : Fin 6) : Finset V := by
  classical exact Finset.univ.filter (fun v => F.Single v i)

noncomputable def oppSite (i : Fin 6) : Finset V := by
  classical exact F.oppSet.filter (fun v => G.Adj v (F.c i))

private lemma cyc6_ne : ∀ i j : Fin 6, Cyclic i j → i ≠ j := by decide
private lemma cyc6_sites : ∀ i j : Fin 6, Cyclic i j ↔ j=i+1 ∨ j=i+5 := by decide

theorem local_cycle_bound (i : Fin 6) :
    localIndependence G (F.c i) ≤ 2 + (F.singleSite i).card + (F.oppSite i).card := by
  classical
  obtain ⟨A,hA,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) (F.c i)
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let U := F.singleSite i ∪ F.oppSite i
  let B := A \ U
  let T : Finset (Fin 6) := {i+1,i+5}
  have seat (y : V) (hy : y∈B) : ∃ j, Cyclic i j ∧ (y=F.c j ∨ G.Adj y (F.c j)) := by
    obtain ⟨hy,hn⟩ := Finset.mem_sdiff.mp hy
    have e := hN _ hy
    by_cases out : Outside F.c y
    · rcases F.classify (x:=y) ⟨out,i,e.symm⟩ with ⟨j,hj⟩ | ⟨j,hj⟩ | ⟨j,hj⟩
      · have h := (hj.2 i).mp e.symm
        exact (hn (Finset.mem_union_left _ (by simpa [singleSite,h] using hj))).elim
      · rcases (hj.2 i).mp e.symm with h | h
        · exact ⟨j+1,by simpa [h] using rooted_edge j,Or.inr ((hj.2 _).mpr (Or.inr rfl))⟩
        · exact ⟨j,(cyclic_symm _ _).mpr (by simpa [h] using rooted_edge j),
            Or.inr ((hj.2 _).mpr (Or.inl rfl))⟩
      · have hw := (F.mem_oppSet y).mpr ⟨j,hj⟩
        exact (hn (Finset.mem_union_right _ (by simp [oppSite,hw,e.symm]))).elim
    · obtain ⟨j,rfl⟩ := F.exists_cycle out
      exact ⟨j,(F.adj _ _).mp e,Or.inl rfl⟩
  let f (y : V) := if h : y∈B then Classical.choose (seat y h) else i
  have hs {y : V} (h : y∈B) : Cyclic i (f y) ∧ (y=F.c (f y) ∨ G.Adj y (F.c (f y))) := by
    simpa only [f,dif_pos h] using Classical.choose_spec (seat y h)
  have inT {y : V} (hy : y∈B) : f y∈T := by
    simpa [T] using (cyc6_sites _ _).mp (hs hy).1
  have inj : Set.InjOn f (↑B : Set V) := by
    intro y hy z hz he
    have hy' := (Finset.mem_sdiff.mp hy).1
    have hz' := (Finset.mem_sdiff.mp hz).1
    exact F.stamp_uniq (F.inj.ne (cyc6_ne _ _ (hs hy).1)) (hN _ hy') (hN _ hz') (hI _ hy' _ hz')
      (hs hy).2 (he.symm ▸ (hs hz).2)
  have hT : T.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have hB := (Finset.card_le_card_of_injOn f (fun _ h => inT h) inj).trans hT
  have hInt := (Finset.card_le_card (show A ∩ U ⊆ U from Finset.inter_subset_right)).trans
    (Finset.card_union_le (F.singleSite i) (F.oppSite i))
  have hC := Finset.card_sdiff_add_card_inter A U
  change B.card + (A ∩ U).card = A.card at hC
  omega

#print axioms local_cycle_bound
#print axioms local_double_bound
#print axioms local_opp_bound
end Frame
end Graffiti133Hex

/- Original module: HexLowSum133 -/

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

noncomputable def singleSet : Finset V := by
  classical exact Finset.univ.filter (fun x => ∃ i, F.Single x i)

noncomputable def cycleSet : Finset V := by
  classical exact Finset.univ.image F.c

private theorem single_site_sum : (∑ i, (F.singleSite i).card) = F.singleSet.card := by
  classical
  have ht : ((Finset.univ : Finset (Fin 6)).biUnion F.singleSite) = F.singleSet := by
    ext x
    simp [singleSet,singleSite]
  have hd : (↑(Finset.univ : Finset (Fin 6)) : Set (Fin 6)).PairwiseDisjoint F.singleSite := by
    intro a _ b _ ne
    apply Finset.disjoint_left.mpr
    intro x ha hb
    have sa : F.Single x a := by simpa [singleSite] using ha
    have sb : F.Single x b := by simpa [singleSite] using hb
    exact ne ((sb.2 a).mp ((sa.2 a).mpr rfl))
  rw [← Finset.card_biUnion hd, ht]

private theorem opp_site_sum : (∑ i, (F.oppSite i).card) = 2 * F.oppSet.card := by
  classical
  simp only [oppSite,Finset.card_filter]
  rw [Finset.sum_comm]
  have step (x : V) (hx : x∈F.oppSet) : (∑ j : Fin 6, if G.Adj x (F.c j) then 1 else 0) = 2 := by
    obtain ⟨i,hi⟩ := (F.mem_oppSet x).mp hx
    simp_rw [hi.2]
    have aux : ∀ i : Fin 3, (∑ j : Fin 6, if j=frontInd i ∨ j=frontInd i+3 then (1:ℕ) else 0) = 2 := by decide
    exact aux i
  calc
    (∑ x ∈ F.oppSet, ∑ i : Fin 6, if G.Adj x (F.c i) then 1 else 0)
        = ∑ _x ∈ F.oppSet, 2 := Finset.sum_congr rfl step
    _ = 2 * F.oppSet.card := by simp [Nat.mul_comm]

private theorem inc_symm :
    (∑ x ∈ F.oppSet, (F.farNeighbors x).card) =
      ∑ r ∈ F.farSet, (F.oppNeighbors r).card := by
  classical
  simp only [farNeighbors,oppNeighbors,Finset.card_filter]
  rw [Finset.sum_comm]
  simp only [G.adj_comm]

/-- Hexagon density when every singleton-profile vertex has local independence
at most two; antipodal-to-far incidences cancel between the two budgets. -/
theorem low_hex_budget (hc : G.Connected) (hm : ∀ r, 2 ≤ localIndependence G r)
    (low : ∀ x i, F.Single x i → localIndependence G x ≤ 2) :
    (∑ x, localIndependence G x) ≤ 3 * Fintype.card V := by
  classical
  let A := F.cycleSet
  let S := F.singleSet
  let O := F.oppSet
  let R := F.farSet
  let D := Finset.univ \ (A ∪ S ∪ O ∪ R)
  have cyc (x : V) : x ∈ A ↔ ∃ i, x = F.c i := by
    constructor
    · intro h
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
      exact ⟨i,hi.symm⟩
    · rintro ⟨i,rfl⟩
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have sm (x : V) : x∈S ↔ ∃ i, F.Single x i := by simp [S,singleSet]
  have so : Disjoint S O := by
    apply Finset.disjoint_left.mpr
    intro x hs ho
    obtain ⟨i,hi⟩ := (sm x).mp hs
    obtain ⟨j,hj⟩ := (F.mem_oppSet x).mp ho
    have h1 := (hi.2 _).mp ((hj.2 _).mpr (Or.inl rfl))
    have h2 := (hi.2 _).mp ((hj.2 _).mpr (Or.inr rfl))
    exact (by decide : ∀ j : Fin 3, frontInd j ≠ frontInd j+3) j (h1.trans h2.symm)
  have aS : Disjoint A S := by
    apply Finset.disjoint_left.mpr
    intro x ha hs
    obtain ⟨i,hi⟩ := (cyc x).mp ha
    obtain ⟨j,hj⟩ := (sm x).mp hs
    exact hj.1 i hi
  have aO : Disjoint A O := by
    apply Finset.disjoint_left.mpr
    intro x ha hs
    obtain ⟨i,hi⟩ := (cyc x).mp ha
    obtain ⟨j,hj⟩ := (F.mem_oppSet x).mp hs
    exact hj.1 i hi
  have aR : Disjoint A R := by
    apply Finset.disjoint_left.mpr
    intro x ha hr
    obtain ⟨i,hi⟩ := (cyc x).mp ha
    exact ((F.mem_farSet x).mp hr).1 i hi
  have sR : Disjoint S R := by
    apply Finset.disjoint_left.mpr
    intro x hs hr
    obtain ⟨i,hi⟩ := (sm x).mp hs
    exact ((F.mem_farSet x).mp hr).2 i ((hi.2 i).mpr rfl)
  have oR : Disjoint O R := by
    apply Finset.disjoint_left.mpr
    intro x ho hr
    obtain ⟨i,hi⟩ := (F.mem_oppSet x).mp ho
    exact ((F.mem_farSet x).mp hr).2 (frontInd i) ((hi.2 _).mpr (Or.inl rfl))
  have d1 : Disjoint (A ∪ S) O := Finset.disjoint_union_left.mpr ⟨aO,so⟩
  have d2 : Disjoint (A ∪ S ∪ O) R := Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_left.mpr ⟨aR,sR⟩,oR⟩
  have d3 : Disjoint (A ∪ S ∪ O ∪ R) D := by
    apply Finset.disjoint_left.mpr
    exact fun x hx hd => (Finset.mem_sdiff.mp hd).2 hx
  have u : A ∪ S ∪ O ∪ R ∪ D = Finset.univ := by
    ext x
    by_cases h : x ∈ A ∪ S ∪ O ∪ R <;> simp [D,h]
  have ca : A.card=6 := by simp [A,cycleSet,Finset.card_image_of_injective _ F.inj]
  have co := F.card_oppSet
  change O.card ≤ 3 at co
  have ns : Fintype.card V = 6+S.card+O.card+R.card+D.card := by
    rw [← Finset.card_univ,←u,Finset.card_union_of_disjoint d3,Finset.card_union_of_disjoint d2,
      Finset.card_union_of_disjoint d1,Finset.card_union_of_disjoint aS,ca]
  let f := localIndependence G
  have splits : (∑ x, f x) =
      (∑ x ∈ A,f x)+(∑ x ∈ S,f x)+(∑ x ∈ O,f x)+(∑ x ∈ R,f x)+(∑ x ∈ D,f x) := by
    rw [←u,Finset.sum_union d3,Finset.sum_union d2,Finset.sum_union d1,Finset.sum_union aS]
  have bA : (∑ x∈A,f x) ≤ 12+S.card+2*O.card := by
    change (∑ x∈Finset.univ.image F.c,f x) ≤ _
    rw [Finset.sum_image (fun _ _ _ _ e => F.inj e)]
    apply (Finset.sum_le_sum (fun i _ => F.local_cycle_bound i)).trans
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      Nat.nsmul_eq_mul,single_site_sum,opp_site_sum,S,O]
    omega
  have bS : (∑ x∈S,f x) ≤ 2*S.card := by
    calc
      (∑ x ∈ S, f x) ≤ ∑ _x ∈ S, (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨i,hi⟩ := (sm x).mp hx
        exact low x i hi
      _ = 2*S.card := by simp [Finset.sum_const,Nat.nsmul_eq_mul,Nat.mul_comm]
  let inc := ∑ r∈R,(F.oppNeighbors r).card
  have bO : (∑ x∈O,f x) ≤ 2*O.card+inc := by
    have h := Finset.sum_le_sum (s:=O) (fun x hx => by
      obtain ⟨i,hi⟩ := (F.mem_oppSet x).mp hx
      exact F.local_opp_bound hi)
    simpa [Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul,Nat.mul_comm,
      inc,O,R,F.inc_symm] using h
  have bR : (∑ x∈R,f x)+inc ≤ 3*R.card+3 := by
    simpa only [Finset.sum_add_distrib] using F.far_global_budget hc hm
  have bD : (∑ x∈D,f x) ≤ 3*D.card := by
    have step (x : V) (hx : x∈D) : f x ≤ 3 := by
      have hn := (Finset.mem_sdiff.mp hx).2
      have out : Outside F.c x := fun i h => hn (by simp [(cyc x).mpr ⟨i,h⟩])
      have hf : ¬F.Far x := fun h => hn (Finset.mem_union_right _ ((F.mem_farSet x).mpr h))
      have hnear : F.Near x := by
        refine ⟨out,?_⟩
        apply Classical.byContradiction
        intro h
        exact hf ⟨out,fun i e => h ⟨i,e⟩⟩
      rcases F.classify hnear with ⟨i,hi⟩ | ⟨i,hi⟩ | ⟨i,hi⟩
      · exact (hn (by simp [(sm x).mpr ⟨i,hi⟩])).elim
      · exact F.local_double_bound hi
      · exact (hn (by simp [show x∈O from (F.mem_oppSet x).mpr ⟨i,hi⟩])).elim
    calc
      (∑ x ∈ D, f x) ≤ ∑ _x ∈ D, (3 : ℕ) := Finset.sum_le_sum step
      _ = 3*D.card := by simp [Finset.sum_const,Nat.nsmul_eq_mul,Nat.mul_comm]
  rw [splits,ns]
  omega

#print axioms low_hex_budget
end Frame
end Graffiti133Hex

/- Original module: HexHighTables133 -/

namespace Graffiti133Hex
open Frame
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000
private def anchorTable (a b : Fin 15) : Option (SmallCert 9) :=
  match a.val, b.val with
  | 1, 1 => some (.four 0 7 1 6)
  | 1, 2 => some (.four 0 7 1 6)
  | 1, 3 => some (.four 0 7 1 6)
  | 1, 4 => some (.four 0 7 1 6)
  | 1, 5 => some (.four 0 7 1 6)
  | 1, 7 => some (.four 0 7 1 6)
  | 1, 8 => some (.four 0 7 1 6)
  | 1, 9 => some (.four 0 7 1 6)
  | 1, 10 => some (.four 0 7 1 6)
  | 1, 13 => some (.four 0 7 1 6)
  | 1, 14 => some (.four 0 7 1 6)
  | 2, 1 => some (.four 0 8 1 6)
  | 2, 2 => some (.four 2 6 7 8)
  | 2, 4 => some (.path ![1,2,7,6,8,4,5])
  | 2, 5 => some (.four 0 8 5 6)
  | 2, 7 => some (.four 0 8 1 6)
  | 2, 8 => some (.four 2 6 7 8)
  | 2, 9 => some (.path ![1,2,7,6,8,4,5])
  | 2, 10 => some (.four 0 8 5 6)
  | 2, 13 => some (.four 0 8 1 6)
  | 2, 14 => some (.four 0 8 5 6)
  | 3, 1 => some (.four 0 8 1 6)
  | 3, 3 => some (.four 3 6 7 8)
  | 3, 5 => some (.four 0 8 5 6)
  | 3, 7 => some (.four 0 8 1 6)
  | 3, 8 => some (.four 3 6 7 8)
  | 3, 9 => some (.four 3 6 7 8)
  | 3, 10 => some (.four 0 8 5 6)
  | 3, 13 => some (.four 0 8 1 6)
  | 3, 14 => some (.four 0 8 5 6)
  | 4, 1 => some (.four 0 8 1 6)
  | 4, 2 => some (.path ![1,2,8,6,7,4,5])
  | 4, 4 => some (.four 4 6 7 8)
  | 4, 5 => some (.four 0 8 5 6)
  | 4, 7 => some (.four 0 8 1 6)
  | 4, 8 => some (.path ![1,2,8,6,7,4,5])
  | 4, 9 => some (.four 4 6 7 8)
  | 4, 10 => some (.four 0 8 5 6)
  | 4, 13 => some (.four 0 8 1 6)
  | 4, 14 => some (.four 0 8 5 6)
  | 5, 1 => some (.four 0 7 5 6)
  | 5, 2 => some (.four 0 7 5 6)
  | 5, 3 => some (.four 0 7 5 6)
  | 5, 4 => some (.four 0 7 5 6)
  | 5, 5 => some (.four 0 7 5 6)
  | 5, 7 => some (.four 0 7 5 6)
  | 5, 8 => some (.four 0 7 5 6)
  | 5, 9 => some (.four 0 7 5 6)
  | 5, 10 => some (.four 0 7 5 6)
  | 5, 13 => some (.four 0 7 5 6)
  | 5, 14 => some (.four 0 7 5 6)
  | 7, 1 => some (.four 0 7 1 6)
  | 7, 2 => some (.four 0 7 1 6)
  | 7, 3 => some (.four 0 7 1 6)
  | 7, 4 => some (.four 0 7 1 6)
  | 7, 5 => some (.four 0 7 1 6)
  | 7, 7 => some (.four 0 7 1 6)
  | 7, 8 => some (.four 0 7 1 6)
  | 7, 9 => some (.four 0 7 1 6)
  | 7, 10 => some (.four 0 7 1 6)
  | 7, 13 => some (.four 0 7 1 6)
  | 7, 14 => some (.four 0 7 1 6)
  | 8, 1 => some (.four 0 8 1 6)
  | 8, 2 => some (.four 2 6 7 8)
  | 8, 3 => some (.four 3 6 7 8)
  | 8, 4 => some (.path ![1,2,7,6,8,4,5])
  | 8, 5 => some (.four 0 8 5 6)
  | 8, 7 => some (.four 0 8 1 6)
  | 8, 8 => some (.four 2 3 7 8)
  | 8, 9 => some (.four 3 6 7 8)
  | 8, 10 => some (.four 0 8 5 6)
  | 8, 13 => some (.four 0 8 1 6)
  | 8, 14 => some (.four 0 8 5 6)
  | 9, 1 => some (.four 0 8 1 6)
  | 9, 2 => some (.path ![1,2,8,6,7,4,5])
  | 9, 3 => some (.four 3 6 7 8)
  | 9, 4 => some (.four 4 6 7 8)
  | 9, 5 => some (.four 0 8 5 6)
  | 9, 7 => some (.four 0 8 1 6)
  | 9, 8 => some (.four 3 6 7 8)
  | 9, 9 => some (.four 3 4 7 8)
  | 9, 10 => some (.four 0 8 5 6)
  | 9, 13 => some (.four 0 8 1 6)
  | 9, 14 => some (.four 0 8 5 6)
  | 10, 1 => some (.four 0 7 5 6)
  | 10, 2 => some (.four 0 7 5 6)
  | 10, 3 => some (.four 0 7 5 6)
  | 10, 4 => some (.four 0 7 5 6)
  | 10, 5 => some (.four 0 7 5 6)
  | 10, 7 => some (.four 0 7 5 6)
  | 10, 8 => some (.four 0 7 5 6)
  | 10, 9 => some (.four 0 7 5 6)
  | 10, 10 => some (.four 0 7 5 6)
  | 10, 13 => some (.four 0 7 5 6)
  | 10, 14 => some (.four 0 7 5 6)
  | 13, 1 => some (.four 0 7 1 6)
  | 13, 2 => some (.four 0 7 1 6)
  | 13, 3 => some (.four 0 7 1 6)
  | 13, 4 => some (.four 0 7 1 6)
  | 13, 5 => some (.four 0 7 1 6)
  | 13, 7 => some (.four 0 7 1 6)
  | 13, 8 => some (.four 0 7 1 6)
  | 13, 9 => some (.four 0 7 1 6)
  | 13, 10 => some (.four 0 7 1 6)
  | 13, 13 => some (.four 0 7 1 6)
  | 13, 14 => some (.four 0 7 1 6)
  | 14, 1 => some (.four 0 7 5 6)
  | 14, 2 => some (.four 0 7 5 6)
  | 14, 3 => some (.four 0 7 5 6)
  | 14, 4 => some (.four 0 7 5 6)
  | 14, 5 => some (.four 0 7 5 6)
  | 14, 7 => some (.four 0 7 5 6)
  | 14, 8 => some (.four 0 7 5 6)
  | 14, 9 => some (.four 0 7 5 6)
  | 14, 10 => some (.four 0 7 5 6)
  | 14, 13 => some (.four 0 7 5 6)
  | 14, 14 => some (.four 0 7 5 6)
  | _, _ => none
private def extraTable (a : Fin 15) (b : Fin 8) : Option (SmallCert 10) :=
  match a.val, b.val with
  | 0, 0 => some (.path ![4,3,2,7,6,0,9])
  | 0, 1 => some (.path ![5,4,3,2,7,6,9])
  | 0, 2 => some (.four 0 7 6 9)
  | 0, 3 => some (.four 0 7 6 9)
  | 0, 4 => some (.four 0 8 6 9)
  | 0, 5 => some (.four 0 8 6 9)
  | 0, 6 => some (.four 0 7 6 9)
  | 0, 7 => some (.four 0 7 6 9)
  | 1, 0 => some (.path ![4,3,8,6,0,1,9])
  | 1, 1 => some (.four 0 9 1 6)
  | 1, 2 => some (.four 1 7 2 9)
  | 1, 3 => some (.four 0 9 1 6)
  | 1, 5 => some (.four 0 9 1 6)
  | 1, 6 => some (.four 1 7 2 9)
  | 1, 7 => some (.four 0 9 1 6)
  | 2, 0 => some (.path ![4,5,0,6,7,2,9])
  | 2, 1 => some (.four 2 6 7 9)
  | 2, 2 => some (.path ![3,4,5,0,6,7,9])
  | 2, 3 => some (.four 2 6 7 9)
  | 2, 4 => some (.four 2 8 3 9)
  | 2, 5 => some (.four 2 6 7 9)
  | 2, 6 => some (.four 2 8 3 9)
  | 2, 7 => some (.four 2 6 7 9)
  | 3, 0 => some (.path ![5,0,6,7,2,3,9])
  | 3, 1 => some (.four 3 6 8 9)
  | 3, 2 => some (.four 2 9 3 7)
  | 3, 3 => some (.four 2 9 3 7)
  | 3, 4 => some (.path ![5,0,6,7,2,3,9])
  | 3, 5 => some (.four 3 6 8 9)
  | 3, 6 => some (.four 2 9 3 7)
  | 3, 7 => some (.four 2 9 3 7)
  | 4, 0 => some (.path ![0,6,7,2,3,4,9])
  | 4, 1 => some (.path ![1,2,7,6,9,4,5])
  | 4, 2 => some (.path ![1,0,6,7,9,4,3])
  | 4, 4 => some (.four 3 9 4 8)
  | 4, 5 => some (.four 3 9 4 8)
  | 4, 6 => some (.four 3 9 4 8)
  | 4, 7 => some (.four 3 9 4 8)
  | 5, 0 => some (.path ![2,3,8,6,0,5,9])
  | 5, 1 => some (.four 0 9 5 6)
  | 5, 2 => some (.path ![0,5,9,7,2,3,8])
  | 5, 3 => some (.four 0 9 5 6)
  | 5, 4 => some (.path ![0,5,9,8,3,2,7])
  | 5, 5 => some (.four 0 9 5 6)
  | 5, 6 => some (.four 6 9 7 8)
  | 5, 7 => some (.four 0 9 5 6)
  | 6, 0 => some (.path ![4,3,2,7,6,0,9])
  | 6, 1 => some (.four 0 9 1 6)
  | 6, 2 => some (.four 0 7 6 9)
  | 6, 3 => some (.four 0 7 6 9)
  | 6, 4 => some (.four 0 8 6 9)
  | 6, 5 => some (.four 0 8 6 9)
  | 6, 6 => some (.four 0 7 6 9)
  | 6, 7 => some (.four 0 7 6 9)
  | 7, 0 => some (.path ![4,3,8,6,0,1,9])
  | 7, 1 => some (.four 0 9 1 6)
  | 7, 2 => some (.four 1 7 2 9)
  | 7, 3 => some (.four 0 9 1 6)
  | 7, 4 => some (.four 2 8 3 9)
  | 7, 5 => some (.four 0 9 1 6)
  | 7, 6 => some (.four 1 7 2 9)
  | 7, 7 => some (.four 0 9 1 6)
  | 8, 0 => some (.path ![4,5,0,6,7,2,9])
  | 8, 1 => some (.four 2 6 7 9)
  | 8, 2 => some (.four 2 9 3 7)
  | 8, 3 => some (.four 2 6 7 9)
  | 8, 4 => some (.four 2 8 3 9)
  | 8, 5 => some (.four 2 6 7 9)
  | 8, 6 => some (.four 2 8 3 9)
  | 8, 7 => some (.four 2 6 7 9)
  | 9, 0 => some (.path ![2,7,6,0,5,4,9])
  | 9, 1 => some (.four 3 6 8 9)
  | 9, 2 => some (.four 2 9 3 7)
  | 9, 3 => some (.four 2 9 3 7)
  | 9, 4 => some (.four 3 9 4 8)
  | 9, 5 => some (.four 3 6 8 9)
  | 9, 6 => some (.four 2 9 3 7)
  | 9, 7 => some (.four 2 9 3 7)
  | 10, 0 => some (.path ![0,6,7,2,3,4,9])
  | 10, 1 => some (.four 0 9 5 6)
  | 10, 2 => some (.path ![0,5,9,7,2,3,8])
  | 10, 3 => some (.four 0 9 5 6)
  | 10, 4 => some (.four 3 9 4 8)
  | 10, 5 => some (.four 0 9 5 6)
  | 10, 6 => some (.four 3 9 4 8)
  | 10, 7 => some (.four 0 9 5 6)
  | 11, 0 => some (.path ![4,3,2,7,6,0,9])
  | 11, 1 => some (.four 0 9 5 6)
  | 11, 2 => some (.four 0 7 6 9)
  | 11, 3 => some (.four 0 7 6 9)
  | 11, 4 => some (.four 0 8 6 9)
  | 11, 5 => some (.four 0 8 6 9)
  | 11, 6 => some (.four 0 7 6 9)
  | 11, 7 => some (.four 0 7 6 9)
  | 12, 1 => some (.four 3 6 8 9)
  | 12, 2 => some (.four 0 7 6 9)
  | 12, 3 => some (.four 0 7 6 9)
  | 12, 4 => some (.four 0 8 6 9)
  | 12, 5 => some (.four 0 8 6 9)
  | 12, 6 => some (.four 0 7 6 9)
  | 12, 7 => some (.four 0 7 6 9)
  | 13, 0 => some (.path ![0,6,7,2,3,4,9])
  | 13, 1 => some (.four 0 9 1 6)
  | 13, 2 => some (.four 1 7 2 9)
  | 13, 3 => some (.four 0 9 1 6)
  | 13, 4 => some (.four 3 9 4 8)
  | 13, 5 => some (.four 0 9 1 6)
  | 13, 6 => some (.four 1 7 2 9)
  | 13, 7 => some (.four 0 9 1 6)
  | 14, 0 => some (.path ![4,5,9,2,7,6,8])
  | 14, 1 => some (.four 0 9 5 6)
  | 14, 3 => some (.four 0 9 5 6)
  | 14, 4 => some (.four 2 8 3 9)
  | 14, 5 => some (.four 0 9 5 6)
  | 14, 6 => some (.four 2 8 3 9)
  | 14, 7 => some (.four 0 9 5 6)
  | _, _ => none
def CertCheck {n : ℕ} (R : Fin n → Fin n → Prop) : Option (SmallCert n) → Prop
| none => False
| some c => CertTrue R c

noncomputable instance {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] (c : Option (SmallCert n)) :
    Decidable (CertCheck R c) := by
  cases c <;> unfold CertCheck <;> infer_instance

theorem certCheck_elim {n : ℕ} {R : Fin n → Fin n → Prop} {C : Option (SmallCert n)}
    (h : CertCheck R C) : ∃ c, CertTrue R c := by
  cases C with
  | none => exact h.elim
  | some c => exact ⟨c,h⟩

noncomputable def anchorB (a b : Fin 15) : Fin 3 → Fin 6 → Bool :=
  fun i => contactsB (![0,a,b] i)

def anchorE (i j : Fin 3) : Bool := decide
  ((i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0))

theorem anchor_cert (a b : Fin 15) :
    contactsB a 0 = false → contactsB b 0 = false →
    ((a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3)) ∨
      CertCheck (SmallRel (anchorB a b) anchorE) (anchorTable a b) := by
  revert a b
  decide

noncomputable def extraB (a : Fin 15) : Fin 4 → Fin 6 → Bool :=
  fun i => contactsB (![0,2,3,a] i)

def extraE (mask : Fin 8) (i j : Fin 4) : Bool :=
  if i.val < 3 then
    if j.val < 3 then decide ((i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0))
    else mask.val.testBit i.val
  else if j.val < 3 then mask.val.testBit j.val else false

theorem extra_cert (a : Fin 15) (b : Fin 8) :
    ((a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 3) ∨ (a = 12 ∧ b = 0) ∨ (a = 14 ∧ b = 2)) ∨
      CertCheck (SmallRel (extraB a) (extraE b)) (extraTable a b) := by
  revert a b
  decide

def optionProfiles (i : Fin 4) : Fin 15 := ![1,4,12,14] i
def optionMasks (i : Fin 4) : Fin 8 := ![4,3,0,2] i

noncomputable def doubleExtraB (a b : Fin 4) : Fin 5 → Fin 6 → Bool :=
  fun i => contactsB (![0,2,3,optionProfiles a,optionProfiles b] i)

def doubleExtraE (a b : Fin 4) (edge : Bool) (i j : Fin 5) : Bool :=
  if i.val < 3 then
    if j.val < 3 then decide ((i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0))
    else (optionMasks (if j.val = 3 then a else b)).val.testBit i.val
  else if j.val < 3 then (optionMasks (if i.val = 3 then a else b)).val.testBit j.val
  else if i=j then false else edge

private def doubleTable (a b : Fin 4) (e : Bool) : Option (SmallCert 11) :=
  match a.val, b.val, e with
  | 0, 1, false => some (.path ![0,1,9,8,3,4,10])
  | 0, 1, true => some (.four 6 9 8 10)
  | 0, 2, true => some (.four 0 9 1 10)
  | 0, 3, false => some (.path ![0,5,10,2,3,8,9])
  | 0, 3, true => some (.four 1 10 2 9)
  | 1, 2, false => some (.path ![1,0,10,3,4,9,7])
  | 1, 2, true => some (.four 0 9 6 10)
  | 1, 3, false => some (.path ![0,6,9,4,3,2,10])
  | 1, 3, true => some (.four 2 9 7 10)
  | 2, 3, false => some (.path ![4,3,9,0,6,7,10])
  | 2, 3, true => some (.four 0 10 5 9)
  | _, _, _ => none

theorem double_extra_cert (a b : Fin 4) (e : Bool) : a < b →
    (a = 0 ∧ b = 2 ∧ e = false) ∨
    CertCheck (SmallRel (doubleExtraB a b) (doubleExtraE a b e)) (doubleTable a b e) := by
  revert a b e
  decide
end Graffiti133Hex

/- Original module: HexHighAnchor133 -/

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} (F : Frame G)

private def relabelIndex (a : Fin 6) (rev : Bool) (j : Fin 6) :=
  if rev then a-j else a+j

private lemma relabelIndex_inj (a : Fin 6) (rev : Bool) : Function.Injective (relabelIndex a rev) := by
  intro i j
  have h : ∀ a rev (i j : Fin 6), relabelIndex a rev i = relabelIndex a rev j → i=j := by decide
  exact h a rev i j

private lemma relabelIndex_adj : ∀ a rev (i j : Fin 6),
    Cyclic (relabelIndex a rev i) (relabelIndex a rev j) ↔ Cyclic i j := by decide

def relabel (a : Fin 6) (rev : Bool) : Frame G where
  c := F.c ∘ relabelIndex a rev
  inj := F.inj.comp (relabelIndex_inj a rev)
  adj i j := (F.adj _ _).trans (relabelIndex_adj a rev i j)
  h4 := F.h4
  no7 := F.no7

private lemma stay_out {x : V} (hx : Outside F.c x) (a : Fin 6) (rev : Bool) :
    Outside (F.relabel a rev).c x := fun _ => hx _

private lemma change_single {x : V} {i : Fin 6} (hx : F.Single x (relabelIndex a rev i)) :
    (F.relabel a rev).Single x i := by
  refine ⟨F.stay_out hx.1 a rev,fun j => ?_⟩
  change G.Adj x (F.c (relabelIndex a rev j)) ↔ _
  rw [hx.2]
  exact ⟨fun e => relabelIndex_inj a rev e,congrArg _⟩

private lemma profile_one (a : Fin 6) :
    ∀ j : Fin 6, contactsB ⟨a.val,by omega⟩ j=true ↔ j=a := by
  intro j
  simp [contactsB,contact,a.isLt]

private lemma anchor_patterns {x y z : V} (hx : F.Single x 0)
    (hy : F.Near y) (hz : F.Near z)
    (exy : G.Adj x y) (exz : G.Adj x z) (eyz : ¬G.Adj y z) (nyz : y ≠ z)
    (cy : ¬G.Adj y (F.c 0)) (cz : ¬G.Adj z (F.c 0)) :
    (F.Single y 2 ∧ F.Single z 3) ∨ (F.Single y 3 ∧ F.Single z 2) ∨
    (F.Single y 3 ∧ F.Single z 4) ∨ (F.Single y 4 ∧ F.Single z 3) := by
  classical
  obtain ⟨a,ha⟩ := F.profile_exists hy
  obtain ⟨b,hb⟩ := F.profile_exists hz
  have ac : contactsB a 0=false := Bool.eq_false_iff.mpr (fun e => cy ((ha _).mp e))
  have bc : contactsB b 0=false := Bool.eq_false_iff.mpr (fun e => cz ((hb _).mp e))
  rcases anchor_cert a b ac bc with ok | bad
  · have H (a : Fin 15) (u : V) (hu : Outside F.c u)
        (h : ∀ j, contactsB a j=true ↔ G.Adj u (F.c j)) (i : Fin 6) (eq : a.val=i.val) :
        F.Single u i := by
      refine ⟨hu,fun j => (h j).symm.trans ?_⟩
      have tt : a = ⟨i.val,by omega⟩ := Fin.ext eq
      exact tt.symm ▸ profile_one i j
    rcases ok with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨H 2 y hy.1 ha 2 rfl,H 3 z hz.1 hb 3 rfl⟩
    · exact Or.inr (Or.inl ⟨H 3 y hy.1 ha 3 rfl,H 2 z hz.1 hb 2 rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨H 3 y hy.1 ha 3 rfl,H 4 z hz.1 hb 4 rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨H 4 y hy.1 ha 4 rfl,H 3 z hz.1 hb 3 rfl⟩))
  · obtain ⟨cert,hcert⟩ := certCheck_elim bad
    let e : Fin 3 → V := ![x,y,z]
    have ei : Function.Injective e := by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp [e,exy.ne,Ne.symm exy.ne,exz.ne,Ne.symm exz.ne,nyz,Ne.symm nyz] at h ⊢
    have off (i : Fin 3) : Outside F.c (e i) := by
      fin_cases i
      · exact hx.1
      · exact hy.1
      · exact hz.1
    have hB (i : Fin 3) (j : Fin 6) : anchorB a b i j=true ↔ G.Adj (e i) (F.c j) := by
      fin_cases i
      · simpa [anchorB,e] using (profile_one 0 j).trans ((hx.2 j).symm)
      · simpa [anchorB,e] using ha j
      · simpa [anchorB,e] using hb j
    have hE (i j : Fin 3) : anchorE i j=true ↔ G.Adj (e i) (e j) := by
      fin_cases i <;> fin_cases j <;>
        simp [anchorE,e,G.loopless,exy,exy.symm,exz,exz.symm,eyz,show ¬G.Adj z y from fun h => eyz h.symm]
    exact (F.reject_small e ei off hB hE cert hcert).elim

private theorem high_neighbors {x : V} (high : 3 ≤ localIndependence G x)
    {i : Fin 6} (hx : F.Single x i) :
    ∃ y z, y ≠ z ∧ G.Adj x y ∧ G.Adj x z ∧ ¬G.Adj y z ∧
      F.Near y ∧ F.Near z ∧ ¬G.Adj y (F.c i) ∧ ¬G.Adj z (F.c i) := by
  classical
  obtain ⟨A,hA,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
  obtain ⟨hN,hI⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA
  let B := A.filter (fun w => w=F.c i ∨ G.Adj w (F.c i))
  have cb : B.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha,ha'⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb,hb'⟩ := Finset.mem_filter.mp hb
    exact F.stamp_uniq (hx.1 i) (hN _ ha) (hN _ hb) (hI _ ha _ hb) ha' hb'
  let C := A \ B
  have Bsub : B ⊆ A := Finset.filter_subset _ _
  have sum := Finset.card_sdiff_add_card_eq_card Bsub
  have c2 : 1 < C.card := by
    change C.card+B.card=A.card at sum
    omega
  obtain ⟨y,hy,z,hz,yz⟩ := Finset.one_lt_card.mp c2
  have eY := hN y (Finset.mem_sdiff.mp hy).1
  have eZ := hN z (Finset.mem_sdiff.mp hz).1
  have nch (u : V) (hu : u∈C) : u ≠ F.c i ∧ ¬G.Adj u (F.c i) := by
    obtain ⟨hu,hb⟩ := Finset.mem_sdiff.mp hu
    exact ⟨fun h => hb (Finset.mem_filter.mpr ⟨hu,Or.inl h⟩),
      fun h => hb (Finset.mem_filter.mpr ⟨hu,Or.inr h⟩)⟩
  have near (u : V) (hu : u∈C) : F.Near u := by
    have e := hN u (Finset.mem_sdiff.mp hu).1
    have out : Outside F.c u := by
      intro j he
      have h := (hx.2 j).mp (he ▸ e)
      exact (nch u hu).1 (he.trans (congrArg F.c h))
    refine ⟨out,?_⟩
    apply Classical.byContradiction
    intro bad
    have fu : F.Far u := ⟨out,fun j h => bad ⟨j,h⟩⟩
    obtain ⟨j,hj⟩ := F.far_edge_opposite ⟨hx.1,⟨i,(hx.2 _).mpr rfl⟩⟩ fu e
    have e1 := (hx.2 _).mp ((hj.2 (frontInd j)).mpr (Or.inl rfl))
    have e2 := (hx.2 _).mp ((hj.2 (frontInd j+3)).mpr (Or.inr rfl))
    exact (by decide : ∀ j : Fin 3, frontInd j ≠ frontInd j+3) j (e1.trans e2.symm)
  exact ⟨y,z,yz,eY,eZ,hI _ (Finset.mem_sdiff.mp hy).1 _ (Finset.mem_sdiff.mp hz).1,
    near y hy,near z hz,(nch y hy).2,(nch z hz).2⟩

structure Anchor (F : Frame G) where
  x : V
  y : V
  z : V
  sx : F.Single x 0
  sy : F.Single y 2
  sz : F.Single z 3
  xy : G.Adj x y
  xz : G.Adj x z
  yz : ¬G.Adj y z
  nd : y ≠ z

theorem high_has_anchor {x : V} {i : Fin 6} (hx : F.Single x i)
    (hhigh : 3 ≤ localIndependence G x) : ∃ H : Frame G, Nonempty (Anchor H) := by
  let H := F.relabel i false
  have h0 : relabelIndex i false 0=i := by simp [relabelIndex]
  have hx' : H.Single x 0 := F.change_single (h0.symm ▸ hx)
  obtain ⟨y,z,nes,ex,ez,eyz,hy,hz,cy,cz⟩ := H.high_neighbors hhigh hx'
  rcases H.anchor_patterns hx' hy hz ex ez eyz nes cy cz with t | t | t | t
  · exact ⟨H,⟨⟨x,y,z,hx',t.1,t.2,ex,ez,eyz,nes⟩⟩⟩
  · exact ⟨H,⟨⟨x,z,y,hx',t.2,t.1,ez,ex,fun e => eyz e.symm,nes.symm⟩⟩⟩
  · exact ⟨H.relabel 0 true,⟨⟨x,z,y,H.change_single hx',H.change_single t.2,
      H.change_single t.1,ez,ex,fun e => eyz e.symm,nes.symm⟩⟩⟩
  · exact ⟨H.relabel 0 true,⟨⟨x,y,z,H.change_single hx',H.change_single t.1,
      H.change_single t.2,ex,ez,eyz,nes⟩⟩⟩

#print axioms high_has_anchor
end Frame
end Graffiti133Hex

/- Original module: HexHighExtra133 -/

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {F : Frame G}

namespace Anchor
variable (A : Anchor F)

def station (i : Fin 3) : V := ![A.x,A.y,A.z] i

lemma station_inj : Function.Injective A.station := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [station,A.xy.ne,Ne.symm A.xy.ne,A.xz.ne,Ne.symm A.xz.ne,A.nd,Ne.symm A.nd] at h ⊢

lemma station_out (i : Fin 3) : Outside F.c (A.station i) := by
  fin_cases i
  · exact A.sx.1
  · exact A.sy.1
  · exact A.sz.1

lemma station_profile (i : Fin 3) (j : Fin 6) :
    anchorB 2 3 i j=true ↔ G.Adj (A.station i) (F.c j) := by
  fin_cases i
  · exact (by
      simp [station,anchorB,contactsB,contact,A.sx.2,show (0:Fin 15).val<6 by decide])
  · exact (by
      simp [station,anchorB,contactsB,contact,A.sy.2,show (2:Fin 15).val<6 by decide])
  · exact (by
      simp [station,anchorB,contactsB,contact,A.sz.2,show (3:Fin 15).val<6 by decide]
      rfl)

lemma station_edges (i j : Fin 3) :
    anchorE i j=true ↔ G.Adj (A.station i) (A.station j) := by
  fin_cases i <;> fin_cases j <;>
    simp [station,anchorE,G.loopless,A.xy,A.xy.symm,A.xz,A.xz.symm,A.yz,
      show ¬G.Adj A.z A.y from fun h => A.yz h.symm]

def Extra (v : V) (i : Fin 4) : Prop :=
  (∀ j, contactsB (optionProfiles i) j=true ↔ G.Adj v (F.c j)) ∧
  (∀ j : Fin 3, (optionMasks i).val.testBit j.val=true ↔ G.Adj v (A.station j))

private def mask3 (c : Fin 3 → Bool) : Fin 8 :=
  ⟨(if c 0 then 1 else 0)+(if c 1 then 2 else 0)+(if c 2 then 4 else 0),by split <;> split <;> split <;> decide⟩

private lemma mask3_spec : ∀ (c : Fin 3 → Bool) (i : Fin 3),
    (mask3 c).val.testBit i.val = c i := by decide

theorem extra_classify {v : V} (hv : F.Near v) (nv : ∀ i, v ≠ A.station i) :
    ∃ i, A.Extra v i := by
  classical
  obtain ⟨t,ht⟩ := F.profile_exists hv
  let c : Fin 3 → Bool := fun i => decide (G.Adj v (A.station i))
  let b := mask3 c
  have bm (i : Fin 3) : b.val.testBit i.val=true ↔ G.Adj v (A.station i) := by
    rw [mask3_spec c i]
    simp [c]
  rcases extra_cert t b with ok | bad
  · have form (i : Fin 4) (hp : optionProfiles i=t) (hm : optionMasks i=b) : A.Extra v i :=
      ⟨fun j => hp.symm ▸ ht j,fun j => hm.symm ▸ bm j⟩
    rcases ok with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨0,form 0 h1.symm h2.symm⟩
    · exact ⟨1,form 1 h1.symm h2.symm⟩
    · exact ⟨2,form 2 h1.symm h2.symm⟩
    · exact ⟨3,form 3 h1.symm h2.symm⟩
  · obtain ⟨cert,hcert⟩ := certCheck_elim bad
    let e : Fin 4 → V := ![A.x,A.y,A.z,v]
    have nX : v ≠ A.x := nv 0
    have nY : v ≠ A.y := nv 1
    have nZ : v ≠ A.z := nv 2
    have ei : Function.Injective e := by
      intro i j h
      fin_cases i <;> fin_cases j <;>
        simp [e,A.xy.ne,Ne.symm A.xy.ne,A.xz.ne,Ne.symm A.xz.ne,A.nd,Ne.symm A.nd,
          nX,Ne.symm nX,nY,Ne.symm nY,nZ,Ne.symm nZ] at h ⊢
    have hO (i : Fin 4) : Outside F.c (e i) := by
      fin_cases i
      · exact A.sx.1
      · exact A.sy.1
      · exact A.sz.1
      · exact hv.1
    have hB (i : Fin 4) (j : Fin 6) : extraB t i j=true ↔ G.Adj (e i) (F.c j) := by
      fin_cases i
      · exact A.station_profile 0 j
      · exact A.station_profile 1 j
      · exact A.station_profile 2 j
      · simpa [extraB,e] using ht j
    have hE (i j : Fin 4) : extraE b i j=true ↔ G.Adj (e i) (e j) := by
      have mb (i : Fin 3) := bm i
      fin_cases i <;> fin_cases j <;>
        first | exact mb 0 | exact mb 1 | exact mb 2 |
          (first | simpa only [G.adj_comm] using mb 0 | simpa only [G.adj_comm] using mb 1 |
            simpa only [G.adj_comm] using mb 2) |
          (simp [extraE,e,G.loopless,A.xy,A.xy.symm,A.xz,A.xz.symm,A.yz,
            show ¬G.Adj A.z A.y from fun h => A.yz h.symm])
    exact (F.reject_small e ei hO hB hE cert hcert).elim

/-- All four admissible optional profiles occur at most once. -/
theorem extra_unique {v w : V} (i : Fin 4) (hv : A.Extra v i) (hw : A.Extra w i) : v=w := by
  have hs : ∀ i : Fin 4,
      (∃ j k : Fin 6, j≠k ∧ contactsB (optionProfiles i) j=true ∧ contactsB (optionProfiles i) k=true) ∨
      ∃ j : Fin 6, ∃ a : Fin 3, contactsB (optionProfiles i) j=true ∧
        (optionMasks i).val.testBit a.val=true := by decide
  rcases hs i with ⟨j,k,n,hj,hk⟩ | ⟨j,a,hj,ha⟩
  · exact F.h4 (F.c j) (F.c k) v w (F.inj.ne n) ((hv.1 _).mp hj).symm
      ((hv.1 _).mp hk).symm ((hw.1 _).mp hj).symm ((hw.1 _).mp hk).symm
  · exact F.h4 (F.c j) (A.station a) v w (Ne.symm (A.station_out a j))
      ((hv.1 _).mp hj).symm ((hv.2 _).mp ha).symm
      ((hw.1 _).mp hj).symm ((hw.2 _).mp ha).symm

#print axioms extra_classify
#print axioms extra_unique
end Anchor
end Frame
end Graffiti133Hex

/- Original module: HexHighPair133 -/

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {F : Frame G}

namespace Anchor
variable (A : Anchor F)

theorem extra_pair {v w : V} {a b : Fin 4}
    (ha : A.Extra v a) (hb : A.Extra w b) (hab : a < b)
    (hv : Outside F.c v) (hw : Outside F.c w)
    (nv : ∀ i, v ≠ A.station i) (nw : ∀ i, w ≠ A.station i) :
    a = 0 ∧ b = 2 ∧ ¬ G.Adj v w := by
  classical
  let p : Bool := decide (G.Adj v w)
  have hp : p=true ↔ G.Adj v w := by simp [p]
  rcases double_extra_cert a b p hab with approved | bad
  · exact ⟨approved.1,approved.2.1,fun e => by simp [approved.2.2] at hp; exact hp e⟩
  · obtain ⟨cert,hcert⟩ := certCheck_elim bad
    have nV : v ≠ w := by
      intro eq
      have h : ∀ j, contactsB (optionProfiles a) j = contactsB (optionProfiles b) j := by
        intro j
        exact Bool.eq_iff_iff.mpr ((ha.1 j).trans (eq.symm ▸ (hb.1 j).symm))
      have distinct : ∀ a b : Fin 4, a < b →
          ¬(∀ j, contactsB (optionProfiles a) j = contactsB (optionProfiles b) j) := by decide
      exact distinct a b hab h
    let e : Fin 5 → V := ![A.x,A.y,A.z,v,w]
    have nX : v ≠ A.x := nv 0
    have nY : v ≠ A.y := nv 1
    have nZ : v ≠ A.z := nv 2
    have nX' : w ≠ A.x := nw 0
    have nY' : w ≠ A.y := nw 1
    have nZ' : w ≠ A.z := nw 2
    have hI : Function.Injective e := by
      intro i j h
      fin_cases i <;> fin_cases j <;>
        simp [e,A.xy.ne,Ne.symm A.xy.ne,A.xz.ne,Ne.symm A.xz.ne,A.nd,Ne.symm A.nd,
          nX,Ne.symm nX,nY,Ne.symm nY,nZ,Ne.symm nZ,
          nX',Ne.symm nX',nY',Ne.symm nY',nZ',Ne.symm nZ',nV,Ne.symm nV] at h ⊢
    have hO (i : Fin 5) : Outside F.c (e i) := by
      fin_cases i
      · exact A.sx.1
      · exact A.sy.1
      · exact A.sz.1
      · exact hv
      · exact hw
    have hB (i : Fin 5) (j : Fin 6) : doubleExtraB a b i j=true ↔ G.Adj (e i) (F.c j) := by
      fin_cases i
      · simpa [doubleExtraB,e,anchorB,station] using A.station_profile 0 j
      · simpa [doubleExtraB,e,anchorB,station] using A.station_profile 1 j
      · simpa [doubleExtraB,e,anchorB,station] using A.station_profile 2 j
      · simpa [doubleExtraB,e] using ha.1 j
      · simpa [doubleExtraB,e] using hb.1 j
    have hE (i j : Fin 5) : doubleExtraE a b p i j=true ↔ G.Adj (e i) (e j) := by
      have pb (i : Fin 3) := hb.2 i
      have pa (i : Fin 3) := ha.2 i
      fin_cases i <;> fin_cases j <;>
        first | exact pa 0 | exact pa 1 | exact pa 2 |
          exact pb 0 | exact pb 1 | exact pb 2 | exact hp | exact (show p = true ↔ G.Adj w v from ⟨fun h => (hp.mp h).symm,fun h => hp.mpr h.symm⟩) |
          (first | simpa only [G.adj_comm] using pa 0 | simpa only [G.adj_comm] using pa 1 |
            simpa only [G.adj_comm] using pa 2 | simpa only [G.adj_comm] using pb 0 |
            simpa only [G.adj_comm] using pb 1 | simpa only [G.adj_comm] using pb 2 |
            simpa only [G.adj_comm] using hp) |
          (simp [doubleExtraE,e,G.loopless,A.xy,A.xy.symm,A.xz,A.xz.symm,A.yz,
            show ¬G.Adj A.z A.y from fun h => A.yz h.symm])
    exact (F.reject_small e hI hO hB hE cert hcert).elim


private noncomputable def farModelB (i : Fin 5) : Fin 6 → Bool :=
  if i=4 then fun _ => false else contactsB (![0,2,3,14,0] i)

private def farModelE (i j : Fin 5) : Bool := decide
  ((i=0 ∧ (j=1 ∨ j=2)) ∨ (j=0 ∧ (i=1 ∨ i=2)) ∨
   (i=1 ∧ j=3) ∨ (i=3 ∧ j=1) ∨ (i=3 ∧ j=4) ∨ (i=4 ∧ j=3))

private lemma far_model_cert :
    CertTrue (SmallRel farModelB farModelE) (.path ![0,6,8,3,2,9,10]) := by decide

theorem no_far_extra_three {v r : V} (hv : A.Extra v 3) (ho : Outside F.c v)
    (nv : ∀ i, v ≠ A.station i) (hr : F.Far r) (ev : G.Adj v r) : False := by
  classical
  let e : Fin 5 → V := ![A.x,A.y,A.z,v,r]
  have nX : v ≠ A.x := nv 0
  have nY : v ≠ A.y := nv 1
  have nZ : v ≠ A.z := nv 2
  have rX : r ≠ A.x := fun he => hr.2 0 (he.symm ▸ (A.sx.2 0).mpr rfl)
  have rY : r ≠ A.y := fun he => hr.2 2 (he.symm ▸ (A.sy.2 2).mpr rfl)
  have rZ : r ≠ A.z := fun he => hr.2 3 (he.symm ▸ (A.sz.2 3).mpr rfl)
  have rx : ¬G.Adj A.x r := by
    intro he
    obtain ⟨k,hk⟩ := F.far_edge_opposite ⟨A.sx.1,⟨0,(A.sx.2 0).mpr rfl⟩⟩ hr he
    have h := ((A.sx.2 _).mp ((hk.2 _).mpr (Or.inl rfl))).trans
      ((A.sx.2 _).mp ((hk.2 _).mpr (Or.inr rfl))).symm
    exact (by decide : ∀ k : Fin 3, frontInd k ≠ frontInd k+3) k h
  have ry : ¬G.Adj A.y r := by
    intro he
    obtain ⟨k,hk⟩ := F.far_edge_opposite ⟨A.sy.1,⟨2,(A.sy.2 2).mpr rfl⟩⟩ hr he
    have h := ((A.sy.2 _).mp ((hk.2 _).mpr (Or.inl rfl))).trans
      ((A.sy.2 _).mp ((hk.2 _).mpr (Or.inr rfl))).symm
    exact (by decide : ∀ k : Fin 3, frontInd k ≠ frontInd k+3) k h
  have rz : ¬G.Adj A.z r := by
    intro he
    obtain ⟨k,hk⟩ := F.far_edge_opposite ⟨A.sz.1,⟨3,(A.sz.2 3).mpr rfl⟩⟩ hr he
    have h := ((A.sz.2 _).mp ((hk.2 _).mpr (Or.inl rfl))).trans
      ((A.sz.2 _).mp ((hk.2 _).mpr (Or.inr rfl))).symm
    exact (by decide : ∀ k : Fin 3, frontInd k ≠ frontInd k+3) k h
  have hI : Function.Injective e := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp [e,A.xy.ne,Ne.symm A.xy.ne,A.xz.ne,Ne.symm A.xz.ne,A.nd,Ne.symm A.nd,
        nX,Ne.symm nX,nY,Ne.symm nY,nZ,Ne.symm nZ,rX,Ne.symm rX,rY,Ne.symm rY,rZ,Ne.symm rZ,
        ev.ne,Ne.symm ev.ne] at h ⊢
  have hO (i : Fin 5) : Outside F.c (e i) := by
    fin_cases i
    · exact A.sx.1
    · exact A.sy.1
    · exact A.sz.1
    · exact ho
    · exact hr.1
  have hB (i : Fin 5) (j : Fin 6) : farModelB i j=true ↔ G.Adj (e i) (F.c j) := by
    fin_cases i
    · simpa [farModelB,e,anchorB,station] using A.station_profile 0 j
    · simpa [farModelB,e,anchorB,station] using A.station_profile 1 j
    · simpa [farModelB,e,anchorB,station] using A.station_profile 2 j
    · exact hv.1 j
    · simp [farModelB,e,hr.2 j]
  have hE (i j : Fin 5) : farModelE i j=true ↔ G.Adj (e i) (e j) := by
    have pe (i : Fin 3) := hv.2 i
    fin_cases i <;> fin_cases j <;>
      first |
        exact pe 0 | exact pe 1 | exact pe 2 |
        (first | simpa only [G.adj_comm] using pe 0 | simpa only [G.adj_comm] using pe 1 |
          simpa only [G.adj_comm] using pe 2) |
        (simp [farModelE,e,G.loopless,A.xy,A.xy.symm,A.xz,A.xz.symm,A.yz,ev,ev.symm,rx,ry,rz,
          show ¬G.Adj A.z A.y from fun h => A.yz h.symm,
          show ¬G.Adj r A.x from fun h => rx h.symm,
          show ¬G.Adj r A.y from fun h => ry h.symm,
          show ¬G.Adj r A.z from fun h => rz h.symm])
  exact F.reject_small e hI hO hB hE _ far_model_cert

#print axioms extra_pair
#print axioms no_far_extra_three
end Anchor
end Frame
end Graffiti133Hex

/- Original module: HexHighNoFar133 -/

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {F : Frame G}

namespace Anchor
variable (A : Anchor F)

theorem opp_not_station {x : V} {i : Fin 3} (hi : F.Opp x i) :
    ∀ s, x ≠ A.station s := by
  have ns {j : Fin 6} (h : F.Single x j) : False := by
    have h1 := (h.2 _).mp ((hi.2 _).mpr (Or.inl rfl))
    have h2 := (h.2 _).mp ((hi.2 _).mpr (Or.inr rfl))
    exact (by decide : ∀ i : Fin 3, frontInd i ≠ frontInd i+3) i (h1.trans h2.symm)
  intro s eq
  fin_cases s
  · change x=A.x at eq
    exact ns (eq.symm ▸ A.sx)
  · change x=A.y at eq
    exact ns (eq.symm ▸ A.sy)
  · change x=A.z at eq
    exact ns (eq.symm ▸ A.sz)

theorem any_far_opp_is_two {o r : V} {j : Fin 3} (ho : F.Opp o j)
    (hr : F.Far r) (e : G.Adj o r) : A.Extra o 2 := by
  have nv := A.opp_not_station ho
  obtain ⟨k,hk⟩ := A.extra_classify ⟨ho.1,frontInd j,(ho.2 _).mpr (Or.inl rfl)⟩ nv
  have check : ∀ a : Fin 4, ∀ i : Fin 3,
      (∀ l, contactsB (optionProfiles a) l=true ↔ l=frontInd i ∨ l=frontInd i+3) →
      a=2 ∨ a=3 := by decide
  rcases check k j (fun l => (hk.1 l).trans (ho.2 l)) with rfl | rfl
  · exact hk
  · exact (A.no_far_extra_three hk ho.1 nv hr e).elim

include A in
theorem high_no_far (hc : G.Connected) (hm : ∀ r, 2 ≤ localIndependence G r) :
    ∀ r, ¬F.Far r := by
  classical
  intro r hr
  obtain ⟨o,i,hoi,hor⟩ := F.far_has_opp hc hm r hr
  have hO := A.any_far_opp_is_two hoi hr hor
  have allSides (a : V) (ha : G.Adj r a) : F.Far a ∨ a=o := by
    by_cases f : F.Far a
    · exact Or.inl f
    · obtain ⟨j,hj⟩ := F.far_neighbor_opp hr ha.symm f
      exact Or.inr (A.extra_unique 2 (A.any_far_opp_is_two hj hr ha.symm) hO)
  have allFar (a : V) (ha : F.Far a) : G.Adj o a := by
    obtain ⟨w,j,hw,ewa⟩ := F.far_has_opp hc hm a ha
    exact A.extra_unique 2 (A.any_far_opp_is_two hw ha ewa) hO ▸ ewa
  obtain ⟨S,hS,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) r
  obtain ⟨nh,ih⟩ := Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hS
  have least := hm r
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (show 1<S.card by omega)
  have ra := nh a ha
  have rb := nh b hb
  rcases allSides a ra with fA | rfl <;> rcases allSides b rb with fB | rfl
  · exact ab (F.h4 r o a b hor.ne.symm ra (allFar _ fA) rb (allFar _ fB))
  · exact ih a ha _ hb (allFar _ fA).symm
  · exact ih _ ha b hb (allFar _ fB)
  · exact ab rfl

#print axioms high_no_far
end Anchor
end Frame
end Graffiti133Hex

/- Original module: HexHighModel133 -/

namespace Graffiti133Hex
open Frame
open Graffiti133NoFive Finset
open scoped BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000

abbrev HighSlot := Fin 6 ⊕ (Fin 3 ⊕ Fin 4)
def cSlot (i : Fin 6) : HighSlot := .inl i
def sSlot (i : Fin 3) : HighSlot := .inr (.inl i)
def eSlot (i : Fin 4) : HighSlot := .inr (.inr i)

def SlotAdj : HighSlot → HighSlot → Prop
| .inl i, .inl j => Cyclic i j
| .inl j, .inr (.inl i) => anchorB 2 3 i j = true
| .inr (.inl i), .inl j => anchorB 2 3 i j = true
| .inl j, .inr (.inr i) => contactsB (optionProfiles i) j = true
| .inr (.inr i), .inl j => contactsB (optionProfiles i) j = true
| .inr (.inl i), .inr (.inl j) => anchorE i j = true
| .inr (.inr i), .inr (.inl j) => (optionMasks i).val.testBit j.val = true
| .inr (.inl j), .inr (.inr i) => (optionMasks i).val.testBit j.val = true
| .inr (.inr _), .inr (.inr _) => False

noncomputable instance : DecidableRel SlotAdj := by
  intro i j
  cases i with
  | inl i => cases j with
      | inl j => unfold SlotAdj; infer_instance
      | inr j => cases j <;> unfold SlotAdj <;> infer_instance
  | inr i =>
    cases i <;> cases j
    all_goals first | (unfold SlotAdj; infer_instance) | (rename_i q; cases q <;> unfold SlotAdj <;> infer_instance)

def SlotActive (b : Fin 4 → Bool) : HighSlot → Bool
| .inl _ | .inr (.inl _) => true
| .inr (.inr i) => b i

def activeSlots (b : Fin 4 → Bool) : Finset HighSlot :=
  Finset.univ.filter (fun i => SlotActive b i=true)

noncomputable def slotDegree (S : Finset HighSlot) (i : HighSlot) : ℕ :=
  (S.filter (SlotAdj i)).card

def Legal (b : Fin 4 → Bool) : Prop :=
  ∀ i j : Fin 4, i<j → b i = true → b j = true → i=0 ∧ j=2

instance (b : Fin 4 → Bool) : Decidable (Legal b) := by
  unfold Legal
  infer_instance

theorem model_budget (b : Fin 4 → Bool) (hb : Legal b) :
    (∑ i∈activeSlots b, slotDegree (activeSlots b) i) ≤ 3*(activeSlots b).card := by
  revert b
  decide

#print axioms model_budget
end Graffiti133Hex

/- Original module: HexHighSum133 -/

namespace Graffiti133Hex
namespace Frame
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {F : Frame G}

namespace Anchor
variable (A : Anchor F)

private def Label (v : V) : HighSlot → Prop
| .inl i => v=F.c i
| .inr (.inl i) => v=A.station i
| .inr (.inr i) => Outside F.c v ∧ (∀ j, v ≠ A.station j) ∧ A.Extra v i

private theorem label_exists (noFar : ∀ v, ¬F.Far v) (v : V) : ∃ i, A.Label v i := by
  classical
  by_cases out : Outside F.c v
  · by_cases station : ∃ i, v=A.station i
    · obtain ⟨i,hi⟩ := station
      exact ⟨sSlot i,hi⟩
    · have no (i : Fin 3) : v ≠ A.station i := fun h => station ⟨i,h⟩
      have near : F.Near v := by
        refine ⟨out,?_⟩
        apply Classical.byContradiction
        intro h
        exact noFar v ⟨out,fun i e => h ⟨i,e⟩⟩
      obtain ⟨i,hi⟩ := A.extra_classify near no
      exact ⟨eSlot i,out,no,hi⟩
  · obtain ⟨i,hi⟩ := F.exists_cycle out
    exact ⟨cSlot i,hi⟩

private theorem label_inj {v w : V} {i : HighSlot} (h : A.Label v i) (hw : A.Label w i) : v=w := by
  rcases i with i | i
  · exact h.trans hw.symm
  · rcases i with i | i
    · exact h.trans hw.symm
    · exact A.extra_unique i h.2.2 hw.2.2

private theorem label_functional {v : V} {i j : HighSlot}
    (h : A.Label v i) (hj : A.Label v j) : i=j := by
  have cp : ∀ a b : Fin 4,
      (∀ i, (contactsB (optionProfiles a) i=true ↔ contactsB (optionProfiles b) i=true)) →
      a=b := by decide
  cases i with
  | inl a =>
    cases j with
    | inl b => exact congrArg cSlot (F.inj (h.symm.trans hj))
    | inr j =>
      cases j with
      | inl b => exact (A.station_out b a (hj.symm.trans h)).elim
      | inr b => exact (hj.1 a h).elim
  | inr i =>
    cases i with
    | inl a =>
      cases j with
      | inl b => exact (A.station_out a b (h.symm.trans hj)).elim
      | inr j =>
        cases j with
        | inl b => exact congrArg sSlot (A.station_inj (h.symm.trans hj))
        | inr b => exact (hj.2.1 a h).elim
    | inr a =>
      cases j with
      | inl b => exact (h.1 b hj).elim
      | inr j =>
        cases j with
        | inl b => exact (h.2.1 b hj).elim
        | inr b =>
          exact congrArg eSlot (cp a b (fun l => (h.2.2.1 l).trans (hj.2.2.1 l).symm))

private theorem label_adjacency {v w : V} {i j : HighSlot}
    (hi : A.Label v i) (hj : A.Label w j) : G.Adj v w ↔ SlotAdj i j := by
  rcases i with a | a
  · rcases j with b | b
    · change v=F.c a at hi
      change w=F.c b at hj
      simpa only [hi,hj,SlotAdj] using F.adj a b
    · rcases b with b | b
      · change v=F.c a at hi
        change w=A.station b at hj
        rw [hi,hj,G.adj_comm]
        exact (A.station_profile b a).symm
      · change v=F.c a at hi
        rw [hi,G.adj_comm]
        exact (hj.2.2.1 a).symm
  · rcases a with a | a
    · rcases j with b | b
      · change v=A.station a at hi
        change w=F.c b at hj
        rw [hi,hj]
        exact (A.station_profile a b).symm
      · rcases b with b | b
        · change v=A.station a at hi
          change w=A.station b at hj
          rw [hi,hj]
          exact (A.station_edges a b).symm
        · change v=A.station a at hi
          rw [hi,G.adj_comm]
          exact (hj.2.2.2 a).symm
    · rcases j with b | b
      · change w=F.c b at hj
        rw [hj]
        exact (hi.2.2.1 b).symm
      · rcases b with b | b
        · change w=A.station b at hj
          rw [hj]
          exact (hi.2.2.2 b).symm
        · refine ⟨fun h => ?_,False.elim⟩
          rcases lt_trichotomy a b with lt | eq | gt
          · exact (A.extra_pair hi.2.2 hj.2.2 lt hi.1 hj.1 hi.2.1 hj.2.1).2.2 h
          · subst b
            exact h.ne (A.label_inj hi hj)
          · exact (A.extra_pair hj.2.2 hi.2.2 gt hj.1 hi.1 hj.2.1 hi.2.1).2.2 h.symm

include A in
theorem high_hex_budget (hc : G.Connected) (hm : ∀ r, 2 ≤ localIndependence G r) :
    (∑ x, localIndependence G x) ≤ 3 * Fintype.card V := by
  classical
  let f (v : V) : HighSlot := Classical.choose (A.label_exists (A.high_no_far hc hm) v)
  have hf (v : V) : A.Label v (f v) := Classical.choose_spec (A.label_exists (A.high_no_far hc hm) v)
  have inj : Function.Injective f := by
    intro v w h
    exact A.label_inj (hf v) (h.symm ▸ hf w)
  let S := (Finset.univ : Finset V).image f
  have cover (i : HighSlot) : i∈S ↔ ∃ v, A.Label v i := by
    constructor
    · intro h
      obtain ⟨v,_,hv⟩ := Finset.mem_image.mp h
      exact ⟨v,hv ▸ hf v⟩
    · rintro ⟨v,hv⟩
      exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,A.label_functional (hf v) hv⟩
  let b (i : Fin 4) := decide (eSlot i∈S)
  have hb (i : Fin 4) : b i=true ↔ eSlot i ∈ S := by simp [b]
  have isActive : activeSlots b = S := by
    ext i
    rcases i with i | i
    · have hs := (cover (cSlot i)).mpr ⟨F.c i,rfl⟩
      simp [activeSlots,SlotActive,show Sum.inl i∈S from hs]
    · rcases i with i | i
      · have hs := (cover (sSlot i)).mpr ⟨A.station i,rfl⟩
        simp [activeSlots,SlotActive,show Sum.inr (Sum.inl i)∈S from hs]
      · simpa [activeSlots,SlotActive] using hb i
  have legal : Legal b := by
    intro i j hij hi hj
    obtain ⟨v,hv⟩ := (cover _).mp ((hb i).mp hi)
    obtain ⟨w,hw⟩ := (cover _).mp ((hb j).mp hj)
    exact ⟨(A.extra_pair hv.2.2 hw.2.2 hij hv.1 hw.1 hv.2.1 hw.2.1).1,
      (A.extra_pair hv.2.2 hw.2.2 hij hv.1 hw.1 hv.2.1 hw.2.1).2.1⟩
  have bound (v : V) : localIndependence G v ≤ slotDegree S (f v) := by
    obtain ⟨T,hT,eq⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
    have near := (Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hT).1
    have sub (w : V) (hw : w∈T) : f w∈S.filter (SlotAdj (f v)) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨w,Finset.mem_univ _,rfl⟩,
        (A.label_adjacency (hf v) (hf w)).mp (near w hw)⟩
    rw [←eq]
    exact Finset.card_le_card_of_injOn f sub inj.injOn
  have bd := model_budget b legal
  rw [isActive] at bd
  calc
    (∑ v, localIndependence G v) ≤ ∑ v, slotDegree S (f v) :=
      Finset.sum_le_sum (fun v _ => bound v)
    _ = ∑ j∈S,slotDegree S j := by
      symm
      exact Finset.sum_image (fun _ _ _ _ h => inj h)
    _ ≤ 3*S.card := bd
    _ = 3*Fintype.card V := by simp [S,Finset.card_image_of_injective _ inj]

end Anchor

theorem hex_budget (F : Frame G) (hc : G.Connected) (hm : ∀ r, 2 ≤ localIndependence G r) :
    (∑ x, localIndependence G x) ≤ 3 * Fintype.card V := by
  by_cases low : ∀ x i, F.Single x i → localIndependence G x ≤ 2
  · exact F.low_hex_budget hc hm low
  · push_neg at low
    obtain ⟨x,i,hx,hhigh⟩ := low
    obtain ⟨H,⟨anchor⟩⟩ := F.high_has_anchor hx (by omega)
    exact anchor.high_hex_budget hc hm

#print axioms hex_budget
end Frame
end Graffiti133Hex

/- Original module: StrictP7Reduction133 -/

namespace Graffiti133FarPentagon
open SimpleGraph Graffiti133 Graffiti133Revisit Graffiti133NoFive Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
universe u

variable {V : Type u} [Fintype V]

private def HasP7 (G : SimpleGraph V) : Prop :=
  ∃ f : Fin 7 → V, InducedPath G f

private theorem connected_peel_P7_strict (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G)
    (hD : 3*Fintype.card V < (∑ v, localIndependence G v))
    (core : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W), J.Connected →
      FourCycleFree J → (∀ v, 2 ≤ localIndependence J v) →
      3*Fintype.card W < (∑ v, localIndependence J v) →
      HasP7 J) :
    HasP7 G := by
  classical
  let Claim (n : ℕ) := ∀ (W : Type u) [Fintype W] (J : SimpleGraph W),
    Fintype.card W=n → J.Connected → FourCycleFree J →
    3*Fintype.card W < (∑ v, localIndependence J v) →
    HasP7 J
  have aux (n : ℕ) : Claim n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ G hn hC h4 dens
      letI := hC.nonempty
      by_cases hmin : ∀ v, 2 ≤ localIndependence G v
      · exact core W G hC h4 hmin dens
      push_neg at hmin
      obtain ⟨v,hv⟩ := hmin
      let S : Set W := {w | w ≠ v}
      let H := G.induce S
      have hpos : 0 < Fintype.card W := Fintype.card_pos
      have hS : Fintype.card S + 1 = Fintype.card W := by
        have hs : Fintype.card S = Fintype.card W - 1 := by
          change Fintype.card {x : W // ¬ x = v} = _
          rw [Fintype.card_subtype_compl]
          rw [show Fintype.card {x : W // x = v} = 1 from Fintype.card_unique]
        omega
      have h4' : FourCycleFree H := by
        intro a b x y hab hax hbx hay hby
        apply Subtype.ext
        exact h4 _ _ _ _ (fun h => hab (Subtype.ext h)) hax hbx hay hby
      have non : Nonempty S := by
        have pos : 0 < (∑ v, localIndependence G v) := by omega
        obtain ⟨a,b,ab⟩ : ∃ a b, G.Adj a b := by
          apply Classical.byContradiction
          intro no
          have eq : ∀ x, localIndependence G x = 0 := by
            intro x
            obtain ⟨A,hA,hc⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) x
            rw [← hc,Finset.card_eq_zero]
            apply Finset.not_nonempty_iff_eq_empty.mp
            rintro ⟨a,ha⟩
            exact no ⟨x,a,(Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1 a ha⟩
          simp [eq] at pos
        by_cases ha : a=v
        · exact ⟨⟨b,(ha ▸ ab.ne).symm⟩⟩
        · exact ⟨⟨a,ha⟩⟩
      have hConn : H.Connected := connected_delete_low_local G hC v (by omega) non
      have loss := local_sum_delete_bound G h4 v
      have dH : 3*Fintype.card S < (∑ w, localIndependence H w) := by
        rw [← hS,Nat.mul_add,Nat.mul_one] at dens
        change (∑ w, localIndependence G w) ≤ (∑ w : S, localIndependence H w) +
          2*localIndependence G v at loss
        omega
      have witness := ih _ (by omega : Fintype.card S < n) S H rfl hConn h4' dH
      obtain ⟨f,hf⟩ := witness
      exact ⟨fun i => (f i).val,Subtype.val_injective.comp hf.1,hf.2⟩
  exact aux (Fintype.card V) V G rfl hc h4 hD

open Graffiti133Hex in
theorem strict_mean_three_using_holes (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (hmean : 3 < averageLocal G)
    (six : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W) (_F : Graffiti133Hex.Frame J),
      J.Connected → (∀ r, 2 ≤ localIndependence J r) →
      (∑ r, localIndependence J r) ≤ 3*Fintype.card W)
    (seven : ∀ (W : Type u) [Fintype W] (J : SimpleGraph W), J.Connected →
      FourCycleFree J → (∀ r, 2 ≤ localIndependence J r) →
      ¬HasP7 J → ¬Nonempty (Hole J 6) → Hole J 7 →
      (∑ r, localIndependence J r) ≤ 3*Fintype.card W) :
    ∃ f : Fin 7 → V, InducedPath G f := by
  classical
  letI := hc.nonempty
  have dens : 3*Fintype.card V < (∑ r, localIndependence G r) := by
    unfold averageLocal at hmean
    have hpos : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α:=V)
    have h := (lt_div_iff₀ hpos).mp hmean
    rw [← Nat.cast_sum] at h
    exact_mod_cast h
  apply connected_peel_P7_strict G hc h4 dens
  intro W _ J hJ h4 hm hsum
  letI := hJ.nonempty
  have av : 3 ≤ averageLocal J := by
    unfold averageLocal
    have hpos : (0 : ℚ) < Fintype.card W := by exact_mod_cast Fintype.card_pos (α:=W)
    apply (le_div_iff₀ hpos).mpr
    rw [← Nat.cast_sum]
    exact_mod_cast hsum.le
  by_cases p : HasP7 J
  · exact p
  by_cases hh : Nonempty (Hole J 6)
  · obtain ⟨H⟩ := hh
    exact ((not_lt_of_ge (six W J ⟨H,h4,p⟩ hJ hm)) hsum).elim
  rcases local_mean_three_path_or_hole J hJ h4 av with xx | xx | xx
  · exact xx
  · exact (hh xx).elim
  · obtain ⟨H⟩ := xx
    exact ((not_lt_of_ge (seven W J hJ h4 hm p hh H)) hsum).elim

#print axioms strict_mean_three_using_holes
end Graffiti133FarPentagon

/- Original module: P7FullBand133 -/

namespace Graffiti133Revisit
open Graffiti133 Graffiti133FarPentagon SimpleGraph Finset
set_option linter.unusedSectionVars false
universe u
variable {V : Type u} [Fintype V]

/-- Connected C4-free graphs of mean local independence strictly above
three contain an induced P7. -/
theorem P7_of_strict_mean_three (G : SimpleGraph V) (hc : G.Connected)
    (h4 : FourCycleFree G) (ha : 3 < averageLocal G) :
    ∃ f : Fin 7 → V, InducedPath G f := by
  apply strict_mean_three_using_holes G hc h4 ha
  · intro W _ J F c m
    exact Graffiti133Hex.Frame.hex_budget F c m
  · intro W _ J c h4 m no7 no6 H
    exact (Graffiti133C7Only.sum_lt_three_of_hole_seven_no_six H h4 no7 no6 c m).le

/-- Additional unrounded #133 range: mean at most four, radius at most three. -/
theorem conjecture133_real_four_radius_three (G : SimpleGraph V) (hc : G.Connected)
    (hr : radius G ≤ 3) (ha : averageLocal G ≤ 4) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases low : averageLocal G ≤ 3
    · exact conjecture133_real_full_three G hc low
    · refine ⟨7,?_,P7_of_strict_mean_three G hc h4 (lt_of_not_ge low)⟩
      simp only [rhs133,if_pos h4,pow_one]
      change (radius G : ℚ) + averageLocal G ≤ 7
      have hr' : (radius G : ℚ) ≤ 3 := by exact_mod_cast hr
      linarith
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl h4)

/-- Additional unrounded #133 range: mean at most five, radius at most two. -/
theorem conjecture133_real_five_radius_two (G : SimpleGraph V) (hc : G.Connected)
    (hr : radius G ≤ 2) (ha : averageLocal G ≤ 5) :
    ∃ k : ℕ, rhs133 G ≤ (k : ℚ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases low : averageLocal G ≤ 4
    · exact conjecture133_real_four_radius_two G hc hr low
    · have high : 3 < averageLocal G := by linarith
      refine ⟨7,?_,P7_of_strict_mean_three G hc h4 high⟩
      simp only [rhs133,if_pos h4,pow_one]
      change (radius G : ℚ) + averageLocal G ≤ 7
      have hr' : (radius G : ℚ) ≤ 2 := by exact_mod_cast hr
      linarith
  · exact conjecture133_low_average_or_four_cycle G hc (Or.inl h4)

/-- Floor reading, radius at most three, floored mean at most four. -/
theorem conjecture133_floor_four_radius_three (G : SimpleGraph V) (hc : G.Connected)
    (hr : radius G ≤ 3) (ha : ⌊averageLocal G⌋ ≤ 4) :
    ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases hs : ⌊averageLocal G⌋ ≤ 3
    · exact conjecture133_full_floor_three G hc hs
    · have ht : (4 : ℤ) ≤ ⌊averageLocal G⌋ := by omega
      have hq : (4 : ℚ) ≤ (⌊averageLocal G⌋ : ℚ) := by exact_mod_cast ht
      have hgt := (show (3 : ℚ) < 4 by norm_num).trans_le (hq.trans (Int.floor_le _))
      refine ⟨7,?_,P7_of_strict_mean_three G hc h4 hgt⟩
      simp only [catalogueRhs133,if_pos h4,pow_one]
      omega
  · exact conjecture133_floor_le_two_or_four_cycle G hc (Or.inl h4)

/-- Floor reading, radius at most two, floored mean at most five. -/
theorem conjecture133_floor_five_radius_two (G : SimpleGraph V) (hc : G.Connected)
    (hr : radius G ≤ 2) (ha : ⌊averageLocal G⌋ ≤ 5) :
    ∃ k : ℕ, catalogueRhs133 G ≤ (k : ℤ) ∧ ∃ f : Fin k → V, InducedPath G f := by
  classical
  by_cases h4 : FourCycleFree G
  · by_cases hs : ⌊averageLocal G⌋ ≤ 4
    · exact conjecture133_floor_four_radius_two G hc hr hs
    · have ht : (5 : ℤ) ≤ ⌊averageLocal G⌋ := by omega
      have hq : (5 : ℚ) ≤ (⌊averageLocal G⌋ : ℚ) := by exact_mod_cast ht
      have hgt := (show (3 : ℚ) < 5 by norm_num).trans_le (hq.trans (Int.floor_le _))
      refine ⟨7,?_,P7_of_strict_mean_three G hc h4 hgt⟩
      simp only [catalogueRhs133,if_pos h4,pow_one]
      omega
  · exact conjecture133_floor_le_two_or_four_cycle G hc (Or.inl h4)

#print axioms conjecture133_floor_four_radius_three
#print axioms conjecture133_floor_five_radius_two
#print axioms P7_of_strict_mean_three
#print axioms conjecture133_real_four_radius_three
#print axioms conjecture133_real_five_radius_two
end Graffiti133Revisit
