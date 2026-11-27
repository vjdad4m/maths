import P7OrHole133

namespace Graffiti133Hex
open SimpleGraph Graffiti133 Graffiti133RevisitSix Graffiti133NoFive Finset
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem lift_spoke_any {m n : ℕ} (hm : 0 < m) (H : Hole G n)
    (x : V) (hx : Outside H.c x) {b : Fin n → Bool}
    (hb : ∀ i, b i = true ↔ G.Adj x (H.c i))
    (path : Fin m → Fin (n+1)) (inj : Function.Injective path)
    (hs : ∀ i j : Fin m, i < j → (SpokeRel b (path i) (path j) ↔ i.val+1=j.val))
    (head : path ⟨0,hm⟩ = Fin.last n)
    (tail : ∀ i, 0 < i.val → (path i).val < n) :
    ∃ p : Fin m → V, InducedPath G p ∧ p ⟨0,hm⟩ = x ∧
      ∀ i, 0 < i.val → ∃ j, p i = H.c j := by
  let g (r : Fin (n+1)) : V := if hr : r.val < n then H.c ⟨r.val,hr⟩ else x
  have gLast : g (Fin.last n) = x := by simp [g]
  have ginj : Function.Injective g := by
    intro a b eq
    by_cases hA : a.val < n <;> by_cases hB : b.val < n
    · have he := H.inj (show H.c ⟨a.val,hA⟩ = H.c ⟨b.val,hB⟩ by
        simpa only [g,dif_pos hA,dif_pos hB] using eq)
      exact Fin.ext (congrArg (fun z : Fin n => z.val) he)
    · exact False.elim (hx ⟨a.val,hA⟩ (by simpa only [g,dif_pos hA,dif_neg hB] using eq.symm))
    · exact False.elim (hx ⟨b.val,hB⟩ (by simpa only [g,dif_neg hA,dif_pos hB] using eq))
    · apply Fin.ext
      have := a.isLt
      have := b.isLt
      omega
  have hrel (a q : Fin (n+1)) : G.Adj (g a) (g q) ↔ SpokeRel b a q := by
    by_cases hA : a.val < n <;> by_cases hQ : q.val < n
    · simpa only [g,SpokeRel,dif_pos hA,dif_pos hQ] using H.adj ⟨a.val,hA⟩ ⟨q.val,hQ⟩
    · simpa only [g,SpokeRel,dif_pos hA,dif_neg hQ,G.adj_comm] using (hb ⟨a.val,hA⟩).symm
    · simpa only [g,SpokeRel,dif_neg hA,dif_pos hQ] using (hb ⟨q.val,hQ⟩).symm
    · simp [g,SpokeRel,hA,hQ,G.loopless]
  refine ⟨g ∘ path,⟨ginj.comp inj,fun a q he => (hrel _ _).trans (hs a q he)⟩,
    ?_,?_⟩
  · change g (path ⟨0,hm⟩) = x
    rw [head,gLast]
  · intro i hi
    exact ⟨⟨_,tail i hi⟩,dif_pos (tail i hi)⟩

structure Frame (G : SimpleGraph V) extends Hole G 6 where
  h4 : FourCycleFree G
  no7 : ¬∃ p : Fin 7 → V, InducedPath G p

namespace Frame
variable (F : Frame G)

def Single (x : V) (i : Fin 6) : Prop :=
  Outside F.c x ∧ ∀ j, G.Adj x (F.c j) ↔ j=i
def Double (x : V) (i : Fin 6) : Prop :=
  Outside F.c x ∧ ∀ j, G.Adj x (F.c j) ↔ j=i ∨ j=i+1

def frontInd (i : Fin 3) : Fin 6 := i.castLE (by decide)
def Opp (x : V) (i : Fin 3) : Prop :=
  Outside F.c x ∧ ∀ j, G.Adj x (F.c j) ↔ j=frontInd i ∨ j=frontInd i+3

def Near (x : V) : Prop := Outside F.c x ∧ ∃ i, G.Adj x (F.c i)
def Far (x : V) : Prop := Outside F.c x ∧ ∀ i, ¬G.Adj x (F.c i)

lemma near_not_far {x : V} (hn : F.Near x) (hf : F.Far x) : False := by
  obtain ⟨i,hi⟩ := hn.2
  exact hf.2 i hi

private lemma allowed6 : ∀ b : Fin 6 → Bool,
    (∀ i, b i = true → b (i+2) = false) → (∃ i, b i = true) →
    (∃ i, ∀ j, b j=true ↔ j=i) ∨ (∃ i, ∀ j, b j=true ↔ j=i ∨ j=i+1) ∨
      (∃ i : Fin 3, ∀ j, b j=true ↔ j=frontInd i ∨ j=frontInd i+3) := by decide

private lemma step6 : ∀ i : Fin 6, Cyclic i (i+1) ∧ Cyclic (i+1) (i+2) ∧ i≠i+2 := by decide

theorem classify {x : V} (hx : F.Near x) :
    (∃ i, F.Single x i) ∨ (∃ i, F.Double x i) ∨ ∃ i, F.Opp x i := by
  classical
  let b : Fin 6 → Bool := fun i => decide (G.Adj x (F.c i))
  have bt (i : Fin 6) : b i=true ↔ G.Adj x (F.c i) := by simp [b]
  have sep (i : Fin 6) (h : b i=true) : b (i+2)=false := by
    cases he : b (i+2)
    · rfl
    · have t := step6 i
      have eq := F.h4 (F.c i) (F.c (i+2)) x (F.c (i+1))
        (fun e => t.2.2 (F.inj e)) ((bt _).mp h).symm ((bt _).mp he).symm
        ((F.adj _ _).mpr t.1) ((F.adj _ _).mpr t.2.1).symm
      exact (hx.1 _ eq).elim
  obtain ⟨i,hi⟩ := hx.2
  rcases allowed6 b sep ⟨i,(bt _).mpr hi⟩ with a | a | a
  · obtain ⟨j,hj⟩ := a
    exact Or.inl ⟨j,hx.1,fun k => (bt k).symm.trans (hj k)⟩
  · obtain ⟨j,hj⟩ := a
    exact Or.inr (Or.inl ⟨j,hx.1,fun k => (bt k).symm.trans (hj k)⟩)
  · obtain ⟨j,hj⟩ := a
    exact Or.inr (Or.inr ⟨j,hx.1,fun k => (bt k).symm.trans (hj k)⟩)

theorem contact_forbid {x y : V} (hx : Outside F.c x) (hy : Outside F.c y)
    (e : G.Adj x y) {i j : Fin 6} (ex : G.Adj x (F.c i)) (ey : G.Adj y (F.c j)) :
    ¬Cyclic i j := by
  intro ed
  have h := F.h4 x (F.c j) y (F.c i) (hx j) e ey.symm ex ((F.adj _ _).mpr ed).symm
  exact hy _ h

theorem stamp_uniq {x y z : V} {i : Fin 6} (hx : x ≠ F.c i)
    (ex : G.Adj x y) (ez : G.Adj x z) (no : ¬G.Adj y z)
    (hy : y = F.c i ∨ G.Adj y (F.c i)) (hz : z = F.c i ∨ G.Adj z (F.c i)) :
    y=z := by
  rcases hy with hy | hy <;> rcases hz with hz | hz
  · exact hy.trans hz.symm
  · exact (no (hy.symm ▸ hz.symm)).elim
  · exact (no (hz.symm ▸ hy)).elim
  · exact F.h4 x (F.c i) y z hx ex hy.symm ez hz.symm

private def path6 (i : Fin 6) (positive : Bool) : Fin 6 → Fin 7 :=
  ![6,i.castSucc,(i+(if positive then 1 else 5)).castSucc,
    (i+(if positive then 2 else 4)).castSucc,(i+3).castSucc,
    (i+(if positive then 4 else 2)).castSucc]

private lemma normal6 : ∀ b : Fin 6 → Bool,
    ((∃ i, ∀ j,b j=true ↔ j=i) ∨ (∃ i, ∀ j,b j=true ↔ j=i ∨ j=i+1)) →
    ∃ i pos,
      (∀ a c : Fin 6,path6 i pos a=path6 i pos c → a=c) ∧
      (∀ a c : Fin 6,a<c → (SpokeRel b (path6 i pos a) (path6 i pos c) ↔ a.val+1=c.val)) ∧
      (∀ a : Fin 6,0 < a.val → (path6 i pos a).val < 6) := by decide

private theorem rooted6 {x : V} (hx : Outside F.c x)
    (kind : (∃ i, F.Single x i) ∨ ∃ i, F.Double x i) :
    ∃ p : Fin 6 → V, InducedPath G p ∧ p 0=x ∧
      ∀ j, 0 < j.val → ∃ i, p j=F.c i := by
  classical
  let b : Fin 6 → Bool := fun i => decide (G.Adj x (F.c i))
  have bt (i : Fin 6) : b i=true ↔ G.Adj x (F.c i) := by simp [b]
  have shape : (∃ i, ∀ j,b j=true ↔ j=i) ∨ (∃ i, ∀ j,b j=true ↔ j=i ∨ j=i+1) := by
    rcases kind with ⟨i,hi⟩ | ⟨i,hi⟩
    · exact Or.inl ⟨i,fun j => (bt j).trans (hi.2 j)⟩
    · exact Or.inr ⟨i,fun j => (bt j).trans (hi.2 j)⟩
  obtain ⟨i,pos,hi,he,ht⟩ := normal6 b shape
  exact lift_spoke_any (by decide) F.toHole x hx bt (path6 i pos) hi he rfl ht

private def antiPath4 (i : Fin 3) : Fin 4 → Fin 7 :=
  ![6,(frontInd i).castSucc,(frontInd i+1).castSucc,(frontInd i+2).castSucc]
private lemma anti4_ok : ∀ i : Fin 3, ∀ b : Fin 6 → Bool,
    (∀ j,b j=true ↔ j=frontInd i ∨ j=frontInd i+3) →
    (∀ a c : Fin 4,antiPath4 i a=antiPath4 i c → a=c) ∧
      (∀ a c : Fin 4,a<c → (SpokeRel b (antiPath4 i a) (antiPath4 i c) ↔ a.val+1=c.val)) ∧
      (∀ a : Fin 4,0 < a.val → (antiPath4 i a).val < 6) := by decide

theorem rooted4 {x : V} {i : Fin 3} (hx : F.Opp x i) :
    ∃ p : Fin 4 → V, InducedPath G p ∧ p 0=x ∧
      ∀ j, 0 < j.val → ∃ i, p j=F.c i := by
  classical
  let b : Fin 6 → Bool := fun i => decide (G.Adj x (F.c i))
  have bt (i : Fin 6) : b i=true ↔ G.Adj x (F.c i) := by simp [b]
  obtain ⟨a,c,tail⟩ := anti4_ok i b (fun j => (bt j).trans (hx.2 j))
  exact lift_spoke_any (by decide) F.toHole x hx.1 bt (antiPath4 i) a c rfl tail

/-- Only an antipodal frontier vertex can be adjacent to a far vertex. -/
theorem far_edge_opposite {x y : V} (hx : F.Near x) (hy : F.Far y)
    (e : G.Adj x y) : ∃ i, F.Opp x i := by
  classical
  rcases F.classify hx with single | double | opp
  · obtain ⟨p,hp,h0,ht⟩ := F.rooted6 hx.1 (Or.inl single)
    apply False.elim
    apply F.no7
    have off (i : Fin 6) : y ≠ p i := by
      intro eq
      by_cases h : i.val=0
      · have h' : i=0 := Fin.ext h
        rw [h',h0] at eq
        exact e.ne eq.symm
      · obtain ⟨j,hj⟩ := ht i (Nat.pos_of_ne_zero h)
        exact hy.1 j (eq.trans hj)
    have adj : G.Adj y (p 0) := h0.symm ▸ e.symm
    have no (i : Fin 6) (hi : 0 < i.val) : ¬ G.Adj y (p i) := by
      obtain ⟨j,hj⟩ := ht i hi
      exact fun eq => hy.2 j (hj ▸ eq)
    obtain ⟨q,hq,_,_⟩ := prepend_induced_with_positions (by decide) hp y off adj no
    exact ⟨q,hq⟩
  · obtain ⟨p,hp,h0,ht⟩ := F.rooted6 hx.1 (Or.inr double)
    apply False.elim
    apply F.no7
    have off (i : Fin 6) : y ≠ p i := by
      intro eq
      by_cases h : i.val=0
      · have h' : i=0 := Fin.ext h
        rw [h',h0] at eq
        exact e.ne eq.symm
      · obtain ⟨j,hj⟩ := ht i (Nat.pos_of_ne_zero h)
        exact hy.1 j (eq.trans hj)
    have adj : G.Adj y (p 0) := h0.symm ▸ e.symm
    have no (i : Fin 6) (hi : 0 < i.val) : ¬ G.Adj y (p i) := by
      obtain ⟨j,hj⟩ := ht i hi
      exact fun eq => hy.2 j (hj ▸ eq)
    obtain ⟨q,hq,_,_⟩ := prepend_induced_with_positions (by decide) hp y off adj no
    exact ⟨q,hq⟩
  · exact opp

end Frame
end Graffiti133Hex
