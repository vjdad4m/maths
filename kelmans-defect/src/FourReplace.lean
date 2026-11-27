import FourLadder
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.Sum

open Finset
namespace KelmansCactus.FourReplace
open ThreePort

/-- Two graphs plus a matched list of cross edges. The datum of
injective terminal maps is separate and used for the replacement. -/
def glue {X Y I : Type*} (L : SimpleGraph X) (R : SimpleGraph Y)
    (p : I → X) (q : I → Y) : SimpleGraph (X ⊕ Y) where
  Adj
    | .inl x, .inl y => L.Adj x y
    | .inr x, .inr y => R.Adj x y
    | .inl x, .inr y => ∃ i, p i=x ∧ q i=y
    | .inr y, .inl x => ∃ i, p i=x ∧ q i=y
  symm := by
    rintro (x|x) (y|y) h
    · exact h.symm
    · exact h
    · exact h
    · exact h.symm
  loopless := by
    rintro (x|x) h
    · exact L.loopless x h
    · exact R.loopless x h

def remains {X : Type*} [DecidableEq X] (D : Finset X) : Set X := {v | v ∉ D}

def Anchored {X I : Type*} [DecidableEq X]
    (L : SimpleGraph X) (p : I → X) : Prop :=
  ∀ D : Finset X, D.card≤2 → ∀ x : remains D,
    ∃ i, ∃ hi : p i ∉ D, (L.induce (remains D)).Reachable x ⟨p i,hi⟩

section Glue
variable {X Y I : Type*} [DecidableEq X] [DecidableEq Y]
variable {L : SimpleGraph X} {R : SimpleGraph Y} {p : I → X} {q : I → Y}

private def lIn {A : Finset X} {B : Finset Y} (x : remains A) : remains (A.disjSum B) :=
  ⟨.inl x.val,by change Sum.inl x.val ∉ A.disjSum B; rw [inl_mem_disjSum]; exact x.property⟩

private def rIn {A : Finset X} {B : Finset Y} (x : remains B) : remains (A.disjSum B) :=
  ⟨.inr x.val,by change Sum.inr x.val ∉ A.disjSum B; rw [inr_mem_disjSum]; exact x.property⟩

private def lHom {A : Finset X} {B : Finset Y} :
    L.induce (remains A) →g (glue L R p q).induce (remains (A.disjSum B)) :=
  ⟨lIn,fun h => h⟩

private def rHom {A : Finset X} {B : Finset Y} :
    R.induce (remains B) →g (glue L R p q).induce (remains (A.disjSum B)) :=
  ⟨rIn,fun h => h⟩

private theorem cross_adj {A : Finset X} {B : Finset Y} {i : I} (hi : p i∉A) (hj : q i∉B) :
    ((glue L R p q).induce (remains (A.disjSum B))).Adj
      (lIn ⟨p i,hi⟩) (rIn ⟨q i,hj⟩) := ⟨i,rfl,rfl⟩

private theorem split_left {A : Finset X} {B : Finset Y}
    {u : remains (A.disjSum B)} {x : X} (e : u.val = Sum.inl x) :
    ∃ d : x∉A, u = lIn ⟨x,d⟩ := by
  have hh := u.property
  change u.val ∉ A.disjSum B at hh
  rw [e] at hh
  exact ⟨by simpa using hh,Subtype.ext e⟩

private theorem split_right {A : Finset X} {B : Finset Y}
    {u : remains (A.disjSum B)} {x : Y} (e : u.val = Sum.inr x) :
    ∃ d : x∉B, u = rIn ⟨x,d⟩ := by
  have hh := u.property
  change u.val ∉ A.disjSum B at hh
  rw [e] at hh
  exact ⟨by simpa using hh,Subtype.ext e⟩

private theorem right_exit_walk {A : Finset X} {B : Finset Y}
    {v u : remains (A.disjSum B)}
    (walk : ((glue L R p q).induce (remains (A.disjSum B))).Walk u v)
    (hv : ∃ y, v.val = Sum.inl y) :
    ∀ (x : remains B), u = rIn x →
      ∃ i, p i ∉ A ∧ ∃ hq : q i ∉ B, (R.induce (remains B)).Reachable x ⟨q i,hq⟩ := by
  induction walk with
  | nil =>
    rintro x rfl
    obtain ⟨y,hy⟩ := hv
    cases hy
  | @cons u t v e walk ih =>
    rintro x rfl
    cases h : t.val with
    | inl z =>
      obtain ⟨nz,rfl⟩ := split_left h
      have e' : ∃ i, p i=z ∧ q i=x.val := e
      obtain ⟨i,eq1,eq2⟩ := e'
      have hq : q i ∉ B := eq2.symm ▸ x.property
      refine ⟨i, eq1.symm ▸ nz,hq,?_⟩
      have eql : (⟨q i,hq⟩ : remains B)=x := Subtype.ext eq2
      rw [eql]
    | inr z =>
      obtain ⟨nz,rfl⟩ := split_right h
      have edge : (R.induce (remains B)).Adj x ⟨z,nz⟩ := e
      obtain ⟨i,hp,hq,reach⟩ := ih hv ⟨z,nz⟩ rfl
      exact ⟨i,hp,hq,edge.reachable.trans reach⟩

private theorem right_exit {A : Finset X} {B : Finset Y}
    (con : ((glue L R p q).induce (remains (A.disjSum B))).Connected)
    (u : remains A) (x : remains B) :
    ∃ i, p i ∉ A ∧ ∃ hq : q i ∉ B, (R.induce (remains B)).Reachable x ⟨q i,hq⟩ :=
  (con (rIn x) (lIn u)).elim (fun w => right_exit_walk w ⟨u.val,rfl⟩ x rfl)

end Glue

variable {X Y Z I : Type*} [Fintype X] [Fintype Y] [Fintype Z] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq Z] [DecidableEq I]

omit [DecidableEq I] in
private theorem some_port {E : Type*} [DecidableEq E] {r : I → E}
    (hi : Function.Injective r) (cnt : 3≤Fintype.card I) {D : Finset E} (small : D.card≤2) :
    ∃ i, r i ∉ D := by
  classical
  by_contra! no
  let er : I ↪ E := ⟨r,hi⟩
  have sub : univ.map er ⊆ D := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_map.mp hx
    exact no i
  have bound := card_le_card sub
  rw [card_map,card_univ] at bound
  omega

omit [Fintype Y] [Fintype Z] [DecidableEq I] in
private theorem some_open_link {p : I→Z} {q : I→Y}
    (pi : Function.Injective p) (qi : Function.Injective q) (cnt : 3≤Fintype.card I)
    {A : Finset Z} {B : Finset Y} (small : A.card+B.card≤2) :
    ∃ i, p i∉A ∧ q i∉B := by
  classical
  by_contra! no
  let D : Finset (Z⊕Y) := A.disjSum B
  let f : I → (Z⊕Y) := fun i => if p i ∈ A then Sum.inl (p i) else Sum.inr (q i)
  have inj : Function.Injective f := by
    intro i j eq
    by_cases h : p i∈A <;> by_cases h' : p j∈A <;> simp [f,h,h'] at eq
    · exact pi eq
    · exact qi eq
  have sz : D.card≤2 := by simpa [D] using small
  obtain ⟨i,ni⟩ := some_port inj cnt sz
  by_cases ok : p i ∈ A
  · exact ni (by simp [f,D,ok])
  · exact ni (by simp [f,D,ok,no i ok])

omit [DecidableEq I] in
/-- Replace the left shore of a matching seam by any clean tester:
it stays connected after one deletion, and every component after
two deletions meets a surviving port. The opposite shore must be
internally connected before deletions. -/
theorem replace_preserves_three_connected
    {L : SimpleGraph X} {T : SimpleGraph Z} {R : SimpleGraph Y}
    {p : I→X} {r : I→Z} {q : I→Y}
    (orig : KelmansStarter.ThreeConnected (glue L R p q))
    (pp : Function.Injective p) (rp : Function.Injective r) (qp : Function.Injective q)
    (many : 4≤Fintype.card I)
    (right_conn : R.Connected)
    (test_conn : ∀ A : Finset Z, A.card≤1 → (T.induce (remains A)).Connected)
    (test_anchored : Anchored T r) :
    KelmansStarter.ThreeConnected (glue T R r q) := by
  classical
  have test_order : Fintype.card I≤Fintype.card Z := Fintype.card_le_of_injective _ rp
  refine ⟨by rw [Fintype.card_sum]; omega,?_⟩
  intro S small
  let A := S.toLeft
  let B := S.toRight
  have eqS : A.disjSum B = S := toLeft_disjSum_toRight
  have sizes : A.card+B.card≤2 := le_trans (card_toLeft_add_card_toRight.le) small
  change ((glue T R r q).induce (remains S)).Connected
  rw [← eqS]
  let W := (glue T R r q).induce (remains (A.disjSum B))
  obtain ⟨i,hi,hj⟩ := some_open_link rp qp (by omega) sizes
  apply (W.connected_iff_exists_forall_reachable).mpr
  refine ⟨lIn ⟨r i,hi⟩,?_⟩
  by_cases ac : A.card≤1
  · let J : Finset I := univ.filter fun j => r j∈A
    let C : Finset X := J.image p
    have leCA : C.card≤A.card := by
      have le : C.card≤J.card := card_image_le
      let er : I↪Z := ⟨r,rp⟩
      have sub : J.map er ⊆ A := by
        intro u hu
        obtain ⟨j,hj,rfl⟩ := mem_map.mp hu
        exact (mem_filter.mp hj).2
      have bound := card_le_card sub
      rw [card_map] at bound
      omega
    obtain ⟨j,hj⟩ := some_port pp (by omega : 3≤Fintype.card I) (le_trans leCA (by omega))
    have con : ((glue L R p q).induce (remains (C.disjSum B))).Connected :=
      orig.2 _ (by rw [card_disjSum]; omega)
    have right_to_test (u : remains B) : W.Reachable (rIn u) (lIn ⟨r i,hi⟩) := by
      obtain ⟨k,kC,kB,walk⟩ := right_exit con ⟨p j,hj⟩ u
      clear j hj
      have jA : r k ∉ A := fun hm => kC (mem_image.mpr ⟨k,mem_filter.mpr ⟨mem_univ _,hm⟩,rfl⟩)
      have y : W.Reachable (rIn u) (rIn ⟨q k,kB⟩) := walk.elim fun w => (w.map rHom).reachable
      have z : W.Reachable (lIn ⟨r k,jA⟩) (lIn ⟨r i,hi⟩) :=
        (test_conn A ac _ _).elim fun w => (w.map lHom).reachable
      exact y.trans ((cross_adj jA kB).reachable.symm.trans z)
    intro u
    cases hu : u.val with
    | inl x =>
      obtain ⟨hx,rfl⟩ := split_left hu
      exact (test_conn A ac _ _).elim fun w => (w.map lHom).reachable
    | inr x =>
      obtain ⟨hx,rfl⟩ := split_right hu
      exact (right_to_test ⟨x,hx⟩).symm
  · have b0 : B = ∅ := card_eq_zero.mp (by omega)
    have right : (R.induce (remains B)).Connected := by
      rw [b0]
      let f : R →g R.induce (remains (∅ : Finset Y)) := ⟨fun y => ⟨y,not_mem_empty _⟩,fun h => h⟩
      exact right_conn.map f (fun y => ⟨y.val,Subtype.ext rfl⟩)
    intro u
    cases hu : u.val with
    | inl x =>
      obtain ⟨hx,rfl⟩ := split_left hu
      obtain ⟨j,jA,joined⟩ := test_anchored A (by omega) ⟨x,hx⟩
      have hqj : q j ∉ B := by rw [b0]; exact not_mem_empty _
      have between : W.Reachable (rIn ⟨q i,hj⟩) (rIn ⟨q j,hqj⟩) :=
        (right _ _).elim fun w => (w.map rHom).reachable
      have last : W.Reachable (lIn ⟨r j,jA⟩) (lIn ⟨x,hx⟩) :=
        joined.symm.elim fun w => (w.map lHom).reachable
      exact (cross_adj hi hj).reachable.trans (between.trans ((cross_adj jA hqj).reachable.symm.trans last))
    | inr x =>
      obtain ⟨hx,rfl⟩ := split_right hu
      have between : W.Reachable (rIn ⟨q i,hj⟩) (rIn ⟨x,hx⟩) :=
        (right _ _).elim fun w => (w.map rHom).reachable
      exact (cross_adj hi hj).reachable.trans between

#print axioms replace_preserves_three_connected

private noncomputable def back {U W : Type*} (e : U ↪ W) (F : Finset W) : Finset U :=
  F.preimage e e.injective.injOn

private theorem back_mem {U W : Type*} {e : U ↪ W} {F : Finset W} {u : U} :
    u∈back e F ↔ e u∈F := mem_preimage

private theorem recover_map {U W : Type*} [Fintype U]
    (e : U ↪ W) {F : Finset W} (hF : F ⊆ univ.map e) : (back e F).map e = F := by
  ext v
  constructor
  · intro h
    obtain ⟨u,hu,rfl⟩ := mem_map.mp h
    exact back_mem.mp hu
  · intro hv
    obtain ⟨u,_,rfl⟩ := mem_map.mp (hF hv)
    exact mem_map.mpr ⟨u,back_mem.mpr hv,rfl⟩

private theorem local_pull {U W : Type*} [Fintype U] [DecidableEq U] [DecidableEq W]
    {J : SimpleGraph U} {K : SimpleGraph W} (e : U ↪ W)
    (adj : ∀ u v, K.Adj (e u) (e v) → J.Adj u v)
    {P : Finset (Finset W)} {S : Finset W} (sub : S ⊆ univ.map e)
    (h : Assemble.LocalPart K P S) :
    ∃ Q, Assemble.LocalPart J Q (back e S) := by
  classical
  have ms {t : Finset W} (ht : t ∈ P) : (back e t).map e = t :=
    recover_map e ((h.tile_sub K ht).trans sub)
  let Q := P.image (back e)
  refine ⟨Q,⟨?_,?_,?_⟩⟩
  · intro t ht
    obtain ⟨f,hf,rfl⟩ := mem_image.mp ht
    have tile := h.tile f hf
    have cardeq : (back e f).card = f.card := by rw [← card_map e,ms hf]
    obtain ⟨size,c,hc,hcenter⟩ := tile
    obtain ⟨u,hu,hu_eq⟩ := mem_map.mp ((ms hf).symm ▸ hc)
    refine ⟨cardeq.trans size,u,hu,?_⟩
    intro v hv ne
    apply adj
    rw [hu_eq]
    exact hcenter (e v) (back_mem.mp hv) (fun q => ne (e.injective (q.trans hu_eq.symm)))
  · intro t ht s hs ne
    obtain ⟨a,ha,rfl⟩ := mem_image.mp ht
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hs
    refine disjoint_left.mpr fun u ua ub => ?_
    exact disjoint_left.mp (h.disj a ha b hb (fun eq => ne (congrArg (back e) eq))) (back_mem.mp ua) (back_mem.mp ub)
  · ext u
    rw [back_mem,← h.cover]
    simp only [mem_biUnion,id_eq]
    constructor
    · rintro ⟨t,ht,hu⟩
      obtain ⟨s,hs,rfl⟩ := mem_image.mp ht
      exact ⟨s,hs,back_mem.mp hu⟩
    · rintro ⟨s,hs,hu⟩
      exact ⟨back e s,mem_image.mpr ⟨s,hs,rfl⟩,back_mem.mpr hu⟩

/-- Transport a full factor from an embedded graph's image. Edges on the
image may be restricted, but every available edge must pull back. -/
theorem full_factor_of_closed_image {U W : Type*} [Fintype U]
    [DecidableEq U] [DecidableEq W] {J : SimpleGraph U} {K : SimpleGraph W}
    (e : U ↪ W) (adj : ∀ u v, K.Adj (e u) (e v) → J.Adj u v)
    (h : Substitute.Closed K (univ.map e)) : KelmansStarter.HasP3Factor J := by
  obtain ⟨P,hP⟩ := h
  obtain ⟨Q,hQ⟩ := local_pull e adj Subset.rfl hP
  have b : back e ((univ : Finset U).map e) = univ := by
    ext u
    exact iff_of_true (back_mem.mpr (mem_map.mpr ⟨u,mem_univ _,rfl⟩)) (mem_univ _)
  rw [b] at hQ
  exact ⟨Q,hQ.tile,hQ.disj,hQ.cover⟩

private theorem from_image {U W JI : Type*} [Fintype U] [DecidableEq U] [DecidableEq W] [Fintype JI]
    {J : SimpleGraph U} {K : SimpleGraph W} (e : U ↪ W)
    (adj : ∀ u v, K.Adj (e u) (e v) → J.Adj u v) {p : JI→U} {w : JI→Nat}
    (sig : Signature (G:=K) (univ.map e) (fun i => e (p i)) w) :
    Signature (G:=J) univ p w := by
  obtain ⟨F,hF,fd,P,hP⟩ := sig
  have ms (i : JI) : (back e (F i)).map e = F i := recover_map e (hF i).2.inside
  refine ⟨fun i => back e (F i),?_,?_,?_⟩
  · intro i
    have cardeq : (back e (F i)).card = (F i).card := by rw [← card_map e,ms i]
    refine ⟨cardeq.trans (hF i).1,subset_univ _,?_,?_⟩
    · rintro ⟨u,hu⟩
      exact back_mem.mpr ((hF i).2.includes ⟨e u,back_mem.mp hu⟩)
    · intro u hu ne
      exact adj _ _ ((hF i).2.star _ (back_mem.mp hu) (fun er => ne (e.injective er)))
  · intro i j ne
    exact disjoint_left.mpr fun u hu hv => disjoint_left.mp (fd i j ne) (back_mem.mp hu) (back_mem.mp hv)
  · obtain ⟨Q,hQ⟩ := local_pull e adj (sdiff_subset : univ.map e \ univ.biUnion F ⊆ univ.map e) hP
    have eq : back e (univ.map e \ univ.biUnion F) = univ \ univ.biUnion (fun i => back e (F i)) := by
      ext u
      simp [back_mem,mem_biUnion]
    rw [eq] at hQ
    exact ⟨Q,hQ⟩

omit [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] [DecidableEq I] in
private theorem glue_seam {L : SimpleGraph X} {R : SimpleGraph Y} {p : I→X} {q : I→Y}
    (pi : Function.Injective p) (qi : Function.Injective q) :
    Seam (G:=glue L R p q) ((univ : Finset X).map Function.Embedding.inl)
      (fun i => Sum.inl (p i)) (fun i => Sum.inr (q i)) := by
  refine ⟨by simp,by simp,fun i j h => pi (Sum.inl.inj h),fun i j h => qi (Sum.inr.inj h),?_⟩
  rintro (a|a) ha (b|b) hb
  · simp at hb
  · change (∃ i, p i = a ∧ q i = b) ↔ _
    simp only [Sum.inl.injEq,Sum.inr.injEq]
  · simp at ha
  · simp at ha

private theorem complement_left :
    ((univ : Finset X).map (Function.Embedding.inl : X ↪ X⊕Y))ᶜ =
      ((univ : Finset Y).map Function.Embedding.inr) := by
  ext u
  cases u <;> simp

omit [DecidableEq I] in
/-- Exact compatibility on the two separate vertex sets. No factor gets
lost by pulling the seam certificate out of the disjoint-sum ambient graph. -/
theorem glued_factor_iff {L : SimpleGraph X} {R : SimpleGraph Y} {p : I→X} {q : I→Y}
    (pi : Function.Injective p) (qi : Function.Injective q) :
    KelmansStarter.HasP3Factor (glue L R p q) ↔
      ∃ u v : I→Nat, Signature (G:=L) univ p u ∧ Signature (G:=R) univ q v ∧
        ∀ i, Opposite (u i) (v i) := by
  rw [factor_iff_signatures (glue_seam pi qi), complement_left]
  constructor
  · rintro ⟨u,v,lu,rv,ok⟩
    exact ⟨u,v,from_image Function.Embedding.inl (fun _ _ h => h) lu,
      from_image Function.Embedding.inr (fun _ _ h => h) rv,ok⟩
  · rintro ⟨u,v,lu,rv,ok⟩
    exact ⟨u,v,FourLadder.signature_map Function.Embedding.inl (fun _ _ _ _ h => h) lu,
      FourLadder.signature_map Function.Embedding.inr (fun _ _ _ _ h => h) rv,ok⟩

omit [DecidableEq I] in
/-- Testers of any residue-preserving size: replace one side by a dominated
palette on fewer vertices, then lift the smaller graph's factor. -/
theorem transfer_factor {L : SimpleGraph X} {T : SimpleGraph Z} {R : SimpleGraph Y}
    {p : I→X} {r : I→Z} {q : I→Y}
    (pi : Function.Injective p) (ri : Function.Injective r) (qi : Function.Injective q)
    (dom : ∀ w, (∀ i, w i≤2) → Signature (G:=T) univ r w → Signature (G:=L) univ p w)
    (fact : KelmansStarter.HasP3Factor (glue T R r q)) :
    KelmansStarter.HasP3Factor (glue L R p q) := by
  obtain ⟨u,v,hu,hv,ok⟩ := (glued_factor_iff ri qi).mp fact
  have small : ∀ i, u i≤2 := by intro i; have z := ok i; unfold Opposite at z; omega
  exact (glued_factor_iff pi qi).mpr ⟨u,v,dom u small hu,hv,ok⟩

#print axioms glued_factor_iff
#print axioms transfer_factor

instance decidableGlue {U W J : Type*} [Fintype J] [DecidableEq U] [DecidableEq W]
    (L : SimpleGraph U) (R : SimpleGraph W) [DecidableRel L.Adj] [DecidableRel R.Adj]
    (p : J→U) (q : J→W) (u v : U⊕W) : Decidable ((glue L R p q).Adj u v) := by
  cases u <;> cases v <;> unfold glue <;> dsimp <;> infer_instance

theorem left_degree {U W J : Type*} [Fintype U] [Fintype W] [Fintype J]
    [DecidableEq U] [DecidableEq W]
    {L : SimpleGraph U} {R : SimpleGraph W} [DecidableRel L.Adj] [DecidableRel R.Adj]
    {p : J→U} {q : J→W} (pi : Function.Injective p) (a : U) :
    (glue L R p q).degree (Sum.inl a) =
      L.degree a + if (∃ i, p i=a) then 1 else 0 := by
  let S := univ.filter ((glue L R p q).Adj (Sum.inl a))
  rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  change S.card = _
  rw [← card_toLeft_add_card_toRight]
  have left : S.toLeft = L.neighborFinset a := by
    ext x
    simp only [mem_toLeft,S,mem_filter,mem_univ,true_and,SimpleGraph.mem_neighborFinset]
    rfl
  rw [left]
  change L.degree a + S.toRight.card = _
  congr 1
  by_cases h : ∃ i, p i=a
  · rw [if_pos h]
    obtain ⟨i,hi⟩ := h
    have rs : S.toRight = {q i} := by
      ext x
      simp only [mem_toRight,S,mem_filter,mem_univ,true_and,mem_singleton]
      change (∃ j, p j=a ∧ q j=x) ↔ x=q i
      constructor
      · rintro ⟨j,jp,jq⟩
        obtain rfl := pi (jp.trans hi.symm)
        exact jq.symm
      · rintro rfl
        exact ⟨i,hi,rfl⟩
    rw [rs,card_singleton]
  · rw [if_neg h]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_not_mem.mpr
    intro x hx
    have hx' := (mem_filter.mp (mem_toRight.mp hx)).2
    obtain ⟨i,hi,_⟩ := (show ∃ i, p i=a ∧ q i=x from hx')
    exact h ⟨i,hi⟩

theorem right_degree {U W J : Type*} [Fintype U] [Fintype W] [Fintype J]
    [DecidableEq U] [DecidableEq W]
    {L : SimpleGraph U} {R : SimpleGraph W} [DecidableRel L.Adj] [DecidableRel R.Adj]
    {p : J→U} {q : J→W} (qi : Function.Injective q) (a : W) :
    (glue L R p q).degree (Sum.inr a) =
      R.degree a + if (∃ i, q i=a) then 1 else 0 := by
  let S := univ.filter ((glue L R p q).Adj (Sum.inr a))
  rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter]
  change S.card = _
  rw [← card_toLeft_add_card_toRight,add_comm]
  have right : S.toRight = R.neighborFinset a := by
    ext x
    simp only [mem_toRight,S,mem_filter,mem_univ,true_and,SimpleGraph.mem_neighborFinset]
    rfl
  rw [right]
  change R.degree a + S.toLeft.card = _
  congr 1
  by_cases h : ∃ i, q i=a
  · rw [if_pos h]
    obtain ⟨i,hi⟩ := h
    have ls : S.toLeft = {p i} := by
      ext x
      simp only [mem_toLeft,S,mem_filter,mem_univ,true_and,mem_singleton]
      change (∃ j, p j=x ∧ q j=a) ↔ x=p i
      constructor
      · rintro ⟨j,jp,jq⟩
        obtain rfl := qi (jq.trans hi.symm)
        exact jp.symm
      · rintro rfl
        exact ⟨i,rfl,hi⟩
    rw [ls,card_singleton]
  · rw [if_neg h]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_not_mem.mpr
    intro x hx
    have hx' := (mem_filter.mp (mem_toLeft.mp hx)).2
    obtain ⟨i,_,hi⟩ := (show ∃ i, p i=x ∧ q i=a from hx')
    exact h ⟨i,hi⟩

omit [DecidableEq I] in
theorem replace_preserves_cubic
    {L : SimpleGraph X} {T : SimpleGraph Z} {R : SimpleGraph Y}
    [DecidableRel L.Adj] [DecidableRel T.Adj] [DecidableRel R.Adj]
    {p : I→X} {q : I→Y} {r : I→Z} (qi : Function.Injective q) (ri : Function.Injective r)
    (orig : ∀ x, (glue L R p q).degree x=3)
    (test : ∀ x, T.degree x = if (∃ i, r i=x) then 2 else 3) :
    ∀ x, (glue T R r q).degree x=3 := by
  rintro (x|x)
  · rw [left_degree ri,test]
    split <;> omega
  · rw [right_degree qi,← right_degree (L:=L) (p:=p) qi]
    exact orig (Sum.inr x)

private theorem quad_sum (w : Bool×Bool→ℕ) :
    (∑ i, w i) = (w (false,false)+w (false,true))+(w (true,false)+w (true,true)) := by
  have h : (univ : Finset (Bool×Bool)) = {(false,false),(false,true),(true,false),(true,true)} := by decide
  simp [h,add_assoc]

/-- If the left shore is spanned by a sufficiently long ladder rooted at
its corners, any strictly smaller congruent clean four-port tester
gives a valid graph-order reduction. No stronger conjecture is invoked:
the only input is z1 on the smaller graph. -/
theorem ladder_shore_reduction
    {L : SimpleGraph X} {R : SimpleGraph Y} {T : SimpleGraph Z}
    [DecidableRel L.Adj] [DecidableRel R.Adj] [DecidableRel T.Adj]
    {n : ℕ} (hn : 6≤n) (e : (Fin n × Bool)↪X) (covered : (univ : Finset (Fin n×Bool)).map e = univ)
    (ladder : ∀ u v, (FourLadder.ladder n).Adj u v → L.Adj (e u) (e v))
    {q : Bool×Bool→Y} {r : Bool×Bool→Z} (qi : Function.Injective q) (ri : Function.Injective r)
    (right_conn : R.Connected)
    (test_conn : ∀ A : Finset Z, A.card≤1 → (T.induce (remains A)).Connected)
    (test_anchored : Anchored T r)
    (test_degree : ∀ x, T.degree x = if (∃ i, r i=x) then 2 else 3)
    (less : Fintype.card Z < Fintype.card X)
    (same : Fintype.card Z%6 = Fintype.card X%6)
    (original_cubic : ∀ x, (glue L R (FourLadder.ports (by omega) e) q).degree x=3)
    (original_conn : KelmansStarter.ThreeConnected (glue L R (FourLadder.ports (by omega) e) q))
    (original_order : 6 ∣ Fintype.card (X⊕Y))
    (z1_smaller : ∀ (H : SimpleGraph (Z⊕Y)) (dec : DecidableRel H.Adj),
      Fintype.card (Z⊕Y) < Fintype.card (X⊕Y) → @KelmansStarter.Conjecture _ _ _ H dec) :
    KelmansStarter.HasP3Factor (glue L R (FourLadder.ports (by omega) e) q) := by
  let p := FourLadder.ports (by omega) e
  have pi : Function.Injective p := by
    rintro ⟨a,b⟩ ⟨c,d⟩ eq
    have eq' := e.injective eq
    have s := congrArg Prod.snd eq'
    have f := congrArg (fun x : Fin n×Bool => x.1.val) eq'
    change b=d at s
    change (if a then n-1 else 0)=(if c then n-1 else 0) at f
    have ac : a=c := by cases a <;> cases c <;> simp at f ⊢ <;> omega
    exact Prod.ext ac s
  have many : 4≤Fintype.card (Bool×Bool) := by decide
  have oc : 6 ∣ Fintype.card (Z⊕Y) := by
    rw [Fintype.card_sum,Nat.dvd_iff_mod_eq_zero]
    rw [Fintype.card_sum,Nat.dvd_iff_mod_eq_zero] at original_order
    omega
  have strictly : Fintype.card (Z⊕Y) < Fintype.card (X⊕Y) := by
    simp only [Fintype.card_sum]; omega
  have conn := replace_preserves_three_connected original_conn pi ri qi many right_conn test_conn test_anchored
  have cubic := replace_preserves_cubic qi ri original_cubic test_degree
  have hf := z1_smaller (glue T R r q) inferInstance strictly cubic conn oc
  apply transfer_factor pi ri qi _ hf
  intro w limit hw
  have wres := width_congruence hw
  rw [card_univ,quad_sum] at wres
  have ord : Fintype.card X = 2*n := by
    have cc := congrArg Finset.card covered
    simpa [Fintype.card_prod,mul_comm] using cc.symm
  let u (i : Bool×Bool) : Fin 3 := ⟨w i,by have h := limit i; omega⟩
  have residue : ((w (false,false)+w (false,true))+(w (true,false)+w (true,true)))%3=(2*n)%3 := by omega
  have hh := FourLadder.full_palette_of_ladder hn e ladder u residue
  rw [covered] at hh
  exact hh

#print axioms ladder_shore_reduction

/-- A one-vertex apex is a convenient route to certify shore anchoring:
all its incidences land at ports, and the apex stays present. -/
theorem anchored_of_apex {U J : Type*} [DecidableEq U] {T : SimpleGraph U} {p : J→U}
    (ok : ∀ D : Finset U, D.card≤2 →
      ((glue (⊥ : SimpleGraph Unit) T (fun _ : J => ()) p).induce
        (remains ((∅ : Finset Unit).disjSum D))).Connected) :
    Anchored T p := by
  intro D hd x
  obtain ⟨i,_,hi,hx⟩ := right_exit (ok D hd) ⟨(),not_mem_empty ()⟩ x
  exact ⟨i,hi,hx⟩


omit [DecidableEq I] in
/-- In a 3-connected matching cut with at most five edges, each shore
is connected. A component with at most two ports would be isolated
by deleting the corresponding vertices on the opposite side. -/
theorem right_connected_of_small_matching_cut
    {L : SimpleGraph X} {R : SimpleGraph Y} {p : I→X} {q : I→Y}
    (orig : KelmansStarter.ThreeConnected (glue L R p q)) (pi : Function.Injective p)
    (count : 3≤Fintype.card I ∧ Fintype.card I≤5) :
    R.Connected := by
  classical
  let C (x : Y) : Finset I := univ.filter fun i => R.Reachable x (q i)
  have many (x : Y) : 3≤(C x).card := by
    by_contra! small
    let D := (C x).image p
    have few : D.card≤2 := by
      have h : D.card≤(C x).card := card_image_le
      omega
    obtain ⟨j,hj⟩ := some_port pi count.1 few
    have con := orig.2 (D.disjSum (∅ : Finset Y)) (by simpa using few)
    obtain ⟨i,hn,_,hr⟩ := right_exit con ⟨p j,hj⟩ ⟨x,not_mem_empty x⟩
    let f : R.induce (remains (∅ : Finset Y)) →g R := ⟨Subtype.val,fun h => h⟩
    have r : R.Reachable x (q i) := hr.elim fun w => (w.map f).reachable
    exact hn (mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,r⟩,rfl⟩)
  have npos : 0<Fintype.card I := by omega
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp npos
  letI : Nonempty Y := ⟨q i⟩
  refine ⟨?_⟩
  intro u v
  by_contra no
  have dd : Disjoint (C u) (C v) := by
    rw [disjoint_left]
    intro j hu hv
    exact no ((mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm)
  have hh := (C u ∪ C v).card_le_univ
  rw [card_union_of_disjoint dd] at hh
  have lu := many u
  have lv := many v
  omega

#print axioms right_connected_of_small_matching_cut

omit [DecidableEq I] in
/-- Perfect matching between two 2-connected rails. The rails may be
any graphs which stay connected after at most one vertex deletion. -/
theorem perfect_rail_glue_three_connected
    {L : SimpleGraph X} {R : SimpleGraph Y} (p : I ≃ X) (q : I ≃ Y)
    (many : 3≤Fintype.card I)
    (lconn : ∀ A : Finset X, A.card≤1 → (L.induce (remains A)).Connected)
    (rconn : ∀ B : Finset Y, B.card≤1 → (R.induce (remains B)).Connected) :
    KelmansStarter.ThreeConnected (glue L R p q) := by
  have szX := Fintype.card_congr p
  have szY := Fintype.card_congr q
  refine ⟨by rw [Fintype.card_sum]; omega,?_⟩
  intro D small
  let A := D.toLeft
  let B := D.toRight
  have eqD : A.disjSum B = D := toLeft_disjSum_toRight
  have bd : A.card+B.card≤2 := le_trans (card_toLeft_add_card_toRight.le) small
  change ((glue L R p q).induce (remains D)).Connected
  rw [← eqD]
  let W := (glue L R p q).induce (remains (A.disjSum B))
  obtain ⟨i,ai,bi⟩ := some_open_link p.injective q.injective many bd
  apply (W.connected_iff_exists_forall_reachable).mpr
  refine ⟨lIn ⟨p i,ai⟩,?_⟩
  have base : W.Reachable (lIn ⟨p i,ai⟩) (rIn ⟨q i,bi⟩) := (cross_adj ai bi).reachable
  intro u
  cases e : u.val with
  | inl x =>
    obtain ⟨hx,rfl⟩ := split_left e
    by_cases hs : A.card≤1
    · exact (lconn _ hs _ _).elim fun w => (w.map lHom).reachable
    · have B0 : B=∅ := card_eq_zero.mp (by omega)
      let j := p.symm x
      have ja : p j∉A := by simpa [j] using hx
      have jb : q j∉B := by rw [B0]; exact not_mem_empty _
      have way : W.Reachable (rIn ⟨q i,bi⟩) (rIn ⟨q j,jb⟩) :=
        (rconn _ (by omega) _ _).elim fun w => (w.map rHom).reachable
      have target : lIn (A:=A) (B:=B) ⟨p j,ja⟩ = lIn ⟨x,hx⟩ := by
        apply Subtype.ext
        change Sum.inl (p j) = Sum.inl x
        simp [j]
      rw [← target]
      exact base.trans (way.trans (cross_adj ja jb).reachable.symm)
  | inr x =>
    obtain ⟨hx,rfl⟩ := split_right e
    by_cases hs : B.card≤1
    · exact base.trans ((rconn _ hs _ _).elim fun w => (w.map rHom).reachable)
    · have A0 : A=∅ := card_eq_zero.mp (by omega)
      let j := q.symm x
      have jb : q j∉B := by simpa [j] using hx
      have ja : p j∉A := by rw [A0]; exact not_mem_empty _
      have way : W.Reachable (lIn ⟨p i,ai⟩) (lIn ⟨p j,ja⟩) :=
        (lconn _ (by omega) _ _).elim fun w => (w.map lHom).reachable
      have target : rIn (A:=A) (B:=B) ⟨q j,jb⟩ = rIn ⟨x,hx⟩ := by
        apply Subtype.ext
        change Sum.inr (q j) = Sum.inr x
        simp [j]
      rw [← target]
      exact way.trans (cross_adj ja jb).reachable

#print axioms perfect_rail_glue_three_connected
end KelmansCactus.FourReplace
