import ThetaErasedEarStitch
import ThetaAdjacentEarCap
import TwinObstruction
import FiveCapCut

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.ThetaErasedEarCap
open SquareCap (SmallTrivial FactorOn omitEdge three_connected_of_small_trivial)
open PentagonProfile (Port)
open PentagonCap (attach attach_degree_outside SmallFourTrivial pathCap path3 pathRoot path_cap_cubic)
open ThetaAdjacentEarRefill (Shape In Out)
open ThetaAdjacentEarStitch (factor_of_two_leaves)
open ThetaAdjacentEarCap (released place)
open ThetaFiveModes (Lane mid leaf)
open ThetaAdjacentEarLeafModes (WeakLayout)
open ThetaDeadLeafProfiles (MidLayout)
open ThetaErasedEarRefill (midSite firstSite lastSite refill_shared)
noncomputable section
universe u

variable {V : Type u}

def erased (B : SimpleGraph V) (K : SimpleGraph (Fin 9)) (q : Port↪V) :=
  omitEdge (released B K q) (In 7) (In 8)

theorem erased_shape (B : SimpleGraph V) (K : SimpleGraph (Fin 9)) (q : Port↪V)
    (ring : K.Adj 0 1 ∧ K.Adj 1 2 ∧ K.Adj 2 3 ∧ K.Adj 3 4 ∧ K.Adj 4 5 ∧ K.Adj 5 0)
    (a : K.Adj 2 7) (b : K.Adj 5 8) : Shape (erased B K q) := by
  have keep (u v : Fin 9) (edge : K.Adj u v)
      (different : ¬((u=7∧v=8)∨(u=8∧v=7))) :
      (erased B K q).Adj (In u) (In v) := by
    refine ⟨edge,?_⟩
    simpa using different
  exact ⟨keep _ _ ring.1 (by decide),keep _ _ ring.2.1 (by decide),
    keep _ _ ring.2.2.1 (by decide),keep _ _ ring.2.2.2.1 (by decide),
    keep _ _ ring.2.2.2.2.1 (by decide),keep _ _ ring.2.2.2.2.2 (by decide),
    keep _ _ a (by decide),keep _ _ b (by decide)⟩

private def laneRole (s i : Bool) : Port := if s then if i then 4 else 1 else if i then 3 else 2
private def lane (p : Port↪V) : Lane↪V :=
  ⟨fun z=>p (laneRole z.1 z.2),fun a b h=>
    (by decide : ∀ a b : Lane,laneRole a.1 a.2=laneRole b.1 b.2 → a=b) _ _ (p.injective h)⟩

private theorem left_ends : ∀ i : Port,pathRoot i=0 ↔ i=2∨i=3 := by decide
private theorem only_mid : ∀ i : Port,pathRoot i=1 ↔ i=0 := by decide
private theorem right_ends : ∀ i : Port,pathRoot i=2 ↔ i=1∨i=4 := by decide
private theorem in_leaf : ∀ s : Bool,∀ x : Fin 3,path3.Adj (if s then 2 else 0) x→x=1 := by decide
private theorem in_mid : ∀ x : Fin 3,path3.Adj 1 x→x=0∨x=2 := by decide

private theorem layout {B : SimpleGraph V} (p : Port↪V) {J : SimpleGraph (V⊕Fin 3)}
    (sub : J≤pathCap B p) : WeakLayout J (lane p) := by
  constructor
  intro s a ed
  have h := sub ed
  cases a with
  | inr x =>
    have t : path3.Adj (if s then 2 else 0) x := h
    exact Or.inl (congrArg Sum.inr (in_leaf s x t))
  | inl v =>
    obtain ⟨i,e,g⟩ : ∃ i,p i=v ∧ pathRoot i=(if s then 2 else 0) := h
    right
    cases s
    · rcases (left_ends i).mp g with rfl|rfl
      · exact Or.inl (congrArg Sum.inl e.symm)
      · exact Or.inr (congrArg Sum.inl e.symm)
    · rcases (right_ends i).mp g with rfl|rfl
      · exact Or.inl (congrArg Sum.inl e.symm)
      · exact Or.inr (congrArg Sum.inl e.symm)

private theorem midpoint {B : SimpleGraph V} (p : Port↪V) {J : SimpleGraph (V⊕Fin 3)}
    (sub : J≤pathCap B p) : MidLayout J (p 0) := by
  intro a edge
  have h := sub edge
  cases a with
  | inr x =>
    have ed : path3.Adj 1 x := h
    rcases in_mid _ ed with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  | inl v =>
    obtain ⟨i,e,g⟩ : ∃ i,p i=v ∧ pathRoot i=1 := h
    have eq := (only_mid i).mp g
    subst i
    exact Or.inr (Or.inr (congrArg Sum.inl e.symm))

private theorem wire (B : SimpleGraph V) (K : SimpleGraph (Fin 9)) (q : Port↪V)
    (i : Port) (r : Fin 9) (h : place i=r) :
    (erased B K q).Adj (In r) (Out (q i)) := by
  exact ⟨⟨i,rfl,h⟩,by simp⟩

private theorem old_wire {B : SimpleGraph V} (K : SimpleGraph (Fin 9))
    (q p : Port↪V) (a b : V⊕Fin 3) (x y : V)
    (e : (omitEdge (pathCap B p) a b).Adj (.inl x) (.inl y)) :
    (erased B K q).Adj (Out x) (Out y) := ⟨e.1,by simp⟩

variable [Fintype V] [DecidableEq V]

private theorem degree_same {W : Type*} [Fintype W] {A B : SimpleGraph W}
    [DecidableRel A.Adj] [DecidableRel B.Adj] (eq : A=B) (x : W) :
    A.degree x = B.degree x := by
  subst B
  let f (F : Fintype ↑(A.neighborSet x)) := @SimpleGraph.degree W A x F
  exact congrArg f (Subsingleton.elim _ _)

private theorem smaller_factor
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    {B : SimpleGraph V} [DecidableRel B.Adj] {K : SimpleGraph (Fin 9)}
    {q : Port↪V} [DecidableRel (released B K q).Adj]
    (cub : ∀ v,(released B K q).degree v=3)
    (small : SmallTrivial (released B K q)) (small4 : SmallFourTrivial (released B K q))
    (order : Fintype.card (V⊕Fin 9)%6=4)
    (r : Equiv.Perm Port)
    (safe14 : ¬B.Adj (q (r 1)) (q (r 4))) (safe23 : ¬B.Adj (q (r 2)) (q (r 3)))
    (root a b : V⊕Fin 3) (edge : (pathCap B (r.toEmbedding.trans q)).Adj a b) :
    FactorOn (omitEdge (pathCap B (r.toEmbedding.trans q)) a b) (univ.erase root) := by
  let p := r.toEmbedding.trans q
  let A := attach B K p (place ∘ r)
  have eq : A=released B K q := EarCase.reindex_attachment q place r
  letI : DecidableRel A.Adj := fun x y=>by rw [eq]; infer_instance
  have ww (v) : A.degree v=3 := (degree_same eq v).trans (cub _)
  have s3 : SmallTrivial A := eq.symm ▸ small
  have s4 : SmallFourTrivial A := eq.symm ▸ small4
  let C := pathCap B p
  classical
  let three : Fin 3↪Fin 9 :=
    ⟨fun i=>⟨i.val,by have h:=i.isLt; omega⟩,
      fun _ _ z=>Fin.ext (congrArg (fun w : Fin 9=>w.val) z)⟩
  have cs : SmallTrivial C := FiveCapCut.five_cap_of_nonadjacent_pairs three s3 s4 ww safe14 safe23
  have cd : ∀ v,C.degree v=3 :=
    path_cap_cubic (G:=B) (P:=K) (p:=p) (r:=place ∘ r) (fun v=>ww (.inl v))
  have big : 5≤Fintype.card V := by simpa using (Fintype.card_le_of_injective q q.injective)
  have c3 : Fintype.card (V⊕Fin 3)=Fintype.card V+3 := by simp
  have c9 : Fintype.card (V⊕Fin 9)=Fintype.card V+9 := by simp
  apply smaller (V⊕Fin 3) C (by omega) cd
    (three_connected_of_small_trivial C cd (by omega) cs) cs (by omega) root a b edge

private def zeroIndex (i : Port) : Port :=
  if i=0 then 3 else if i=1 then 2 else if i=2 then 0 else if i=3 then 4 else 1

private def zeroPerm : Equiv.Perm Port := Equiv.ofBijective zeroIndex ⟨(by decide : ∀ a b,zeroIndex a=zeroIndex b→a=b),
    (by decide : ∀ b,∃ a,zeroIndex a=b)⟩

private theorem z_wire : ∀ s i : Bool,
    place (zeroPerm (laneRole s i)) =
    (if i then ThetaAdjacentEarRefill.nextSite s else ThetaAdjacentEarRefill.firstSite s) := by decide

theorem zero_extra
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    {B : SimpleGraph V} [DecidableRel B.Adj] {K : SimpleGraph (Fin 9)}
    {q : Port↪V} [DecidableRel (released B K q).Adj]
    (cub : ∀ v,(released B K q).degree v=3)
    (small : SmallTrivial (released B K q)) (small4 : SmallFourTrivial (released B K q))
    (order : Fintype.card (V⊕Fin 9)%6=4)
    (safe04 : ¬B.Adj (q 0) (q 4)) (safe21 : ¬B.Adj (q 2) (q 1))
    (sh : Shape (erased B K q)) :
    FactorOn (erased B K q) (univ.erase (Sum.inr 6)) := by
  let p := zeroPerm.toEmbedding.trans q
  let J := omitEdge (pathCap B p) mid (leaf false)
  have f : FactorOn J (univ.erase mid) :=
    smaller_factor smaller cub small small4 order zeroPerm safe21 safe04 mid mid (leaf false)
      (show path3.Adj 1 0 from by decide)
  have sub : J≤pathCap B p := fun _ _ e=>e.1
  apply factor_of_two_leaves (layout p sub) sh
    (old_wire K q p mid (leaf false)) _ f
  intro s i _
  exact wire B K q _ _ (z_wire s i)

abbrev Routing := Fin 4

def basicRoute (r : Routing) : Fin 3 := if r=1 then 1 else if r=2 then 2 else 0

def index (r : Routing) (i : Port) : Port :=
  if r=0 then
    if i=0 then 0 else if i=1 then 3 else if i=2 then 2 else if i=3 then 1 else 4
  else if r=1 then
    if i=0 then 4 else if i=1 then 3 else if i=2 then 2 else if i=3 then 1 else 0
  else if r=2 then
    if i=0 then 4 else if i=1 then 3 else if i=2 then 0 else if i=3 then 2 else 1
  else
    if i=0 then 0 else if i=1 then 4 else if i=2 then 2 else if i=3 then 3 else 1

def perm (r : Routing) : Equiv.Perm Port :=
  Equiv.ofBijective (index r) ⟨(by decide : ∀ r,∀ a b,index r a=index r b→a=b) r,
    (by decide : ∀ r,∀ b,∃ a,index r a=b) r⟩

private theorem m_wire : ∀ r : Routing,place (perm r 0)=midSite (basicRoute r) := by decide
private theorem f_wire : ∀ r : Routing,place (perm r 2)=firstSite (basicRoute r) := by decide
private theorem l_wire : ∀ r : Routing,r≠3 → place (perm r 3)=lastSite (basicRoute r) := by decide

private def blocker (r : Routing) (p : Port↪V) : V⊕Fin 3 :=
  if r=3 then .inl (p 3) else mid

omit [Fintype V] [DecidableEq V] in
private theorem blocker_real (B : SimpleGraph V) (r : Routing) (p : Port↪V) :
    (pathCap B p).Adj (leaf false) (blocker r p) := by
  by_cases he : r=3
  · rw [blocker,if_pos he]
    exact ⟨3,rfl,by decide⟩
  · rw [blocker,if_neg he]
    exact (show path3.Adj 0 1 from by decide)

/-- Each selected cap erases the actual absorbed edge. The new F2
omission is an internal cap edge, or the now-dead original root wire. -/
theorem routed
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    {B : SimpleGraph V} [DecidableRel B.Adj] {K : SimpleGraph (Fin 9)}
    {q : Port↪V} [DecidableRel (released B K q).Adj]
    (cub : ∀ v,(released B K q).degree v=3)
    (small : SmallTrivial (released B K q)) (small4 : SmallFourTrivial (released B K q))
    (order : Fintype.card (V⊕Fin 9)%6=4)
    (r : Routing)
    (sa : ¬B.Adj (q (perm r 1)) (q (perm r 4)))
    (sb : ¬B.Adj (q (perm r 2)) (q (perm r 3)))
    (sh : Shape (erased B K q)) :
    FactorOn (erased B K q) (univ.erase (Sum.inr 6)) := by
  let p := (perm r).toEmbedding.trans q
  let J := omitEdge (pathCap B p) (leaf false) (blocker r p)
  have sub : J≤pathCap B p := fun _ _ h=>h.1
  have f : FactorOn J (univ.erase (leaf true)) :=
    smaller_factor smaller cub small small4 order (perm r) sa sb (leaf true)
      (leaf false) (blocker r p) (blocker_real B r p)
  have nd (i : Bool) : p 0≠lane p (false,i) := by
    intro h
    have test : ∀ i : Bool,(0:Port)≠laneRole false i := by decide
    exact test i (p.injective h)
  have wm : J.Adj mid (.inl (p 0)) →
      (erased B K q).Adj (In (midSite (basicRoute r))) (Out (p 0)) :=
    fun _=>wire B K q _ _ (m_wire r)
  have wl (i : Bool) : J.Adj (leaf false) (.inl (lane p (false,i))) →
      (erased B K q).Adj (In (if i then lastSite (basicRoute r) else firstSite (basicRoute r)))
        (Out (lane p (false,i))) := by
    intro e
    cases i
    · exact wire B K q _ _ (f_wire r)
    · by_cases he : r=3
      · have i : blocker r p = Sum.inl (lane p (false,true)) := by simp [blocker,he,lane,laneRole]
        exact (e.2 (Or.inl ⟨rfl,i.symm⟩)).elim
      · exact wire B K q _ _ (l_wire r he)
  refine ThetaErasedEarStitch.factor_of_dead_leaf (layout p sub) (midpoint p sub) nd sh
    (basicRoute r) (old_wire K q p (leaf false) (blocker r p)) wm wl ?_ f
  intro A T ma ml md v mode
  by_cases he : r=3
  · rcases mode with ⟨rfl,w⟩|⟨i,rfl,w⟩
    · exact refill_shared sh false _ (by simpa [he,basicRoute,midSite] using wm w)
    · cases i
      · exact refill_shared sh true _ (by simpa [he,basicRoute,firstSite] using wl false w)
      · have e : blocker r p = Sum.inl (lane p (false,true)) := by
          simp [blocker,he,lane,laneRole]
        exact (w.2 (Or.inl ⟨rfl,e.symm⟩)).elim
  · have stop : ¬J.Adj mid (leaf false) := by
      intro k
      have e : blocker r p=mid := by simp [blocker,he]
      exact k.2 (Or.inr ⟨e.symm,rfl⟩)
    exact (ThetaErasedEarStitch.split_by_blocked_internal_edge
      (layout p sub) (midpoint p sub) nd stop T ma ml md).elim

/-- The second nominal extra edge exists before erasing the original
ear; the first may be absent. Neither is needed in the refill itself. -/
theorem second_extra
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    {B : SimpleGraph V} [DecidableRel B.Adj] {K : SimpleGraph (Fin 9)}
    {q : Port↪V} [DecidableRel (released B K q).Adj]
    (cub : ∀ v,(released B K q).degree v=3)
    (small : SmallTrivial (released B K q)) (small4 : SmallFourTrivial (released B K q))
    (order : Fintype.card (V⊕Fin 9)%6=4)
    (real21 : B.Adj (q 2) (q 1)) (safe41 : ¬B.Adj (q 4) (q 1))
    (sh : Shape (erased B K q)) :
    FactorOn (erased B K q) (univ.erase (Sum.inr 6)) := by
  by_cases n : B.Adj (q 3) (q 2)
  · have no : ¬B.Adj (q 3) (q 1) := by
      intro yes
      have large : 5≤Fintype.card (V⊕Fin 9) := by simp
      exact TwinObstruction.no_triangle small large
        (a:=Out (q 3)) (b:=Out (q 2)) (c:=Out (q 1))
        n real21 yes.symm (le_of_eq (cub _)) (le_of_eq (cub _)) (le_of_eq (cub _))
    have degree : B.degree (q 2)=2 := by
      have eq : (univ : Finset Port).filter (fun j=>q j=q 2)={2} := by
        ext j; simp [q.injective.eq_iff]
      letI : DecidableRel (attach B K q place).Adj := ‹DecidableRel (released B K q).Adj›
      have h := cub (Out (q 2))
      change (attach B K q place).degree (Sum.inl (q 2))=3 at h
      rw [attach_degree_outside,eq,card_singleton] at h
      omega
    have no02 : ¬B.Adj (q 0) (q 2) := by
      intro yes
      have neq03 : q 0≠q 3 := fun h=>(by decide : (0:Port)≠3) (q.injective h)
      have neq01 : q 0≠q 1 := fun h=>(by decide : (0:Port)≠1) (q.injective h)
      have neq13 : q 1≠q 3 := fun h=>(by decide : (1:Port)≠3) (q.injective h)
      have sub : ({q 0,q 1,q 3} : Finset V)⊆B.neighborFinset (q 2) := by
        intro v hv
        simp only [mem_insert,mem_singleton] at hv
        rcases hv with rfl|rfl|rfl
        · exact (mem_neighborFinset _ _ _).mpr yes.symm
        · exact (mem_neighborFinset _ _ _).mpr real21
        · exact (mem_neighborFinset _ _ _).mpr n.symm
      have h := card_le_card sub
      have size : ({q 0,q 1,q 3}:Finset V).card=3 := by
        simp [card_insert_of_not_mem,neq01,neq03,neq13]
      rw [size,card_neighborFinset_eq_degree,degree] at h
      omega
    exact routed smaller cub small small4 order 2 no no02 sh
  · exact routed smaller cub small small4 order 3 safe41 (fun e=>n e.symm) sh

/-- When the first nominal extra edge exists and the second does not,
at least one of the two remaining cap pairs is safe by triangle-freeness. -/
theorem first_extra
    (smaller : EarCase.CyclicF2Below.{u} (Fintype.card (V⊕Fin 9)))
    {B : SimpleGraph V} [DecidableRel B.Adj] {K : SimpleGraph (Fin 9)}
    {q : Port↪V} [DecidableRel (released B K q).Adj]
    (cub : ∀ v,(released B K q).degree v=3)
    (small : SmallTrivial (released B K q)) (small4 : SmallFourTrivial (released B K q))
    (order : Fintype.card (V⊕Fin 9)%6=4)
    (real04 : B.Adj (q 0) (q 4)) (safe21 : ¬B.Adj (q 2) (q 1))
    (sh : Shape (erased B K q)) :
    FactorOn (erased B K q) (univ.erase (Sum.inr 6)) := by
  by_cases n : B.Adj (q 3) (q 4)
  · have no : ¬B.Adj (q 3) (q 0) := by
      intro yes
      have large : 5≤Fintype.card (V⊕Fin 9) := by simp
      exact TwinObstruction.no_triangle small large
        (a:=Out (q 0)) (b:=Out (q 4)) (c:=Out (q 3))
        real04 n.symm yes (le_of_eq (cub _)) (le_of_eq (cub _)) (le_of_eq (cub _))
    exact routed smaller cub small small4 order 1 no safe21 sh
  · exact routed smaller cub small small4 order 0 n safe21 sh

#print axioms zero_extra
#print axioms routed
#print axioms first_extra
#print axioms second_extra
end
end KelmansCactus.AtomicBridge.ThetaErasedEarCap
