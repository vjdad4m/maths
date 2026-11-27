import Assemble
import Mathlib.Data.List.TakeDrop

open Finset
namespace KelmansCactus.PathSlides

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

abbrev Parts (V : Type*) := Finset (Finset V)

/-- Exact tile family, with its used vertices contained in an ambient region. -/
structure PackIn (G : SimpleGraph V) (D : Finset V) (P : Parts V) : Prop where
  part : Assemble.LocalPart G P (P.biUnion id)
  inside : P.biUnion id ⊆ D

/-- A neutral move removes one tile, inserts a different tile, and keeps
every other tile exactly. In particular, there is no global rematching. -/
structure Slide (G : SimpleGraph V) (D : Finset V) (P Q : Parts V) : Prop where
  start : PackIn G D P
  stop : PackIn G D Q
  one : ∃ K a b, a∉K ∧ b∉K ∧ a≠b ∧ P=insert a K ∧ Q=insert b K

inductive Slides (G : SimpleGraph V) (D : Finset V) :
    ℕ → Parts V → Parts V → Prop where
  | nil (P) (ok : PackIn G D P) : Slides G D 0 P P
  | cons {n P Q R} : Slide G D P Q → Slides G D n Q R → Slides G D (n+1) P R

theorem Slides.ok_start {D : Finset V} {n P Q} (s : Slides G D n P Q) : PackIn G D P := by
  cases s with
  | nil _ ok => exact ok
  | cons step _ => exact step.start

theorem Slides.ok_stop {D : Finset V} {n P Q} (s : Slides G D n P Q) : PackIn G D Q := by
  induction s with
  | nil _ ok => exact ok
  | cons _ _ ih => exact ih

theorem Slide.same_size {D : Finset V} {P Q} (e : Slide G D P Q) : P.card=Q.card := by
  obtain ⟨K,a,b,ha,hb,_,rfl,rfl⟩ := e.one
  rw [card_insert_of_not_mem ha,card_insert_of_not_mem hb]

theorem Slides.same_size {D : Finset V} {n P Q} (s : Slides G D n P Q) : P.card=Q.card := by
  induction s with
  | nil => rfl
  | cons e _ ih => exact e.same_size.trans ih

theorem Slides.append {D : Finset V} {n m P Q R}
    (a : Slides G D n P Q) (b : Slides G D m Q R) : Slides G D (n+m) P R := by
  induction a with
  | nil => simpa using b
  | @cons n P Q S step _ ih =>
    rw [show n+1+m=(n+m)+1 by omega]
    exact Slides.cons step (ih b)

private theorem PackIn.tile_inside {D : Finset V} {P : Parts V} (p : PackIn G D P)
    {t : Finset V} (ht : t∈P) : t ⊆ D :=
  (p.part.tile_sub G ht).trans p.inside

theorem PackIn.union {D E : Finset V} {P Q : Parts V}
    (p : PackIn G D P) (q : PackIn G E Q) (sep : Disjoint D E) :
    PackIn G (D∪E) (P∪Q) := by
  refine ⟨⟨?_,?_,rfl⟩,?_⟩
  · intro t ht
    exact (mem_union.mp ht).elim (p.part.tile t) (q.part.tile t)
  · intro s hs t ht ne
    rcases mem_union.mp hs with hs | hs <;> rcases mem_union.mp ht with ht | ht
    · exact p.part.disj s hs t ht ne
    · exact sep.mono (p.tile_inside hs) (q.tile_inside ht)
    · exact sep.symm.mono (q.tile_inside hs) (p.tile_inside ht)
    · exact q.part.disj s hs t ht ne
  · intro x hx
    obtain ⟨t,ht,tx⟩ := mem_biUnion.mp hx
    exact (mem_union.mp ht).elim
      (fun hp => mem_union_left _ (p.tile_inside hp tx)) (fun hp => mem_union_right _ (q.tile_inside hp tx))

private theorem only {A : Finset V} (h : KelmansStarter.IsTile G A) : PackIn G A {A} := by
  refine ⟨⟨?_,?_,rfl⟩,?_⟩
  · intro t ht
    simpa only [mem_singleton.mp ht] using h
  · intro t ht u hu ne
    exact (ne ((mem_singleton.mp ht).trans (mem_singleton.mp hu).symm)).elim
  · simp

private theorem separate {D E : Finset V} (sep : Disjoint D E)
    {s : Finset V} (some : s.Nonempty) (sd : s⊆D)
    {Q : Parts V} (q : PackIn G E Q) : s∉Q := by
  intro sm
  obtain ⟨v,vs⟩ := some
  exact disjoint_left.mp sep (sd vs) (q.tile_inside sm vs)

theorem Slide.frame {D E : Finset V} {P Q F : Parts V}
    (e : Slide G D P Q) (f : PackIn G E F) (sep : Disjoint D E) :
    Slide G (D∪E) (P∪F) (Q∪F) := by
  refine ⟨e.start.union f sep,e.stop.union f sep,?_⟩
  obtain ⟨K,a,b,ha,hb,ne,pa,qb⟩ := e.one
  have aa : a∈P := pa.symm ▸ mem_insert_self _ _
  have bb : b∈Q := qb.symm ▸ mem_insert_self _ _
  have an : a.Nonempty := card_pos.mp (by rw [(e.start.part.tile a aa).1]; decide)
  have bn : b.Nonempty := card_pos.mp (by rw [(e.stop.part.tile b bb).1]; decide)
  refine ⟨K∪F,a,b,?_,?_,ne,?_,?_⟩
  · intro hm
    exact (mem_union.mp hm).elim ha (separate sep an (e.start.tile_inside aa) f)
  · intro hm
    exact (mem_union.mp hm).elim hb (separate sep bn (e.stop.tile_inside bb) f)
  · rw [pa,insert_union]
  · rw [qb,insert_union]

theorem Slides.frame {D E : Finset V} {n P Q F}
    (steps : Slides G D n P Q) (f : PackIn G E F) (sep : Disjoint D E) :
    Slides G (D∪E) n (P∪F) (Q∪F) := by
  induction steps with
  | nil p ok => exact Slides.nil _ (ok.union f sep)
  | cons step _ ih => exact Slides.cons (step.frame f sep) ih

theorem Slides.widen {D E : Finset V} {n P Q} (steps : Slides G D n P Q) (sub : D⊆E) :
    Slides G E n P Q := by
  induction steps with
  | nil p ok => exact Slides.nil _ ⟨ok.part,ok.inside.trans sub⟩
  | cons step _ ih =>
    exact Slides.cons ⟨⟨step.start.part,step.start.inside.trans sub⟩,
      ⟨step.stop.part,step.stop.inside.trans sub⟩,step.one⟩ ih


theorem union_cover (P Q : Parts V) : (P∪Q).biUnion id = P.biUnion id ∪ Q.biUnion id := by
  ext v
  constructor
  · intro hv
    obtain ⟨t,hm,tv⟩ := mem_biUnion.mp hv
    exact (mem_union.mp hm).elim (fun p => mem_union_left _ (mem_biUnion.mpr ⟨t,p,tv⟩))
      (fun q => mem_union_right _ (mem_biUnion.mpr ⟨t,q,tv⟩))
  · intro hv
    rcases mem_union.mp hv with p|q
    · obtain ⟨t,ht,tv⟩ := mem_biUnion.mp p
      exact mem_biUnion.mpr ⟨t,mem_union_left _ ht,tv⟩
    · obtain ⟨t,ht,tv⟩ := mem_biUnion.mp q
      exact mem_biUnion.mpr ⟨t,mem_union_right _ ht,tv⟩

theorem single_union (T : Finset V) (P : Parts V) : {T}∪P = insert T P := by
  ext t
  simp

/-- Partition a vertex list into consecutive triples, dropping a short
final suffix if present. Applications below have no dropped suffix. -/
def triples : List V → Parts V
  | a::b::c::t => insert {a,b,c} (triples t)
  | _ => ∅

private theorem local_triple {a b c : V} (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (e₁ : G.Adj a b) (e₂ : G.Adj b c) :
    KelmansStarter.IsTile G ({a,b,c}:Finset V) := by
  refine ⟨by simp [ab,ac,bc],b,by simp,?_⟩
  intro u hu ne
  simp only [mem_insert,mem_singleton] at hu
  rcases hu with rfl|rfl|rfl
  · exact e₁.symm
  · exact (ne rfl).elim
  · exact e₂

private theorem prefix_three_absent {a b c : V} {t : List V}
    (nodup : (a::b::c::t).Nodup) :
    Disjoint ({a,b,c}:Finset V) t.toFinset := by
  have a₀ := (List.nodup_cons.mp nodup).1
  have a₁ := (List.nodup_cons.mp nodup.tail).1
  have a₂ := (List.nodup_cons.mp nodup.tail.tail).1
  apply disjoint_left.mpr
  intro v hv vt
  have x := List.mem_toFinset.mp vt
  simp only [mem_insert,mem_singleton] at hv
  rcases hv with rfl|rfl|rfl
  · exact a₀ (by simp [x])
  · exact a₁ (by simp [x])
  · exact a₂ x

omit [DecidableEq V] in
private theorem distinct_three {a b c : V} {t : List V}
    (nodup : (a::b::c::t).Nodup) : a≠b ∧ a≠c ∧ b≠c := by
  refine ⟨?_,?_,?_⟩ <;> intro h
  · subst a; exact (List.nodup_cons.mp nodup).1 (by simp)
  · subst a; exact (List.nodup_cons.mp nodup).1 (by simp)
  · subst b; exact (List.nodup_cons.mp nodup.tail).1 (by simp)

theorem triples_part (n : ℕ) (l : List V) (length : l.length=3*n)
    (nodup : l.Nodup) (chain : l.Chain' G.Adj) :
    Assemble.LocalPart G (triples l) l.toFinset := by
  induction n generalizing l with
  | zero =>
    have ll : l=[] := List.length_eq_zero_iff.mp (by simpa using length)
    subst l
    exact ⟨by simp [triples],by simp [triples],by simp [triples]⟩
  | succ n ih =>
    match l with
    | [] | [_] | [_,_] => simp at length <;> omega
    | a::b::c::t =>
      have tl : t.length=3*n := by simp at length; omega
      have tb := ih t tl nodup.tail.tail.tail chain.tail.tail.tail
      obtain ⟨ab,ac,bc⟩ := distinct_three nodup
      have tt := local_triple ab ac bc chain.rel_head chain.tail.rel_head
      have old : PackIn G t.toFinset (triples t) := ⟨tb.cover.symm ▸ tb,tb.cover.le⟩
      have h := (only tt).union old (prefix_three_absent nodup)
      have splitU : ({a,b,c} ∪ t.toFinset : Finset V)=(a::b::c::t).toFinset := by
        ext v
        simp [or_assoc]
      have cov : (({({a,b,c}:Finset V)} : Parts V)∪triples t).biUnion id =
          (a::b::c::t).toFinset := by
        rw [union_cover]
        rw [tb.cover]
        have base : (({({a,b,c}:Finset V)} : Parts V).biUnion id) = {a,b,c} := by
          ext v
          simp [mem_biUnion]
        rw [base]
        exact splitU
      have shape : ({({a,b,c}:Finset V)} : Parts V)∪triples t=triples (a::b::c::t) := by
        rw [single_union]
        rfl
      rw [← shape,← cov]
      exact h.part

private theorem triples_in (n : ℕ) (l : List V) (length : l.length=3*n)
    (nodup : l.Nodup) (chain : l.Chain' G.Adj) :
    PackIn G l.toFinset (triples l) := by
  have h := triples_part n l length nodup chain
  exact ⟨h.cover.symm ▸ h,h.cover.le⟩

/-- One-hole sweep from the start of a path: a hole moves by three
positions across each next tile. Precisely n single-tile exchanges
shift the hole from the first vertex to the last. -/
theorem sweep (n : ℕ) (a : V) (tail : List V) (length : tail.length=3*n)
    (nodup : (a::tail).Nodup) (chain : (a::tail).Chain' G.Adj) :
    Slides G (a::tail).toFinset n (triples tail) (triples (a::tail).dropLast) := by
  induction n generalizing a tail with
  | zero =>
    have e : tail=[] := List.length_eq_zero_iff.mp (by simpa using length)
    subst tail
    exact Slides.nil _ ⟨⟨by simp [triples],by simp [triples],rfl⟩,by simp [triples]⟩
  | succ n ih =>
    match tail with
    | [] | [_] | [_,_] => simp at length <;> omega
    | b::c::d::rest =>
      let T : Finset V := {b,c,d}
      let U : Finset V := {a,b,c}
      let D := (a::b::c::d::rest).toFinset
      have len : rest.length=3*n := by simp at length; omega
      have inc : (b::c::d::rest).toFinset ⊆ D := by simp [D]
      have part : PackIn G D (triples (b::c::d::rest)) :=
        let h := triples_in (n+1) _ length nodup.tail chain.tail
        ⟨h.part,h.inside.trans inc⟩
      have after := ih d rest len nodup.tail.tail.tail chain.tail.tail.tail
      have uSep : Disjoint U (d::rest).toFinset := prefix_three_absent nodup
      obtain ⟨ab,ac,bc⟩ := distinct_three nodup
      have ut : KelmansStarter.IsTile G U :=
        local_triple ab ac bc chain.rel_head chain.tail.rel_head
      have ur := (only ut)
      have frame := after.frame ur uSep.symm
      have board : (d::rest).toFinset ∪ U=D := by
        ext x
        simp [D,U,or_assoc,or_comm,or_left_comm]
      rw [board] at frame
      have frame' : Slides G D n (insert U (triples rest))
          (triples (a::b::c::d::rest).dropLast) := by
        rw [union_comm (triples rest),single_union,union_comm (triples (d::rest).dropLast),single_union] at frame
        have tailEnd : (a::b::c::d::rest).dropLast = a::b::c::(d::rest).dropLast := by
          simp only [List.dropLast_cons₂]
        rw [tailEnd,triples]
        exact frame
      have R := triples_in n rest len nodup.tail.tail.tail.tail chain.tail.tail.tail.tail
      have tSep : Disjoint T rest.toFinset := prefix_three_absent nodup.tail
      have uSep' : Disjoint U rest.toFinset := uSep.mono_right (by simp)
      have Us : U.Nonempty := ⟨a,by simp [U]⟩
      have Ts : T.Nonempty := ⟨b,by simp [T]⟩
      have fresh : U≠T := by
        intro he
        have aa : a∈T := he ▸ (show a∈U by simp [U])
        have an := (List.nodup_cons.mp nodup).1
        exact an (by simp [T,or_assoc] at aa ⊢; tauto)
      have step : Slide G D (triples (b::c::d::rest)) (insert U (triples rest)) :=
        ⟨part,frame'.ok_start,⟨triples rest,T,U,separate tSep Ts Subset.rfl R,
          separate uSep' Us Subset.rfl R,fresh.symm,rfl,rfl⟩⟩
      exact Slides.cons step frame'

#print axioms sweep

private theorem erase_last {a : V} (L : List V) : (a::L).dropLast.toFinset ∪
    {(a::L).getLast (by simp)} = (a::L).toFinset := by
  have e := congrArg List.toFinset (List.dropLast_append_getLast (l:=a::L) (by simp))
  simpa using e

private theorem last_absent {a : V} {L : List V} (nodup : (a::L).Nodup) :
    (a::L).getLast (by simp) ∉ (a::L).dropLast.toFinset := by
  intro h
  have n : ((a::L).dropLast ++ [(a::L).getLast (by simp)]).Nodup :=
    (List.dropLast_append_getLast (l:=a::L) (by simp)).symm ▸ nodup
  exact (List.nodup_append.mp n).2.2 (List.mem_toFinset.mp h) (by simp)

set_option maxHeartbeats 1200000 in
/-- Two path-aligned holes can be swept towards a third. The chosen
paths each begin with a hole and are followed by consecutive whole tiles
of the initial packing, in the displayed order. Other tiles stay fixed.
If their last vertices join the central hole, add that P3 at the end. -/
theorem two_sweeps_finish [Fintype V] (n m : ℕ) (a b z : V) (A B : List V)
    (la : A.length=3*n) (lb : B.length=3*m)
    (na : (a::A).Nodup) (nb : (b::B).Nodup)
    (pa : (a::A).Chain' G.Adj) (pb : (b::B).Chain' G.Adj)
    (K : Parts V) (E : Finset V) (rest : Assemble.LocalPart G K E)
    (sepAB : Disjoint (a::A).toFinset (b::B).toFinset)
    (sepAE : Disjoint (a::A).toFinset E) (sepBE : Disjoint (b::B).toFinset E)
    (za : z∉(a::A).toFinset) (zb : z∉(b::B).toFinset) (ze : z∉E)
    (whole : (a::A).toFinset ∪ (b::B).toFinset ∪ E ∪ {z}=univ)
    (ea : G.Adj ((a::A).getLast (by simp)) z) (eb : G.Adj z ((b::B).getLast (by simp))) :
    let P := triples A ∪ triples B ∪ K
    let Q := triples (a::A).dropLast ∪ triples (b::B).dropLast ∪ K
    Slides G univ (n+m) P Q ∧
      Assemble.LocalPart G (insert {((a::A).getLast (by simp)),z,((b::B).getLast (by simp))} Q) univ := by
  dsimp only
  let DA := (a::A).toFinset
  let DB := (b::B).toFinset
  let PA := triples A
  let PB := triples B
  let QA := triples (a::A).dropLast
  let QB := triples (b::B).dropLast
  let aL := (a::A).getLast (by simp)
  let bL := (b::B).getLast (by simp)
  have fr : PackIn G E K := ⟨rest.cover.symm ▸ rest,rest.cover.le⟩
  have sA := sweep n a A la na pa
  have sB := sweep m b B lb nb pb
  have s₁ := (sA.frame (sB.ok_start.union fr sepBE)
    (disjoint_union_right.mpr ⟨sepAB,sepAE⟩)).widen (subset_univ _)
  have s₂ := (sB.frame (sA.ok_stop.union fr sepAE)
    (disjoint_union_right.mpr ⟨sepAB.symm,sepBE⟩)).widen (subset_univ _)
  refine ⟨?_,?_⟩
  · have first : Slides G univ n (PA∪PB∪K) (QA∪PB∪K) := by
      simpa only [union_assoc] using s₁
    have second : Slides G univ m (QA∪PB∪K) (QA∪QB∪K) := by
      have lhs : PB∪(QA∪K)=QA∪PB∪K := by ac_rfl
      have rhs : QB∪(QA∪K)=QA∪QB∪K := by ac_rfl
      change Slides G univ m (PB∪(QA∪K)) (QB∪(QA∪K)) at s₂
      rwa [lhs,rhs] at s₂
    exact first.append second
  · have ca : aL∈DA := by
      exact List.mem_toFinset.mpr (List.getLast_mem (by simp))
    have cb : bL∈DB := by
      exact List.mem_toFinset.mpr (List.getLast_mem (by simp))
    have aN : aL≠z := fun h => za (h ▸ ca)
    have bN : z≠bL := fun h => zb (h.symm ▸ cb)
    have diff : aL≠bL := fun h => disjoint_left.mp sepAB ca (h.symm ▸ cb)
    let T : Finset V := {aL,z,bL}
    have ht : KelmansStarter.IsTile G T := local_triple aN diff bN ea eb
    let D₀ := (a::A).dropLast.toFinset
    let D₁ := (b::B).dropLast.toFinset
    have len0 : (a::A).dropLast.length=3*n := by simpa using la
    have len1 : (b::B).dropLast.length=3*m := by simpa using lb
    have p0 := triples_part n _ len0 (na.sublist (List.dropLast_sublist _)) pa.init
    have p1 := triples_part m _ len1 (nb.sublist (List.dropLast_sublist _)) pb.init
    have asub : D₀⊆DA := by
      intro v hv
      exact List.mem_toFinset.mpr (List.dropLast_subset _ (List.mem_toFinset.mp hv))
    have bsub : D₁⊆DB := by
      intro v hv
      exact List.mem_toFinset.mpr (List.dropLast_subset _ (List.mem_toFinset.mp hv))
    have frame0 : PackIn G D₀ QA := ⟨p0.cover.symm ▸ p0,p0.cover.le⟩
    have frame1 : PackIn G D₁ QB := ⟨p1.cover.symm ▸ p1,p1.cover.le⟩
    have frames := (frame0.union frame1 (sepAB.mono asub bsub)).union fr
      (disjoint_union_left.mpr ⟨sepAE.mono_left asub,sepBE.mono_left bsub⟩)
    have localT : Disjoint T (D₀∪D₁∪E) := by
      apply disjoint_left.mpr
      intro v vT vr
      change v∈({aL,z,bL}:Finset V) at vT
      simp only [mem_insert,mem_singleton] at vT
      rcases vT with rfl|rfl|rfl
      · rcases mem_union.mp vr with vlo | ve
        · rcases mem_union.mp vlo with vd | vd
          · exact last_absent na vd
          · exact disjoint_left.mp sepAB ca (bsub vd)
        · exact disjoint_left.mp sepAE ca ve
      · rcases mem_union.mp vr with vlo | ve
        · rcases mem_union.mp vlo with vd | vd
          · exact za (asub vd)
          · exact zb (bsub vd)
        · exact ze ve
      · rcases mem_union.mp vr with vlo | ve
        · rcases mem_union.mp vlo with vd | vd
          · exact disjoint_left.mp sepAB (asub vd) cb
          · exact last_absent nb vd
        · exact disjoint_left.mp sepBE cb ve
    have out := (only ht).union frames localT
    have onecov : (({T}:Parts V).biUnion id) = T := by
      ext v
      simp [mem_biUnion]
    have cov : (({T}:Parts V)∪(QA∪QB∪K)).biUnion id=univ := by
      rw [union_cover,union_cover,union_cover,onecov]
      rw [show QA.biUnion id=D₀ from p0.cover,show QB.biUnion id=D₁ from p1.cover,rest.cover]
      have aa : D₀∪{aL}=DA := erase_last A
      have bb : D₁∪{bL}=DB := erase_last B
      have tt : T={aL}∪{bL}∪{z} := by
        ext v
        simp only [T,mem_union,mem_insert,mem_singleton]
        tauto
      rw [tt]
      calc
        _ = (D₀∪{aL})∪(D₁∪{bL})∪E∪{z} := by ac_rfl
        _ = univ := by rw [aa,bb]; exact whole
    have final : Assemble.LocalPart G (({T}:Parts V)∪(QA∪QB∪K)) univ :=
      cov ▸ out.part
    rw [single_union] at final
    exact final

#print axioms two_sweeps_finish

/-- A version using an existing near-perfect packing as input. It is
enough to exhibit the two disjoint consecutive runs among its tiles;
the remaining tiles and their support are recovered automatically. -/
theorem repair_two_runs [Fintype V] (n m : ℕ) (a b z : V) (A B : List V)
    (la : A.length=3*n) (lb : B.length=3*m)
    (na : (a::A).Nodup) (nb : (b::B).Nodup)
    (pa : (a::A).Chain' G.Adj) (pb : (b::B).Chain' G.Adj)
    {P : Parts V} (old : Assemble.LocalPart G P (univ\{a,b,z}))
    (aP : triples A⊆P) (bP : triples B⊆P)
    (sep : Disjoint (a::A).toFinset (b::B).toFinset)
    (za : z∉(a::A).toFinset) (zb : z∉(b::B).toFinset)
    (ea : G.Adj ((a::A).getLast (by simp)) z) (eb : G.Adj z ((b::B).getLast (by simp))) :
    ∃ P' Q, Slides G univ (n+m) P P' ∧
      Q=insert {((a::A).getLast (by simp)),z,((b::B).getLast (by simp))} P' ∧
      Assemble.LocalPart G Q univ := by
  let DA := (a::A).toFinset
  let DB := (b::B).toFinset
  let T := triples A∪triples B
  let K := P\T
  let E := univ\(DA∪DB∪{z})
  have sub : T⊆P := union_subset aP bP
  have unify : triples A∪triples B∪K=P := by
    ext t
    have f := fun hm : t∈T => sub hm
    change t∈T∪(P\T) ↔ t∈P
    simp only [mem_union,mem_sdiff]
    tauto
  have fa := triples_part n A la na.tail pa.tail
  have fb := triples_part m B lb nb.tail pb.tail
  have insideA : A.toFinset⊆DA := by simp [DA]
  have insideB : B.toFinset⊆DB := by simp [DB]
  have kP : K⊆P := sdiff_subset
  have zE : z∉E := by simp [E]
  have rest : Assemble.LocalPart G K E := by
    refine ⟨fun t ht => old.tile t (kP ht),fun s hs t ht ne => old.disj s (kP hs) t (kP ht) ne,?_⟩
    ext v
    constructor
    · intro hm
      obtain ⟨t,ht,tv⟩ := mem_biUnion.mp hm
      have vc := old.tile_sub G (kP ht) tv
      have notH := (mem_sdiff.mp vc).2
      apply mem_sdiff.mpr
      refine ⟨mem_univ _,?_⟩
      intro vs
      rcases mem_union.mp vs with vs|sz
      · rcases mem_union.mp vs with vv|vv
        · have vv' : v∈A.toFinset := by
            have h : v∈DA := vv
            simp only [DA,List.toFinset_cons,mem_insert] at h
            exact h.resolve_left (fun h => notH (h.symm ▸ mem_insert_self _ _))
          obtain ⟨u,up,uv⟩ := mem_biUnion.mp (fa.cover.symm ▸ vv')
          have ne : t≠u := fun e => (mem_sdiff.mp ht).2 (e.symm ▸ mem_union_left _ up)
          exact disjoint_left.mp (old.disj t (kP ht) u (aP up) ne) tv uv
        · have vv' : v∈B.toFinset := by
            have h : v∈DB := vv
            simp only [DB,List.toFinset_cons,mem_insert] at h
            exact h.resolve_left (fun h => notH (h.symm ▸ (by simp : b∈({a,b,z}:Finset V))))
          obtain ⟨u,up,uv⟩ := mem_biUnion.mp (fb.cover.symm ▸ vv')
          have ne : t≠u := fun e => (mem_sdiff.mp ht).2 (e.symm ▸ mem_union_right _ up)
          exact disjoint_left.mp (old.disj t (kP ht) u (bP up) ne) tv uv
      · exact notH (mem_insert_of_mem (mem_insert_of_mem sz))
    · intro hm
      have nv := (mem_sdiff.mp hm).2
      have aa : a∈DA := by simp [DA]
      have bb : b∈DB := by simp [DB]
      have notH : v∉({a,b,z}:Finset V) := by
        intro h
        simp only [mem_insert,mem_singleton] at h
        rcases h with rfl|rfl|rfl
        · exact nv (mem_union_left _ (mem_union_left _ aa))
        · exact nv (mem_union_left _ (mem_union_right _ bb))
        · exact nv (mem_union_right _ (mem_singleton_self _))
      obtain ⟨t,ht,tv⟩ := mem_biUnion.mp (old.cover.symm ▸ mem_sdiff.mpr ⟨mem_univ _,notH⟩)
      have nt : t∉T := by
        intro r
        rcases mem_union.mp r with ta|tb
        · exact nv (mem_union_left _ (mem_union_left _ (insideA (fa.tile_sub G ta tv))))
        · exact nv (mem_union_left _ (mem_union_right _ (insideB (fb.tile_sub G tb tv))))
      exact mem_biUnion.mpr ⟨t,mem_sdiff.mpr ⟨ht,nt⟩,tv⟩
  have cae : Disjoint DA E := disjoint_left.mpr fun v va ve =>
    (mem_sdiff.mp ve).2 (mem_union_left _ (mem_union_left _ va))
  have cbe : Disjoint DB E := disjoint_left.mpr fun v vb ve =>
    (mem_sdiff.mp ve).2 (mem_union_left _ (mem_union_right _ vb))
  have cover : DA∪DB∪E∪{z}=univ := by
    apply eq_univ_of_forall
    intro v
    by_cases hf : v∈DA∪DB∪{z}
    · rcases mem_union.mp hf with h|h
      · exact mem_union_left _ (mem_union_left _ h)
      · exact mem_union_right _ h
    · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _,hf⟩))
  have h := two_sweeps_finish n m a b z A B la lb na nb pa pb K E rest sep cae cbe za zb zE cover ea eb
  dsimp only at h
  rw [unify] at h
  exact ⟨_,_,h.1,rfl,h.2⟩

#print axioms repair_two_runs

theorem Slide.removes_at_most_one {D : Finset V} {P Q} (e : Slide G D P Q) :
    (P\Q).card≤1 := by
  obtain ⟨K,a,b,_,_,_,rfl,rfl⟩ := e.one
  have sub : insert a K \ insert b K ⊆ {a} := by
    intro t ht
    obtain ⟨inP,nQ⟩ := mem_sdiff.mp ht
    rcases mem_insert.mp inP with rfl|h
    · simp
    · exact (nQ (mem_insert_of_mem h)).elim
  simpa using card_le_card sub

theorem Slides.removes_at_most_steps {D : Finset V} {n P Q}
    (e : Slides G D n P Q) : (P\Q).card≤n := by
  induction e with
  | nil => simp
  | @cons n P Q R step _ ih =>
    have sub : P\R ⊆ (P\Q)∪(Q\R) := by
      intro t ht
      obtain ⟨p,nr⟩ := mem_sdiff.mp ht
      by_cases q : t∈Q
      · exact mem_union_right _ (mem_sdiff.mpr ⟨q,nr⟩)
      · exact mem_union_left _ (mem_sdiff.mpr ⟨p,q⟩)
    have h := (card_le_card sub).trans (card_union_le _ _)
    have first := step.removes_at_most_one
    omega

#print axioms Slides.removes_at_most_steps
end KelmansCactus.PathSlides
