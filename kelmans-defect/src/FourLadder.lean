import CopyMimic
import PaletteBudget

open Finset
namespace KelmansCactus.FourLadder
open ThreePort Substitute

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

private def two (a b : ℕ) : Bool → ℕ := fun x => if x then b else a

private def cols (n a b : ℕ) : Finset (Fin n × Bool) :=
  univ.filter fun x => a ≤ x.1.val ∧ x.1.val < b

private theorem mem_cols {n a b : ℕ} {x : Fin n × Bool} :
    x ∈ cols n a b ↔ a ≤ x.1.val ∧ x.1.val < b := by simp [cols]

private def near (u v : ℕ × Bool) : Prop :=
 (u.1=v.1 ∧ u.2≠v.2) ∨
 (u.2=v.2 ∧ (u.1+1=v.1 ∨ v.1+1=u.1))

def ladder (n : ℕ) : SimpleGraph (Fin n × Bool) where
  Adj u v := near (u.1.val,u.2) (v.1.val,v.2)
  symm := by
    intro u v h
    unfold near at h ⊢
    rcases h with ⟨x,y⟩ | ⟨x,y⟩
    · exact Or.inl ⟨x.symm,Ne.symm y⟩
    · exact Or.inr ⟨x.symm,y.symm⟩
  loopless := by
    intro u h
    rcases h with ⟨_,bad⟩ | ⟨_,bad⟩
    · exact bad rfl
    · omega

private instance pad (n : ℕ) (u v : Fin n × Bool) : Decidable ((ladder n).Adj u v) := by
  unfold ladder near
  infer_instance

private def first : Bool → Fin 3 × Bool := (0, ·)

private def endsize (a b : Fin 3) : ℕ :=
  if (a.val+b.val)%3=2 then 1 else if (a.val+b.val)%3=1 then 2 else 3

private theorem endsize_bounds (a b : Fin 3) : 1≤endsize a b ∧ endsize a b≤3 := by
  unfold endsize
  split <;> try omega
  split <;> omega

private theorem endsize_mod (a b : Fin 3) : (2*endsize a b)%3=(a.val+b.val)%3 := by
  unfold endsize
  split <;> try omega
  split <;> omega

private def frag (a b : Fin 3) (r : Bool) : Finset (Fin 3 × Bool) :=
  if (two a.val b.val r)=0 then ∅ else
  if (two a.val b.val r)=1 then {(0,r)} else
  if (two a.val b.val (!r))=0 then {(0,r),(0,!r)} else
  {(0,r),(1,r)}

private def ntiles (a b : Fin 3) : ℕ := (2*endsize a b-a.val-b.val)/3

set_option maxRecDepth 12000 in
private theorem endcheck :
    ∀ a b : Fin 3,
      (∀ r : Bool, (frag a b r).card = two a.val b.val r) ∧
      (∀ r : Bool, frag a b r ⊆ cols 3 0 (endsize a b)) ∧
      (∀ r : Bool, (frag a b r).Nonempty → first r ∈ frag a b r) ∧
      (∀ r : Bool, ∀ x ∈ frag a b r, x ≠ first r → (ladder 3).Adj (first r) x) ∧
      Disjoint (frag a b false) (frag a b true) ∧
      Kelmans.solve (ladder 3) (ntiles a b)
        (cols 3 0 (endsize a b) \ (frag a b false ∪ frag a b true)) = true := by decide

private theorem small_end (a b : Fin 3) :
    Signature (G:=ladder 3) (cols 3 0 (endsize a b)) first (two a.val b.val) := by
  obtain ⟨size,sub,own,adj,dis,sol⟩ := endcheck a b
  refine ⟨frag a b,fun i => ⟨size i,sub i,own i,adj i⟩,?_,?_⟩
  · intro i j ne
    cases i <;> cases j
    · exact (ne rfl).elim
    · exact dis
    · exact dis.symm
    · exact (ne rfl).elim
  · have eq : univ.biUnion (frag a b) = frag a b false ∪ frag a b true := by
      ext x
      simp only [mem_biUnion,mem_univ,true_and,mem_union]
      constructor
      · rintro ⟨i,hi⟩
        cases i
        · exact Or.inl hi
        · exact Or.inr hi
      · rintro (hf|ht)
        · exact ⟨false,hf⟩
        · exact ⟨true,ht⟩
    rw [eq]
    obtain ⟨P,ht,hd,hc⟩ := Kelmans.partition_of_tiles (ladder 3) ((Kelmans.solve_iff _ _ _).mp sol)
    exact ⟨P,ht,hd,hc⟩

private theorem map_sat {X Y : Type*} [DecidableEq X] [DecidableEq Y] (e : X ↪ Y) {S R : Finset X} :
    (S \ R).map e = S.map e \ R.map e := by
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
    obtain ⟨xs,xr⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨mem_map.mpr ⟨x,xs,rfl⟩,fun h => by
      obtain ⟨z,zr,ez⟩ := mem_map.mp h
      exact xr ((e.injective ez) ▸ zr)⟩
  · intro hy
    obtain ⟨ys,yr⟩ := mem_sdiff.mp hy
    obtain ⟨x,xs,rfl⟩ := mem_map.mp ys
    exact mem_map.mpr ⟨x,mem_sdiff.mpr ⟨xs,fun h => yr (mem_map.mpr ⟨x,h,rfl⟩)⟩,rfl⟩

private theorem map_biun {X Y I : Type*} [DecidableEq X] [DecidableEq Y]
    (e : X ↪ Y) (J : Finset I) (F : I → Finset X) :
    (J.biUnion F).map e = J.biUnion (fun i => (F i).map e) := by
  ext z
  constructor
  · intro zz
    obtain ⟨x,hx,hz⟩ := mem_map.mp zz
    obtain ⟨i,hi,xi⟩ := mem_biUnion.mp hx
    exact mem_biUnion.mpr ⟨i,hi,mem_map.mpr ⟨x,xi,hz⟩⟩
  · intro zz
    obtain ⟨i,hi,hz⟩ := mem_biUnion.mp zz
    obtain ⟨x,xi,ex⟩ := mem_map.mp hz
    exact mem_map.mpr ⟨x,mem_biUnion.mpr ⟨i,hi,xi⟩,ex⟩

theorem signature_map {X I : Type*} [DecidableEq X] [Fintype I]
    {H : SimpleGraph X} {S : Finset X} {p : I → X} {w : I → Nat} (e : X ↪ V)
    (adj : ∀ u ∈ S, ∀ v ∈ S, H.Adj u v → G.Adj (e u) (e v))
    (h : Signature (G:=H) S p w) : Signature (G:=G) (S.map e) (fun i => e (p i)) w := by
  obtain ⟨F,hF,dis,P,hP⟩ := h
  refine ⟨fun i => (F i).map e,?_,fun i j ne => (Finset.disjoint_map e).mpr (dis i j ne),?_⟩
  · intro i
    refine ⟨by simpa using (hF i).1,⟨?_,?_,?_⟩⟩
    · intro u hu
      obtain ⟨v,vf,rfl⟩ := mem_map.mp hu
      exact mem_map.mpr ⟨v,(hF i).2.inside vf,rfl⟩
    · rintro ⟨u,hu⟩
      obtain ⟨v,vf,rfl⟩ := mem_map.mp hu
      exact mem_map.mpr ⟨p i,(hF i).2.includes ⟨v,vf⟩,rfl⟩
    · intro v hv ne
      obtain ⟨u,uf,rfl⟩ := mem_map.mp hv
      exact adj (p i) ((hF i).2.inside ((hF i).2.includes ⟨u,uf⟩))
        u ((hF i).2.inside uf) ((hF i).2.star u uf (fun he => ne (congrArg e he)))
  · have tmp := CopyMimic.local_map e (fun u hu v hv => adj u (mem_sdiff.mp hu).1 v (mem_sdiff.mp hv).1) hP
    rw [map_sat,map_biun] at tmp
    exact ⟨_,tmp⟩

private def band {n : ℕ} (e : (Fin n × Bool) ↪ V) (a b : ℕ) : Finset V :=
  (cols n a b).map e

omit [DecidableEq V] in
private theorem mem_band {n a b : ℕ} {e : (Fin n × Bool) ↪ V} {u : Fin n × Bool} :
    e u ∈ band e a b ↔ a ≤ u.1.val ∧ u.1.val<b := by
  simp [band,mem_cols]

omit [DecidableEq V] in
private theorem band_disjoint {n a b c d : ℕ} (e : (Fin n × Bool) ↪ V)
    (le : b≤c) : Disjoint (band e a b) (band e c d) := by
  rw [disjoint_left]
  intro x x₁ x₂
  obtain ⟨u,hu,rfl⟩ := mem_map.mp x₁
  have v₁ := mem_cols.mp hu
  have v₂ := mem_band.mp x₂
  omega

private theorem band_split {n a b c : ℕ} (e : (Fin n × Bool) ↪ V)
    (h₁ : a≤b) (h₂ : b≤c) : band e a b ∪ band e b c = band e a c := by
  rw [band,band,band,← map_union]
  congr 1
  ext x
  simp only [mem_union,mem_cols]
  omega

omit [DecidableEq V] in
private theorem empty_band {n a : ℕ} (e : (Fin n × Bool) ↪ V) : band e a a = ∅ := by
  apply eq_empty_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨u,hu,_⟩ := mem_map.mp hx
  exact (Nat.not_lt_of_ge (mem_cols.mp hu).1) (mem_cols.mp hu).2

private def core (n : ℕ) (r : Bool) (a : ℕ) (ha : a+3≤n) : Fin 3 ↪ Fin n × Bool where
  toFun i := (⟨a+i.val,by have := i.isLt; omega⟩,r)
  inj' := by intro i j h; apply Fin.ext; have hh := congrArg (fun x : Fin n × Bool => x.1.val) h; dsimp at hh; omega

omit [DecidableEq V] in
private theorem core_tile {n : ℕ} (e : (Fin n × Bool) ↪ V) (r : Bool) (a : ℕ) (ha : a+3≤n)
    (adj : ∀ u v, (ladder n).Adj u v → G.Adj (e u) (e v)) :
    KelmansStarter.IsTile G ((univ : Finset (Fin 3)).map ((core n r a ha).trans e)) := by
  let f := (core n r a ha).trans e
  refine ⟨by simp, f 1,mem_map.mpr ⟨1,mem_univ _,rfl⟩,?_⟩
  intro y hy ne
  obtain ⟨i,_,rfl⟩ := mem_map.mp hy
  apply adj
  change near (a+1,r) (a+i.val,r)
  refine Or.inr ⟨rfl,?_⟩
  have hx : i.val≠1 := by intro eq; exact ne (congrArg f (Fin.ext eq))
  have hi := i.isLt
  omega

private theorem core_cover {n a : ℕ} (ha : a+3≤n) (e : (Fin n × Bool) ↪ V) :
    (univ : Finset (Fin 3)).map ((core n false a ha).trans e) ∪
      (univ : Finset (Fin 3)).map ((core n true a ha).trans e) = band e a (a+3) := by
  ext x
  simp only [mem_union,band,mem_map,mem_univ,true_and,mem_cols]
  constructor
  · rintro (⟨v,rfl⟩|⟨v,rfl⟩) <;> exact ⟨_,⟨by change a≤a+v.val; omega,by change a+v.val<a+3; have := v.isLt; omega⟩,rfl⟩
  · rintro ⟨⟨c,r⟩,⟨lo,hi⟩,rfl⟩
    let j : Fin 3 := ⟨c.val-a,by dsimp at lo hi; omega⟩
    have hj : a+j.val=c.val := by change a≤c.val at lo; change a+(c.val-a)=c.val; omega
    cases r
    · exact Or.inl ⟨j,congrArg e (Prod.ext (Fin.ext hj) rfl)⟩
    · exact Or.inr ⟨j,congrArg e (Prod.ext (Fin.ext hj) rfl)⟩

private theorem block {n : ℕ} (e : (Fin n × Bool) ↪ V) (a : ℕ) (ha : a+3≤n)
    (adj : ∀ u v, (ladder n).Adj u v → G.Adj (e u) (e v)) : Closed G (band e a (a+3)) := by
  rw [← core_cover ha e]
  apply add_closed (tile_closed (core_tile e false a ha adj)) (tile_closed (core_tile e true a ha adj))
  rw [disjoint_left]
  intro v hm hq
  obtain ⟨x,_,hx⟩ := mem_map.mp hm
  obtain ⟨y,_,hy⟩ := mem_map.mp hq
  have zz := congrArg Prod.snd (e.injective (hx.trans hy.symm))
  cases zz

private theorem middle {n : ℕ} (e : (Fin n × Bool) ↪ V) (a k : ℕ) (ha : a+3*k≤n)
    (adj : ∀ u v, (ladder n).Adj u v → G.Adj (e u) (e v)) : Closed G (band e a (a+3*k)) := by
  induction k with
  | zero =>
    rw [Nat.mul_zero,add_zero,empty_band]
    exact ⟨∅,by constructor <;> simp⟩
  | succ k ih =>
    rw [show a+3*(k+1)=a+3*k+3 by omega, ← band_split e (b:=a+3*k) (by omega) (by omega)]
    exact add_closed (ih (by omega)) (block e _ (by omega) adj) (band_disjoint e (by omega))

private def endEmbedding (n : ℕ) (hn : 3≤n) (back : Bool) : (Fin 3 × Bool) ↪ (Fin n × Bool) where
  toFun x := (⟨if back then n-1-x.1.val else x.1.val, by
    have hx := x.1.isLt
    split <;> omega⟩,x.2)
  inj' := by
    intro ⟨i,r⟩ ⟨j,s⟩ he
    have c := congrArg (fun p : Fin n × Bool => p.1.val) he
    have t := congrArg Prod.snd he
    apply Prod.ext
    · apply Fin.ext
      change i.val=j.val
      have hi := i.isLt
      have hj := j.isLt
      change (if back then n-1-i.val else i.val) = (if back then n-1-j.val else j.val) at c
      cases back <;> simp at c <;> omega
    · exact t

private theorem end_edges {n : ℕ} (hn : 3≤n) (back : Bool) {u v : Fin 3 × Bool}
    (h : (ladder 3).Adj u v) :
    (ladder n).Adj (endEmbedding n hn back u) (endEmbedding n hn back v) := by
  have hu := u.1.isLt
  have hv := v.1.isLt
  change near (u.1.val,u.2) (v.1.val,v.2) at h
  dsimp [ladder,near,endEmbedding] at h ⊢
  cases back
  · simpa using h
  · simp only [if_true] 
    rcases h with ⟨eq,ne⟩ | ⟨eq,next⟩
    · exact Or.inl ⟨by omega,ne⟩
    · exact Or.inr ⟨eq,by omega⟩

private theorem end_image {n k : ℕ} (hn : 3≤n) (hk : k≤3) (back : Bool) :
    (cols 3 0 k).map (endEmbedding n hn back) =
      if back then cols n (n-k) n else cols n 0 k := by
  ext z
  rw [mem_map]
  cases z with
  | mk c r =>
    have hc := c.isLt
    cases back
    · simp only [Bool.false_eq_true,if_false,mem_cols,Nat.zero_le,true_and]
      constructor
      · rintro ⟨⟨i,s⟩,hi,eq⟩
        have f := congrArg (fun p : Fin n × Bool => p.1.val) eq
        have ux := hi
        change i.val<k at ux
        change i.val=c.val at f
        show c.val<k
        omega
      · intro h
        change c.val<k at h
        exact ⟨(⟨c.val,by omega⟩,r),h,Prod.ext (Fin.ext rfl) rfl⟩
    · simp only [if_pos rfl,if_true,mem_cols,Nat.zero_le,true_and]
      constructor
      · rintro ⟨⟨i,s⟩,hi,eq⟩
        have f := congrArg (fun p : Fin n × Bool => p.1.val) eq
        have ux := hi
        change i.val<k at ux
        change n-1-i.val=c.val at f
        exact ⟨by omega,hc⟩
      · rintro ⟨lo,_⟩
        change n-k≤c.val at lo
        refine ⟨(⟨n-1-c.val,by omega⟩,r),?_,?_⟩
        · change n-1-c.val<k; omega
        · apply Prod.ext
          · apply Fin.ext; change n-1-(n-1-c.val)=c.val; omega
          · rfl

/-- Four corners of a ladder, ordered by (end,row). -/
def ports {n : ℕ} (hn : 0<n) (e : (Fin n × Bool) ↪ V) (i : Bool × Bool) : V :=
  e (⟨if i.1 then n-1 else 0,by split <;> omega⟩,i.2)

private theorem mapped_end {n : ℕ} (hn : 3≤n) (e : (Fin n × Bool) ↪ V)
    (adj : ∀ u v, (ladder n).Adj u v → G.Adj (e u) (e v)) (a b : Fin 3) (back : Bool) :
    Signature (G:=G)
      (if back then band e (n-endsize a b) n else band e 0 (endsize a b))
      (fun r => ports (by omega) e (back,r)) (two a.val b.val) := by
  let eh := endEmbedding n hn back
  have tmp := signature_map (G:=G) (eh.trans e)
    (fun u _ v _ h => adj _ _ (end_edges hn back h)) (small_end a b)
  have bands : (cols 3 0 (endsize a b)).map (eh.trans e) =
        if back then band e (n-endsize a b) n else band e 0 (endsize a b) := by
    rw [← Finset.map_map]
    have fm : (cols 3 0 (endsize a b)).map eh =
        if back then cols n (n-endsize a b) n else cols n 0 (endsize a b) :=
      end_image hn (endsize_bounds a b).2 _
    rw [fm]
    cases back <;> rfl
  have pp (r : Bool) : (eh.trans e) (first r) = ports (by omega) e (back,r) := by
    cases back <;> rfl
  rw [bands] at tmp
  simpa only [pp] using tmp

set_option maxHeartbeats 2500000 in
private theorem combine {L M R : Finset V} {p : Bool × Bool → V} {w : Bool × Bool → ℕ}
    (ls : Signature (G:=G) L (fun i => p (false,i)) (fun i => w (false,i)))
    (m : Closed G M)
    (rs : Signature (G:=G) R (fun i => p (true,i)) (fun i => w (true,i)))
    (LM : Disjoint L M) (LR : Disjoint L R) (MR : Disjoint M R) :
    Signature (G:=G) (L∪M∪R) p w := by
  obtain ⟨F,f,fd,P,hP⟩ := ls
  obtain ⟨H,h,hd,Q,hQ⟩ := rs
  let U := univ.biUnion F
  let T := univ.biUnion H
  have UL : U ⊆ L := by
    intro v hv
    obtain ⟨a,_,va⟩ := mem_biUnion.mp hv
    exact (f a).2.inside va
  have TR : T ⊆ R := by
    intro v hv
    obtain ⟨a,_,va⟩ := mem_biUnion.mp hv
    exact (h a).2.inside va
  let B (i : Bool × Bool) := if i.1 then H i.2 else F i.2
  have both : univ.biUnion B = U∪T := by
    ext v
    simp only [mem_biUnion,mem_univ,true_and,mem_union,U,T]
    constructor
    · rintro ⟨⟨i,j⟩,vm⟩
      cases i
      · exact Or.inl ⟨j,by simpa [B] using vm⟩
      · exact Or.inr ⟨j,by simpa [B] using vm⟩
    · rintro (⟨i,vi⟩|⟨i,vi⟩)
      · exact ⟨(false,i),by simpa [B] using vi⟩
      · exact ⟨(true,i),by simpa [B] using vi⟩
  have residual : (L∪M∪R) \ (U∪T) = (L\U)∪M∪(R\T) := by
    ext v
    simp only [mem_union,mem_sdiff]
    have a := fun (l : v∈L) (r : v∈R) => disjoint_left.mp LR l r
    have b := fun (l : v∈L) (m : v∈M) => disjoint_left.mp LM l m
    have c := fun (m : v∈M) (r : v∈R) => disjoint_left.mp MR m r
    have xl := fun u : v∈U => UL u
    have xr := fun t : v∈T => TR t
    tauto
  refine ⟨B,?_,?_,?_⟩
  · rintro ⟨i,j⟩
    cases i
    · refine ⟨(f j).1,?_⟩
      exact ⟨(f j).2.inside.trans (subset_union_left.trans subset_union_left),(f j).2.includes,(f j).2.star⟩
    · refine ⟨(h j).1,?_⟩
      exact ⟨(h j).2.inside.trans subset_union_right,(h j).2.includes,(h j).2.star⟩
  · rintro ⟨i,j⟩ ⟨k,l⟩ ne
    cases i <;> cases k
    · exact fd j l (fun e => ne (congrArg (false, ·) e))
    · exact LR.mono (f j).2.inside (h l).2.inside
    · exact LR.symm.mono (h j).2.inside (f l).2.inside
    · exact hd j l (fun e => ne (congrArg (true, ·) e))
  · rw [both,residual]
    exact add_closed (add_closed ⟨P,hP⟩ m (LM.mono_left sdiff_subset))
      ⟨Q,hQ⟩ ((disjoint_union_left.mpr ⟨LR.mono_left sdiff_subset,MR⟩).mono_right sdiff_subset)

omit [DecidableEq V] in
private theorem bands_full {n : ℕ} (e : (Fin n × Bool) ↪ V) : band e 0 n = univ.map e := by
  unfold band
  congr 1
  ext v
  simp [mem_cols,v.1.isLt]

/-- A shore with a spanning ladder of at least six rungs supports every width
vector of the correct residue. At each end consume a short 1–3-rung box;
the intervening rail lengths then divide by three. Extra edges are permitted. -/
theorem full_palette_of_ladder {n : ℕ} (hn : 6≤n) (e : (Fin n × Bool) ↪ V)
    (adj : ∀ u v, (ladder n).Adj u v → G.Adj (e u) (e v))
    (w : Bool × Bool → Fin 3)
    (res : (((w (false,false)).val+(w (false,true)).val)+
          ((w (true,false)).val+(w (true,true)).val))%3=(2*n)%3) :
    Signature (G:=G) (univ.map e) (ports (by omega) e) (fun i => (w i).val) := by
  let a := endsize (w (false,false)) (w (false,true))
  let b := endsize (w (true,false)) (w (true,true))
  have ha := endsize_bounds (w (false,false)) (w (false,true))
  have hb := endsize_bounds (w (true,false)) (w (true,true))
  change 1≤a ∧ a≤3 at ha
  change 1≤b ∧ b≤3 at hb
  have am := endsize_mod (w (false,false)) (w (false,true))
  have bm := endsize_mod (w (true,false)) (w (true,true))
  change 2*a%3=((w (false,false)).val+(w (false,true)).val)%3 at am
  change 2*b%3=((w (true,false)).val+(w (true,true)).val)%3 at bm
  have divis : 3 ∣ n-b-a := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  obtain ⟨k,hk⟩ := divis
  have eqn : n-b=a+3*k := by omega
  have left := mapped_end (G:=G) (by omega) e adj (w (false,false)) (w (false,true)) false
  have right := mapped_end (G:=G) (by omega) e adj (w (true,false)) (w (true,true)) true
  have lw : two (w (false,false)).val (w (false,true)).val = fun i => (w (false,i)).val := by
    funext i; cases i <;> rfl
  have rw' : two (w (true,false)).val (w (true,true)).val = fun i => (w (true,i)).val := by
    funext i; cases i <;> rfl
  rw [lw] at left
  rw [rw'] at right
  have mid : Closed G (band e a (n-b)) := by
    rw [eqn]
    exact middle e a k (by omega) adj
  have h := combine (L:=band e 0 a) (M:=band e a (n-b)) (R:=band e (n-b) n)
    (by simpa only [Bool.false_eq_true,if_false] using left)
    mid (by simpa only [if_pos rfl] using right) (p:=ports (by omega) e) (w:=fun i => (w i).val)
    (band_disjoint e (by omega)) (band_disjoint e (by omega)) (band_disjoint e (by omega))
  rw [band_split e (by omega : 0≤a) (by omega : a≤n-b),band_split e (by omega : 0≤n-b) (by omega : n-b≤n),bands_full] at h
  exact h

#print axioms full_palette_of_ladder
end KelmansCactus.FourLadder
