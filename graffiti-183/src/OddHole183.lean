import MaxBlock183

namespace Graffiti183.Exceptional
open Finset SimpleGraph Short177 Graffiti179
set_option maxHeartbeats 3000000
variable {V : Type*} (G : SimpleGraph V)

private def cutIndex {m : ℕ} (f : Fin m ↪ V) (lo len : ℕ) (h : lo+len ≤ m) :
    Fin len ↪ V where
  toFun i := f ⟨lo+i.val,by have := i.isLt; omega⟩
  inj' := fun i j e => Fin.ext (by
    have hh := congrArg Fin.val (f.injective e)
    change lo+i.val=lo+j.val at hh
    omega)

private theorem in_cutIndex {m : ℕ} (f : Fin m ↪ V) (lo len : ℕ) (h : lo+len ≤ m)
    (i : Fin m) :
    f i ∈ indexSet (cutIndex f lo len h) ↔ lo ≤ i.val ∧ i.val < lo+len := by
  rw [mem_indexSet]
  constructor
  · rintro ⟨j,e⟩
    have q := congrArg Fin.val (f.injective e)
    change lo+j.val=i.val at q
    have := j.isLt
    omega
  · rintro ⟨a,b⟩
    refine ⟨⟨i.val-lo,by omega⟩, f.injective.eq_iff.mpr ?_⟩
    apply Fin.ext
    change lo+(i.val-lo)=i.val
    omega

private theorem cut_con {m : ℕ} (f : Fin m ↪ V)
    (step : ∀ i j, i.val+1=j.val → G.Adj (f i) (f j))
    (lo len : ℕ) (h : lo+len ≤ m) (pos : 0<len) :
    Graffiti177.Con G (indexSet (cutIndex f lo len h)) := by
  apply connected_indexSet pos
  intro i j he
  apply step
  change lo+i.val+1=lo+j.val
  omega

private theorem rotate_once {m : ℕ} (hm : 0<m) (f : Fin m ↪ V)
    (h : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j) :
    ∃ p : Fin m ↪ V, indexSet p = indexSet f ∧
      (∀ i, (eq : i.val+1<m) → p i = f ⟨i.val+1,eq⟩) ∧
      ∀ i j, G.Adj (p i) (p j) ↔ CycleAdj i j := by
  let s (i : Fin m) : Fin m := if hi : i.val+1<m then ⟨i.val+1,hi⟩ else ⟨0,hm⟩
  have val_s (i : Fin m) : (s i).val = if i.val+1<m then i.val+1 else 0 := by
    unfold s
    split <;> simp_all
  have inj : Function.Injective s := by
    intro i j e
    have eq := congrArg Fin.val e
    rw [val_s,val_s] at eq
    apply Fin.ext
    have := i.isLt
    have := j.isLt
    split at eq <;> split at eq <;> omega
  let p : Fin m ↪ V := ⟨f ∘ s,f.injective.comp inj⟩
  refine ⟨p,?_,?_,?_⟩
  · ext x
    simp only [mem_indexSet]
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨s i,rfl⟩
    · rintro ⟨i,rfl⟩
      obtain ⟨j,hj⟩ := (Finite.injective_iff_surjective.mp inj) i
      exact ⟨j,congrArg f hj⟩
  · intro i hi
    simp [p,s,hi]
  · intro i j
    change G.Adj (f (s i)) (f (s j)) ↔ _
    rw [h]
    unfold CycleAdj
    rw [val_s,val_s]
    have := i.isLt
    have := j.isLt
    split <;> split <;> omega

/-- Rotate an indexed cycle until the first vertex differs from two prescribed vertices. -/
private theorem rotate_away {m : ℕ} (hm : 6≤m) (f : Fin m ↪ V)
    (h : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j) (v w : V) :
    ∃ p : Fin m ↪ V, indexSet p = indexSet f ∧
      (p ⟨0,by omega⟩ ≠ v ∧ p ⟨0,by omega⟩ ≠ w) ∧
      ∀ i j, G.Adj (p i) (p j) ↔ CycleAdj i j := by
  classical
  let i (k : ℕ) (hk : k<3) : Fin m := ⟨k,by omega⟩
  by_cases h0 : f (i 0 (by decide)) ≠ v ∧ f (i 0 (by decide)) ≠ w
  · exact ⟨f,rfl,h0,h⟩
  obtain ⟨p,ep,sp,hp⟩ := rotate_once G (by omega) f h
  have sp0 : p (i 0 (by decide)) = f (i 1 (by decide)) := sp _ (by simp [i]; omega)
  by_cases h1 : f (i 1 (by decide)) ≠ v ∧ f (i 1 (by decide)) ≠ w
  · refine ⟨p,ep,?_,hp⟩
    change p (i 0 (by decide)) ≠ v ∧ p (i 0 (by decide)) ≠ w
    simpa only [sp0] using h1
  obtain ⟨q,eq,sq,hq⟩ := rotate_once G (by omega) p hp
  have sq0 : q (i 0 (by decide)) = p (i 1 (by decide)) := sq _ (by simp [i]; omega)
  have sp1 : p (i 1 (by decide)) = f (i 2 (by decide)) := sp _ (by simp [i]; omega)
  have distinct (a b : ℕ) (ha : a < 3) (hb : b < 3) (ne : a ≠ b) :
      f (i a ha) ≠ f (i b hb) := fun e => ne (congrArg Fin.val (f.injective e))
  have h0' : f (i 0 (by decide)) = v ∨ f (i 0 (by decide)) = w := by
    by_cases t : f (i 0 (by decide)) = v
    · exact Or.inl t
    · by_cases t' : f (i 0 (by decide)) = w
      · exact Or.inr t'
      · exact (h0 ⟨t,t'⟩).elim
  have h1' : f (i 1 (by decide)) = v ∨ f (i 1 (by decide)) = w := by
    by_cases t : f (i 1 (by decide)) = v
    · exact Or.inl t
    · by_cases t' : f (i 1 (by decide)) = w
      · exact Or.inr t'
      · exact (h1 ⟨t,t'⟩).elim
  refine ⟨q,eq.trans ep,?_,hq⟩
  change q (i 0 (by decide)) ≠ v ∧ q (i 0 (by decide)) ≠ w
  rw [sq0,sp1]
  obtain n01 := distinct 0 1 (by decide) (by decide) (by decide)
  obtain n02 := distinct 0 2 (by decide) (by decide) (by decide)
  obtain n12 := distinct 1 2 (by decide) (by decide) (by decide)
  constructor <;> intro h2 <;> rcases h0' with a | a <;> rcases h1' with b | b
  all_goals first | exact n01 (a.trans b.symm) | exact n02 (a.trans h2.symm) |
    exact n12 (b.trans h2.symm)


private theorem cut_eq_rem [DecidableEq V] {m : ℕ} (f : Fin m ↪ V) (lo len : ℕ) (h : lo+len≤m)
    (a d : Fin m)
    (rem : ∀ i : Fin m, (lo ≤ i.val ∧ i.val < lo+len) ↔ i ≠ a ∧ i ≠ d) :
    indexSet (cutIndex f lo len h) = indexSet f \ {f a,f d} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨j,rfl⟩ := mem_indexSet.mp hx
    let i : Fin m := ⟨lo+j.val,by have := j.isLt; omega⟩
    change f i ∈ indexSet (cutIndex f lo len h) at hx
    change f i ∈ indexSet f \ {f a,f d}
    obtain ⟨na,nd⟩ := (rem i).mp ((in_cutIndex f lo len h i).mp hx)
    exact mem_sdiff.mpr ⟨mem_indexSet_self f i,by simp [f.injective.ne na,f.injective.ne nd]⟩
  · rintro hx
    obtain ⟨i,rfl⟩ := mem_indexSet.mp (mem_sdiff.mp hx).1
    apply (in_cutIndex f lo len h i).mpr
    apply (rem i).mpr
    have hnot := (mem_sdiff.mp hx).2
    simp only [mem_insert,mem_singleton,not_or] at hnot
    exact ⟨fun e => hnot.1 (congrArg f e),fun e => hnot.2 (congrArg f e)⟩

/-- Append a fresh vertex to the indexed vertex set. -/
private def addEnd {m : ℕ} (f : Fin m ↪ V) (u : V) (hu : u ∉ indexSet f) :
    Fin (m+1) ↪ V where
  toFun i := if h : i.val<m then f ⟨i.val,h⟩ else u
  inj' := by
    intro i j e
    have mi := i.isLt
    have mj := j.isLt
    by_cases hi : i.val<m <;> by_cases hj : j.val<m <;> simp only [hi,hj,dif_pos,dif_neg] at e
    · exact Fin.ext (congrArg (fun z : Fin m => z.val) (f.injective e))
    · exact (hu (mem_indexSet.mpr ⟨_,e⟩)).elim
    · exact (hu (mem_indexSet.mpr ⟨_,e.symm⟩)).elim
    · apply Fin.ext; omega

private theorem addEnd_in {m : ℕ} (f : Fin m ↪ V) (u : V) (hu : u ∉ indexSet f) :
    indexSet f ⊆ indexSet (addEnd f u hu) := by
  intro x hx
  obtain ⟨i,rfl⟩ := mem_indexSet.mp hx
  exact mem_indexSet.mpr ⟨⟨i.val,by have := i.isLt; omega⟩,by simp [addEnd,i.isLt]⟩

private theorem path_close {m : ℕ} (hm : 6≤m) (f : Fin m ↪ V)
    (path : ∀ i j, G.Adj (f i) (f j) ↔ PathAdj i j)
    (u : V) (hu : u ∉ indexSet f)
    (endAdj : ∀ i, G.Adj u (f i) ↔ i.val=0 ∨ i.val+1=m) :
    ∀ i j, G.Adj ((addEnd f u hu) i) ((addEnd f u hu) j) ↔ CycleAdj i j := by
  intro i j
  have mi := i.isLt
  have mj := j.isLt
  by_cases hi : i.val<m <;> by_cases hj : j.val<m
  · change G.Adj (if h : i.val<m then f ⟨i.val,h⟩ else u)
      (if h : j.val<m then f ⟨j.val,h⟩ else u) ↔ _
    simp only [hi,hj,dif_pos,path,PathAdj,CycleAdj]
    omega
  · change G.Adj (if h : i.val<m then f ⟨i.val,h⟩ else u)
      (if h : j.val<m then f ⟨j.val,h⟩ else u) ↔ _
    rw [dif_pos hi,dif_neg hj,G.adj_comm,endAdj]
    simp [CycleAdj]
    omega
  · change G.Adj (if h : i.val<m then f ⟨i.val,h⟩ else u)
      (if h : j.val<m then f ⟨j.val,h⟩ else u) ↔ _
    rw [dif_neg hi,dif_pos hj,endAdj]
    simp [CycleAdj]
    omega
  · change G.Adj (if h : i.val<m then f ⟨i.val,h⟩ else u)
      (if h : j.val<m then f ⟨j.val,h⟩ else u) ↔ _
    rw [dif_neg hi,dif_neg hj]
    simp only [CycleAdj,G.irrefl, false_iff]
    omega

private def replaceStart {m : ℕ} (f : Fin m ↪ V) (a d : V)
    (aout : a ∉ indexSet f) (dout : d ∉ indexSet f) (ad : a ≠ d) : Fin (m+1) ↪ V where
  toFun i := if i.val=0 then a else if hi : i.val<m then f ⟨i.val,hi⟩ else d
  inj' := by
    intro i j e
    have mi := i.isLt
    have mj := j.isLt
    by_cases iz : i.val=0 <;> by_cases jz : j.val=0 <;>
      by_cases hi : i.val<m <;> by_cases hj : j.val<m <;>
      simp only [iz,jz,hi,hj,if_pos,if_neg,dif_pos,dif_neg] at e
    all_goals first
      | exact (ad e).elim
      | exact (ad e.symm).elim
      | exact (aout (mem_indexSet.mpr ⟨_,e⟩)).elim
      | exact (aout (mem_indexSet.mpr ⟨_,e.symm⟩)).elim
      | exact (dout (mem_indexSet.mpr ⟨_,e⟩)).elim
      | exact (dout (mem_indexSet.mpr ⟨_,e.symm⟩)).elim
      | exact Fin.ext (congrArg (fun z : Fin m => z.val) (f.injective e))
      | apply Fin.ext; omega

private theorem replaceStart_in {m : ℕ} (f : Fin m ↪ V) (a d : V)
    (aout : a ∉ indexSet f) (dout : d ∉ indexSet f) (ad : a ≠ d)
    (i : Fin m) (hi : i.val≠0) : f i ∈ indexSet (replaceStart f a d aout dout ad) := by
  exact mem_indexSet.mpr ⟨⟨i.val,by have := i.isLt; omega⟩,
    by simp [replaceStart,hi,i.isLt]⟩

private theorem replaced_adj {m : ℕ} (hm : 6≤m) (f : Fin m ↪ V)
    (cyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (a d : V) (aout : a ∉ indexSet f) (dout : d ∉ indexSet f) (ad : a ≠ d)
    (ab : ∀ i, i.val≠0 → (G.Adj a (f i) ↔ i.val=1))
    (db : ∀ i, i.val≠0 → (G.Adj d (f i) ↔ i.val+1=m)) :
    ∀ i j, G.Adj ((replaceStart f a d aout dout ad) i) ((replaceStart f a d aout dout ad) j) ↔
      PathAdj i j ∨ (G.Adj a d ∧
        ((i.val=0 ∧ j.val=m) ∨ (j.val=0 ∧ i.val=m))) := by
  intro i j
  have mi := i.isLt
  have mj := j.isLt
  change G.Adj
    (if i.val=0 then a else if hi : i.val<m then f ⟨i.val,hi⟩ else d)
    (if j.val=0 then a else if hj : j.val<m then f ⟨j.val,hj⟩ else d) ↔ _
  by_cases iz : i.val=0 <;> by_cases jz : j.val=0 <;>
    by_cases hi : i.val<m <;> by_cases hj : j.val<m <;>
    simp [iz,jz,hi,hj,PathAdj,G.irrefl] 
  all_goals try omega
  all_goals try rw [cyc]
  all_goals try rw [ab _ (by assumption)]
  all_goals try rw [db _ (by assumption)]
  all_goals try rw [adj_comm (v := a),ab _ (by assumption)]
  all_goals try rw [adj_comm (v := d),db _ (by assumption)]
  all_goals try rw [adj_comm (u := d) (v := a)]
  all_goals try unfold CycleAdj
  all_goals try simp only [Fin.val_mk]
  all_goals by_cases adjAD : G.Adj a d <;> (try simp [adjAD])
  all_goals try omega
  all_goals have inz : i ≠ 0 := fun e => iz (by simp [e])
  all_goals have jnz : j ≠ 0 := fun e => jz (by simp [e])
  all_goals simp only [inz,jnz,false_and,or_false]


variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem blocker_for_interval {seed : Finset V} (B : Graffiti179.Block G univ seed)
    (hc : G.Connected) (hf : ¬ Claim183 G) {m : ℕ} (f : Fin m ↪ V)
    (eq : indexSet f = B.A ∪ B.B)
    (step : ∀ i j, i.val+1=j.val → G.Adj (f i) (f j))
    (lo len : ℕ) (h : lo+len ≤ m) (pos : 0 < len) {a d : Fin m} (ne : a ≠ d)
    (rem : ∀ i : Fin m, (lo ≤ i.val ∧ i.val < lo+len) ↔ i ≠ a ∧ i ≠ d)
    (aDom : ∃ j : Fin m, lo ≤ j.val ∧ j.val < lo+len ∧ G.Adj (f a) (f j))
    (dDom : ∃ j : Fin m, lo ≤ j.val ∧ j.val < lo+len ∧ G.Adj (f d) (f j)) :
    ∃ x ∉ indexSet f, ∀ i : Fin m, G.Adj x (f i) ↔ i = a ∨ i = d := by
  classical
  have red := cut_eq_rem f lo len h a d rem
  have con := cut_con G f step lo len h pos
  rw [red,eq] at con
  have dom {y : Fin m} (h' : ∃ j : Fin m, lo ≤ j.val ∧ j.val < lo+len ∧ G.Adj (f y) (f j)) :
      Graffiti177.Dominates G ((B.A ∪ B.B) \ {f a,f d}) (f y) := by
    obtain ⟨j,lo',hi',e⟩ := h'
    have mem := (in_cutIndex f lo len h j).mpr ⟨lo',hi'⟩
    rw [red,eq] at mem
    exact ⟨f j,mem,e⟩
  have af : f a ∈ B.A ∪ B.B := eq ▸ mem_indexSet_self f a
  have df : f d ∈ B.A ∪ B.B := eq ▸ mem_indexSet_self f d
  obtain ⟨x,hx,only⟩ := exact_blocker G B hc hf af df (f.injective.ne ne) con
    (dom aDom) (dom dDom)
  refine ⟨x,by simpa only [eq] using hx,?_⟩
  intro i
  exact (only _ (eq ▸ mem_indexSet_self f i)).trans (or_congr f.injective.eq_iff f.injective.eq_iff)

private theorem path_make_hole {seed : Finset V} (B : Graffiti179.Block G univ seed)
    (hc : G.Connected) (hf : ¬ Claim183 G) {m : ℕ} (hm : 6 ≤ m)
    (f : Fin m ↪ V) (eq : indexSet f = B.A ∪ B.B)
    (pa : ∀ i j, G.Adj (f i) (f j) ↔ PathAdj i j) :
    ∃ p : Fin (m+1) ↪ V, seed ⊆ indexSet p ∧ ∀ i j, G.Adj (p i) (p j) ↔ CycleAdj i j := by
  let a : Fin m := ⟨0,by omega⟩
  let d : Fin m := ⟨m-1,by omega⟩
  have rem (i : Fin m) : (1 ≤ i.val ∧ i.val < 1+(m-2)) ↔ i ≠ a ∧ i ≠ d := by
    simp only [ne_eq,Fin.ext_iff,a,d,Fin.val_mk]
    have := i.isLt
    omega
  have step i j (h : i.val+1=j.val) : G.Adj (f i) (f j) := (pa i j).mpr (Or.inl h)
  have ne : a ≠ d := by simp [a,d,Fin.ext_iff]; omega
  have aDom : ∃ j : Fin m, 1 ≤ j.val ∧ j.val < 1+(m-2) ∧ G.Adj (f a) (f j) := by
    refine ⟨⟨1,by omega⟩,by change 1 ≤ 1; omega,by simp; omega,?_⟩
    exact step _ _ rfl
  have dDom : ∃ j : Fin m, 1 ≤ j.val ∧ j.val < 1+(m-2) ∧ G.Adj (f d) (f j) := by
    refine ⟨⟨m-2,by omega⟩,by simp; omega,by simp,?_⟩
    exact (step _ _ (by simp [d]; omega)).symm
  obtain ⟨u,hu,adjU⟩ := blocker_for_interval G B hc hf f eq step 1 (m-2)
    (by omega) (by omega) ne rem aDom dDom
  have shape (i : Fin m) : G.Adj u (f i) ↔ i.val=0 ∨ i.val+1=m := by
    rw [adjU]
    simp only [Fin.ext_iff,a,d,Fin.val_mk]
    omega
  exact ⟨addEnd f u hu,(eq.symm ▸ B.seeded).trans (addEnd_in f u hu),
    path_close G hm f pa u hu shape⟩

private theorem cycle_make_larger {v w : V} (B : Graffiti179.Block G univ {v,w})
    (hc : G.Connected) (hf : ¬ Claim183 G) {m : ℕ} (hm : 6 ≤ m)
    (f : Fin m ↪ V) (eq : indexSet f = B.A ∪ B.B)
    (cyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j) :
    ∃ p : Fin (m+1) ↪ V, ({v,w} : Finset V) ⊆ indexSet p ∧
      ((∀ i j, G.Adj (p i) (p j) ↔ PathAdj i j) ∨
        (∀ i j, G.Adj (p i) (p j) ↔ CycleAdj i j)) := by
  obtain ⟨f',eq',⟨nv,nw⟩,cyc'⟩ := rotate_away G hm f cyc v w
  let a : Fin m := ⟨0,by omega⟩
  let j : Fin m := ⟨1,by omega⟩
  let d : Fin m := ⟨m-1,by omega⟩
  have eq' := eq'.trans eq
  have step (x y : Fin m) (h : x.val+1=y.val) : G.Adj (f' x) (f' y) :=
    (cyc' x y).mpr (Or.inl h)
  have r1 (i : Fin m) : (2 ≤ i.val ∧ i.val < 2+(m-2)) ↔ i ≠ a ∧ i ≠ j := by
    simp only [ne_eq,Fin.ext_iff,a,j,Fin.val_mk]
    have := i.isLt
    omega
  have r2 (i : Fin m) : (1 ≤ i.val ∧ i.val < 1+(m-2)) ↔ i ≠ a ∧ i ≠ d := by
    simp only [ne_eq,Fin.ext_iff,a,d,Fin.val_mk]
    have := i.isLt
    omega
  have ne1 : a ≠ j := by simp [a,j,Fin.ext_iff]
  have ne2 : a ≠ d := by simp [a,d,Fin.ext_iff]; omega
  have hwrap : G.Adj (f' a) (f' d) := by
    apply (cyc' _ _).mpr
    exact Or.inr (Or.inr (Or.inl ⟨rfl,by simp [d]; omega⟩))
  have a1 : ∃ k : Fin m, 2 ≤ k.val ∧ k.val < 2+(m-2) ∧ G.Adj (f' a) (f' k) :=
    ⟨d,by simp [d]; omega,by simp [d]; omega,hwrap⟩
  have j1 : ∃ k : Fin m, 2 ≤ k.val ∧ k.val < 2+(m-2) ∧ G.Adj (f' j) (f' k) :=
    ⟨⟨2,by omega⟩,by change 2 ≤ 2; omega,by simp; omega,step _ _ rfl⟩
  have a2 : ∃ k : Fin m, 1 ≤ k.val ∧ k.val < 1+(m-2) ∧ G.Adj (f' a) (f' k) :=
    ⟨j,by change 1 ≤ 1; omega,by simp [j]; omega,step _ _ rfl⟩
  have d2 : ∃ k : Fin m, 1 ≤ k.val ∧ k.val < 1+(m-2) ∧ G.Adj (f' d) (f' k) :=
    ⟨⟨m-2,by omega⟩,by simp; omega,by simp,(step _ _ (by simp [d]; omega)).symm⟩
  obtain ⟨x,hx,ex⟩ := blocker_for_interval G B hc hf f' eq' step 2 (m-2)
    (by omega) (by omega) ne1 r1 a1 j1
  obtain ⟨y,hy,ey⟩ := blocker_for_interval G B hc hf f' eq' step 1 (m-2)
    (by omega) (by omega) ne2 r2 a2 d2
  have neXY : x ≠ y := by
    intro xy
    have hJ := (ex j).mpr (Or.inr rfl)
    rw [xy,ey] at hJ
    rcases hJ with e | e
    · exact ne1 e.symm
    · have hh := congrArg Fin.val e
      simp [j,d] at hh
      omega
  have eX (i : Fin m) (nz : i.val ≠ 0) : G.Adj x (f' i) ↔ i.val=1 := by
    rw [ex]
    simp [Fin.ext_iff,a,j,nz]
  have eY (i : Fin m) (nz : i.val ≠ 0) : G.Adj y (f' i) ↔ i.val+1=m := by
    rw [ey]
    simp only [Fin.ext_iff,a,d,Fin.val_mk,nz,false_or]
    omega
  let p := replaceStart f' x y hx hy neXY
  have shape := replaced_adj G hm f' cyc' x y hx hy neXY eX eY
  refine ⟨p,?_,?_⟩
  · intro u hu
    have hu' : u ∈ indexSet f' := eq'.symm ▸ B.seeded hu
    obtain ⟨i,rfl⟩ := mem_indexSet.mp hu'
    apply replaceStart_in f' x y hx hy neXY i
    intro h0
    have ei : i = a := Fin.ext h0
    rw [ei] at hu
    rcases mem_insert.mp hu with it | it
    · exact nv it
    · exact nw (mem_singleton.mp it)
  · by_cases yes : G.Adj x y
    · right
      intro i j'
      rw [shape i j']
      simp only [yes,true_and,CycleAdj,PathAdj]
      omega
    · left
      intro i j'
      simpa only [yes,false_and,or_false] using shape i j'

/-- Step 1: a seeded connected bipartite block of size at least six forces
an odd hole of maximum-block order plus one in a hypothetical failure. -/
theorem large_odd_hole {v w : V} (hc : G.Connected) (hf : ¬ Claim183 G)
    (claw : ClawFree G) {seed : Finset V} (seed_v : v ∈ seed) (seed_w : w ∈ seed)
    (h6 : 6 ≤ seed.card) (con : Graffiti177.Con G seed) (bip : TwoColor G seed) :
    ∃ m : ℕ, 7 ≤ m ∧ m%2=1 ∧ ∃ f : Fin m ↪ V,
      ({v,w} : Finset V) ⊆ indexSet f ∧
      (∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j) ∧
      (∀ S : Finset V, v ∈ S → w ∈ S → Graffiti177.Con G S → TwoColor G S → S.card < m) := by
  classical
  let pair : Finset V := {v,w}
  have into : pair ⊆ seed := by simp [pair,insert_subset_iff,seed_v,seed_w]
  have mk (T : Finset V) (vT : v ∈ T) (wT : w ∈ T) : pair ⊆ T := by
    simp [pair,insert_subset_iff,vT,wT]
  -- Pick the largest connected bipartite superset of the pair, not of the full seed.
  let candidates := (univ : Finset (Finset V)).filter
    (fun T => pair ⊆ T ∧ Graffiti177.Con G T ∧ TwoColor G T)
  have seed_mem : seed ∈ candidates := mem_filter.mpr ⟨mem_univ _,into,con,bip⟩
  obtain ⟨S,hS,best⟩ := exists_max_image candidates Finset.card ⟨seed,seed_mem⟩
  obtain ⟨ps,sc,sb⟩ := (mem_filter.mp hS).2
  obtain ⟨B⟩ := exists_largest_block G sc sb
  have hSB := B.seeded
  have BU : B.A ∪ B.B ∈ candidates := mem_filter.mpr
    ⟨mem_univ _,ps.trans hSB,B.conn,⟨_,_,B.disjoint,rfl,B.indA,B.indB⟩⟩
  have eqS : S = B.A ∪ B.B := eq_of_subset_of_card_le hSB (best _ BU)
  let C : Graffiti179.Block G univ pair :=
    ⟨B.A,B.B,B.disjoint,B.indA,B.indB,B.conn,B.inside,ps.trans B.seeded,B.maximal⟩
  have ge : 6 ≤ (C.A ∪ C.B).card := by rw [show C.A ∪ C.B = S from eqS.symm]; exact h6.trans (best _ seed_mem)
  obtain ⟨m,hm,f,pat⟩ := block_index G C.conn
    ⟨C.A,C.B,C.disjoint,rfl,C.indA,C.indB⟩ claw ge
  have finish (P : Fin (m+1) ↪ V) (sub : pair ⊆ indexSet P)
      (asC : ∀ i j, G.Adj (P i) (P j) ↔ CycleAdj i j)
      (sz : (C.A ∪ C.B).card = m) :
      ∃ n : ℕ, 7 ≤ n ∧ n%2=1 ∧ ∃ F : Fin n ↪ V, pair ⊆ indexSet F ∧
        (∀ i j, G.Adj (F i) (F j) ↔ CycleAdj i j) ∧
        (∀ T : Finset V, v ∈ T → w ∈ T → Graffiti177.Con G T → TwoColor G T → T.card < n) := by
    have bound (T : Finset V) (inT : pair ⊆ T) (tc : Graffiti177.Con G T)
        (tb : TwoColor G T) : T.card ≤ m := by
      have c := best T (mem_filter.mpr ⟨mem_univ _,inT,tc,tb⟩)
      rw [eqS] at c
      exact c.trans (show (B.A ∪ B.B).card ≤ m from sz.le)
    have odd : (m+1)%2=1 := by
      by_contra no
      have even : (m+1)%2=0 := by omega
      have ⟨hcon,hbip⟩ := indexed_even_cycle_bip (G:=G) (by omega) even P asC
      have h := bound _ sub hcon hbip
      simp at h
    exact ⟨m+1,by omega,odd,P,sub,asC,fun T hv hw tc tb => Nat.lt_succ_of_le (bound T (mk T hv hw) tc tb)⟩
  rcases pat with ⟨eq,pa⟩ | ⟨eq,cyc⟩
  · obtain ⟨p,sub,cyc⟩ := path_make_hole G C hc hf hm f eq pa
    exact finish p sub cyc (by rw [←eq,indexSet_card])
  · obtain ⟨p,sub,pp|cc⟩ := cycle_make_larger G C hc hf hm f eq cyc
    · have ⟨pc,pb⟩ := indexed_path_bip (G:=G) (by omega) p pp
      have mem : indexSet p ∈ candidates := mem_filter.mpr ⟨mem_univ _,sub,pc,pb⟩
      have cap := best _ mem
      rw [indexSet_card,eqS,show B.A ∪ B.B = C.A ∪ C.B from rfl,←eq,indexSet_card] at cap
      omega
    · exact finish p sub cc (by rw [←eq,indexSet_card])

omit [DecidableRel G.Adj] in
theorem six_pattern_bip_seed {v w : V} (p : SixPattern G v w) :
    ∃ S : Finset V, v ∈ S ∧ w ∈ S ∧ 6 ≤ S.card ∧ Graffiti177.Con G S ∧ TwoColor G S := by
  classical
  let L := [w,p.q,p.a,v,p.b,p.p]
  let A : Finset V := {w,p.a,p.b}
  let B : Finset V := {p.q,v,p.p}
  let T := L.toFinset
  have ht : T.card = 6 := by
    change L.toFinset.card = 6
    rw [List.toFinset_card_of_nodup p.all_distinct]
    rfl
  have hcover : A ∪ B = T := by
    ext x
    simp [A,B,T,L,or_assoc,or_left_comm,or_comm]
  have hiA : Indep G A := by
    intro x hx y hy hn he
    simp only [A,mem_insert,mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact hn rfl
    · exact p.n_aw he.symm
    · exact p.n_wb he
    · exact p.n_aw he
    · exact hn rfl
    · exact p.n_ab he
    · exact p.n_wb he.symm
    · exact p.n_ab he.symm
    · exact hn rfl
  have hiB : Indep G B := by
    intro x hx y hy hn he
    simp only [B,mem_insert,mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact hn rfl
    · exact p.n_vq he.symm
    · exact p.n_qp he
    · exact p.n_vq he
    · exact hn rfl
    · exact p.n_vp he
    · exact p.n_qp he.symm
    · exact p.n_vp he.symm
    · exact hn rfl
  have hd : Disjoint A B := by
    have hh := p.all_distinct
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
      List.nodup_nil, not_false_eq_true, and_true] at hh
    rcases hh with ⟨⟨wq,wa,wv,wb,wp⟩,⟨qa,qv,qb,qp⟩,⟨av,ab,ap⟩,⟨vb,vp⟩,bp⟩
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [A,B,mem_insert,mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with h | h | h <;>
      first | exact wq h | exact wv h | exact wp h | exact qa h.symm |
        exact av h | exact ap h | exact qb h.symm | exact vb h.symm | exact bp h
  have h0 := Graffiti177.con_single G p.p
  have h1 := Graffiti177.con_insert G h0 (mem_singleton_self _) p.e_bp
  have h2 := Graffiti177.con_insert G h1 (mem_insert_self _ _) p.e_vb
  have h3 := Graffiti177.con_insert G h2 (mem_insert_self _ _) p.e_va.symm
  have h4 := Graffiti177.con_insert G h3 (mem_insert_self _ _) p.e_aq.symm
  have h5 := Graffiti177.con_insert G h4 (mem_insert_self _ _) p.e_qw.symm
  have conn : Graffiti177.Con G T := by simpa [T,L] using h5
  exact ⟨T,by simp [T,L],by simp [T,L],ht.ge,conn,A,B,hd,hcover,hiA,hiB⟩

#print axioms large_odd_hole

theorem hole_connected_dom_lower (hc : G.Connected) (hf : ¬ Claim183 G)
    {m : ℕ} (hm : 7 ≤ m) (f : Fin m ↪ V)
    (cyc : ∀ i j, G.Adj (f i) (f j) ↔ CycleAdj i j)
    (D : Finset V) (dc : Graffiti177.Con G D) (dom : ∀ v ∉ D, Graffiti177.Dominates G D v) :
    m-2 ≤ D.card := by
  classical
  let p := cutIndex f 0 (m-1) (by omega)
  have ppath (i j : Fin (m-1)) : G.Adj (p i) (p j) ↔ PathAdj i j := by
    change G.Adj (f ⟨0+i.val,_⟩) (f ⟨0+j.val,_⟩) ↔ _
    rw [cyc]
    simp only [CycleAdj,PathAdj,Fin.val_mk,Nat.zero_add]
    have := i.isLt
    have := j.isLt
    omega
  have ht := (indexed_path_bip (G:=G) (by omega) p ppath).2
  have bsmall : (indexSet p).card ≤ Short177.bipartiteNum G := by
    unfold Short177.bipartiteNum
    exact le_sup (s := univ.filter (TwoColor G)) (f := Finset.card)
      (mem_filter.mpr ⟨mem_univ _,ht⟩)
  have hb := bsmall.trans (Graffiti185.Reuse.bipartite_bridge G)
  rw [indexSet_card] at hb
  change m-1 ≤ Graffiti183.bipartiteNumber G at hb
  have hl : (univ \ D).card ≤ Graffiti183.maxLeaves G :=
    (Graffiti177.conDom_leaves G D dc dom).trans (Graffiti185.Reuse.leaves_bridge G)
  have hU := card_sdiff_add_card_eq_card (subset_univ D)
  rw [card_univ] at hU
  unfold Claim183 at hf
  have hu := metric_upper_bound hc
  omega

#print axioms hole_connected_dom_lower

end Graffiti183.Exceptional
