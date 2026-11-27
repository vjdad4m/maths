import SoloAllRows

namespace OffFour16Solo
open Finset

private theorem count_from_site_color {s t : ℕ} {m : Marks} {col : Fin 3}
    (h0 : m 0=1) (h10 : m 10=2)
    (holes : ∀ k : Fin 11,Hole k.val s t → m k=0)
    (hc : col=1 ∨ col=2) (four : 4≤markCount m col) :
    3≤((sites s t).map m).count col := by
  classical
  let d : Fin 11 := if col=1 then 0 else 10
  let A := (univ : Finset (Fin 11)).filter (fun k => m k=col)
  let L := (sites s t).filter (fun k => m k == col)
  have dc : m d=col := by rcases hc with rfl|rfl <;> simp [d,h0,h10]
  have nb : col≠0 := by rcases hc with rfl|rfl <;> decide
  have Aeq : L.toFinset=A.erase d := by
    ext k
    constructor
    · intro kL
      obtain ⟨kf,kc⟩ := List.mem_filter.mp (List.mem_toFinset.mp kL)
      have ts := of_decide_eq_true (List.mem_filter.mp kf).2
      have kd : k≠d := by
        intro ek
        rcases hc with rfl|rfl
        · exact ts.1 (by simpa [d] using congrArg Fin.val ek)
        · exact ts.2.1 (by simpa [d] using congrArg Fin.val ek)
      exact mem_erase.mpr ⟨kd,mem_filter.mpr ⟨mem_univ _,beq_iff_eq.mp kc⟩⟩
    · intro km
      obtain ⟨kd,kA⟩ := mem_erase.mp km
      have kc := (mem_filter.mp kA).2
      have k0 : k.val≠0 := by
        intro eq
        have kk : k=0 := Fin.ext eq
        rcases hc with rfl|rfl
        · exact kd (by simpa [d] using kk)
        · rw [kk,h0] at kc; contradiction
      have k10 : k.val≠10 := by
        intro eq
        have kk : k=10 := Fin.ext eq
        rcases hc with rfl|rfl
        · rw [kk,h10] at kc; contradiction
        · exact kd (by simpa [d] using kk)
      have h : ¬Hole k.val s t := fun e => nb (kc.symm.trans (holes k e))
      apply List.mem_toFinset.mpr
      exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_finRange _,decide_eq_true ⟨k0,k10,h⟩⟩,
        beq_iff_eq.mpr kc⟩
  have ns : (sites s t).Nodup := (List.nodup_finRange 11).filter _
  have nd : L.Nodup := ns.filter _
  have cEq : ((sites s t).map m).count col=L.length := by
    rw [List.count,List.countP_map,List.countP_eq_length_filter]
    rfl
  have ca := congrArg Finset.card Aeq
  have da : d∈A := mem_filter.mpr ⟨mem_univ _,dc⟩
  rw [List.toFinset_card_of_nodup nd,card_erase_of_mem da] at ca
  change 4≤A.card at four
  omega

theorem check_row {i j x y s t : ℕ} {m : Marks} (ok : row i j=true)
    (xs : (x,y)∈([(1,2),(2,1),(1,3),(2,2),(3,1)] : List (ℕ×ℕ)))
    (fs : fit i j s t=true) (h0 : m 0=1) (h9 : m 10=2)
    (holes : ∀ k : Fin 11, Hole k.val s t → m k=0)
    (sparseH : ((sites s t).map m).count 0≤1)
    (ml : 4≤markCount m 1) (mr : 4≤markCount m 2)
    (pallow : PinsAllowed i j m=true)
    (dleft : (d2Set i j x y m 0).card≤4)
    (dright : (d2Set i j x y m 11).card≤4) :
    Spanning i j x y m ∨ exceptional i j x y m=true := by
  have F : 1≤s ∧ s≤9 ∧ 1≤t ∧ t≤9 ∧ (s=i-1 ∨ s=j-1) ∧ (t=i ∨ t=j) := by
    simpa only [fit,decide_eq_true_eq] using fs
  unfold row at ok
  have ss : s∈[i-1,j-1] := by simpa using F.2.2.2.2.1
  have tt : t∈[i,j] := by simpa using F.2.2.2.2.2
  have e := List.all_eq_true.mp (List.all_eq_true.mp ok s ss) t tt
  have q : part i j s t=true := by simpa [fs] using e
  let d := (sites s t).map m
  have dd : d∈sparse (sites s t).length := by simpa [d] using mem_sparse sparseH
  have cb := List.all_eq_true.mp q d dd
  have eq : decode s t d=m := decode_full s t m h0 h9 holes
  have fastleft := (card_le_card (fastD2Set_subset i j x y m 0)).trans dleft
  have fastright := (card_le_card (fastD2Set_subset i j x y m 11)).trans dright
  have yes : validMarks i j m=true := by simp [validMarks,ml,mr,pallow]
  have raw : 3≤d.count 1 ∧ 3≤d.count 2 :=
    ⟨count_from_site_color h0 h9 holes (.inl rfl) ml,
     count_from_site_color h0 h9 holes (.inr rfl) mr⟩
  have pop : populations.all (fun (x,y) => gate i j x y m)=true := by
    simpa [eq,yes,raw] using cb
  have cb' := List.all_eq_true.mp pop (x,y) (show (x,y)∈populations from xs)
  have hz : hasPath i j x y m=true ∨ exceptional i j x y m=true := by
    simpa [gate,fastleft,fastright,Bool.or_eq_true] using cb'
  exact hz.imp hasPath_sound id

end OffFour16Solo

namespace OffFour16Solo
open Finset

def atPort (i : ℕ) : Vertex := Fin.ofNat' 16 i

def knownExtra (i j x y : ℕ) (m : Marks) (p : ℕ) : Bool :=
  (decide (p≠1) && edge i j x y m (atPort p) 0) ||
  (decide (p≠10) && edge i j x y m (atPort p) 11)

def optSites (i j x y : ℕ) (m : Marks) (p q : ℕ) : List Vertex :=
  if knownExtra i j x y m p then [atPort p] else
  (atPort p)::((List.finRange 16).filter (fun v => decide
    (1≤v.val ∧ v.val≤10 ∧ v.val≠p ∧ v.val≠p-1 ∧ v.val≠p+1 ∧ v.val≠q)))

def pair (u v a b : Vertex) : Bool := decide (u=a ∧ v=b ∨ u=b ∧ v=a)

def edgeAug (i j x y : ℕ) (m : Marks) (e : Bool) (r s : Vertex) (u v : Vertex) : Bool :=
  edge i j x y m u v ||
  (e && pair u v (atPort i) (atPort j)) ||
  (decide (r≠atPort i) && pair u v (atPort i) r) ||
  (decide (s≠atPort j) && pair u v (atPort j) s)

def d2Aug (i j x y : ℕ) (m : Marks) (e : Bool) (r s : Vertex) (u : Vertex) : Finset Vertex :=
  univ.filter fun v => v≠u ∧ !edgeAug i j x y m e r s u v=true ∧
    ∃ w : Vertex, edgeAug i j x y m e r s u w=true ∧ edgeAug i j x y m e r s w v=true

def decodeException (b : Exception) : Marks :=
  fun v => b.marks[v.val]?.getD 0

theorem decodeException_eq (b : Exception) (m : Marks) (eq : b.marks=List.ofFn m) :
    decodeException b=m := by
  funext k
  fin_cases k <;> simp [decodeException,eq]

def exceptionPass (b : Exception) : Bool :=
  let m := decodeException b
  [false,true].all fun e =>
    (optSites b.i b.j b.x b.y m b.i b.j).all fun r =>
      (optSites b.i b.j b.x b.y m b.j b.i).all fun s =>
        !(decide ((d2Aug b.i b.j b.x b.y m e r s (atPort b.i)).card≤4 ∧
          (d2Aug b.i b.j b.x b.y m e r s (atPort b.j)).card≤4))

set_option maxHeartbeats 0 in
set_option maxRecDepth 18000 in
theorem exceptions_rejected : exceptions.all exceptionPass=true := by decide +kernel
#print axioms exceptions_rejected

theorem actual_exc_reject {i j x y : ℕ} {m : Marks} {e : Bool} {r s : Vertex}
    (q : exceptional i j x y m=true)
    (ro : r∈optSites i j x y m i j) (so : s∈optSites i j x y m j i)
    (di : (d2Aug i j x y m e r s (atPort i)).card≤4)
    (dj : (d2Aug i j x y m e r s (atPort j)).card≤4) :
    False := by
  obtain ⟨b,bm,bb⟩ := List.any_eq_true.mp q
  obtain ⟨hi,hj,hx,hy,hm⟩ := of_decide_eq_true bb
  have valid := List.all_eq_true.mp exceptions_rejected b bm
  unfold exceptionPass at valid
  have E := List.all_eq_true.mp valid e (by cases e <;> simp)
  simp only [hi,hj,hx,hy,decodeException_eq _ _ hm] at E
  have R := List.all_eq_true.mp E r ro
  have S := List.all_eq_true.mp R s so
  simp [di,dj] at S

end OffFour16Solo
