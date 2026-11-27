import CreditTrial31
namespace Graffiti384b.EarCredit
open SimpleGraph Finset JointRank
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b

def m (p : ℕ) := 29-p
def draws (p : ℕ) := 11-p
def mark (p i : ℕ) := if p = 1 ∧ i ≠ 0 then i+3 else i+2
def deg (s : ℕ) := if s≤2 then 3 else if s≤5 then 4 else if s≤8 then 5 else
  if s≤12 then 6 else if s≤16 then 7 else if s≤21 then 8 else if s≤27 then 9 else 10
def cost (p i : ℕ) := FiniteRange.badCount (m p) (draws p) (deg (mark p i))
def gain (p i d : ℕ) := cost p i-((m p)-d).choose (draws p)
def gap (p : ℕ) := if p=0 then 2734013 else 1193398

set_option maxRecDepth 20000 in
set_option maxHeartbeats 5000000 in
theorem table : ∀ p : Fin 2,
    (∀ i : Fin 29,∀ d : Fin 11,
      (mark p i≤RankTable.cap d 3 ∨ d.val=10) → (3≤mark p i → 4≤d.val) →
      FiniteRange.badCount (m p) (draws p) d≤cost p i ∧
      (((m p)-d.val).choose (draws p))+gain p i d≤cost p i ∧
      (d.val≤6 → gap p<gain p i d) ∧
      (p.val=0 → d.val≤7 → 2116296≤gain p i d) ∧
      (p.val=0 → d.val≤9 → 739024≤gain p i d) ∧
      (p.val=1 → 218790≤gain p i d) ∧
      (p.val=1 → d.val≤7 → 1007760≤gain p i d) ∧
      (p.val=1 → i.val<25 → 388960≤gain p i d)) ∧
    ((m p-draws p)*(m p).choose (draws p)+CliqueSample.bonus (m p) (draws p) 2+
      p.val*CliqueSample.bonus (m p) (draws p) 3+gap p =
      15*(m p).choose (draws p)+∑ i∈range (m p),cost p i) := by
  unfold gap gain cost deg mark m draws RankTable.cap CliqueSample.bonus FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
private theorem credited {W : Finset V} {v z : V} (vm : v∈W) (off : z∉W) (vz : G.Adj v z) (b : ℕ) :
    ((W.powersetCard b).filter (fun k => v∈FiniteRange.bad G W k)).card≤(W.card-G.degree v).choose b := by
  classical
  by_cases inc : G.neighborFinset v⊆insert z W
  · exact EarPalette.credited_count G vm vz off inc b
  obtain ⟨y,yn,out⟩ := not_subset.mp inc
  obtain ⟨yz,yw⟩ := (show y≠z ∧ y∉W by simpa [not_or] using out)
  have empty : ((W.powersetCard b).filter (fun k => v∈FiniteRange.bad G W k))=∅ := eq_empty_of_forall_not_mem (by
    intro k km; have low := (mem_filter.mp (mem_filter.mp km).2).2
    have two := PinnedColor34.two G yz ((G.mem_neighborFinset ..).mp yn) vz
      (mem_union_left k (mem_compl.mpr yw)) (mem_union_left k (mem_compl.mpr off))
    omega)
  rw [empty,card_empty]; exact Nat.zero_le _

def credit (p : ℕ) (P : Finset V) (r : V→ℕ) (v : V) :=
  if 0<nbr G v P then gain p (r v) (min (G.degree v) 10) else 0

/-- All fixed-neighbor credits share one bound. The rank injection also
limits how many credited vertices can receive any given high-rank allowance. -/
theorem account {P : Finset V} {p : ℕ} (pm : p≤1) (ws : Pᶜ.card=m p)
    (n : Fintype.card V=30) (hi : 15≤gamma G) (free : G.CliqueFree 5)
    (fi : Function.Injective (trianglesAt G))
    (scores : ∀ v∈Pᶜ,2≤trianglesAt G v ∧ (p=1 → trianglesAt G v≠3))
    (small : ∀ v∈Pᶜ,3≤trianglesAt G v → 4≤G.degree v)
    (sc : ∀ z∈P,∀ u v,G.Adj z u → G.Adj z v → u≠v → G.Adj u v)
    (ind : ∀ z∈P,G.neighborFinset z⊆Pᶜ)
    (bonus : (∑ z∈P,CliqueSample.bonus (m p) (draws p) (G.degree z))=
      CliqueSample.bonus (m p) (draws p) 2+p*CliqueSample.bonus (m p) (draws p) 3) :
    ∃ r : V→ℕ,Set.InjOn r ((Pᶜ : Finset V):Set V) ∧ (∀ v∈Pᶜ,r v<m p) ∧
      (∀ v∈Pᶜ,(mark p (r v)≤RankTable.cap (min (G.degree v) 10) 3 ∨ min (G.degree v) 10=10) ∧
        (3≤mark p (r v) → 4≤min (G.degree v) 10)) ∧
      (∑ v∈Pᶜ,credit G p P r v)≤gap p := by
  classical
  let W := Pᶜ
  let f (v : V) := if p=1 ∧ 3<trianglesAt G v then trianglesAt G v-1 else trianglesAt G v
  have inj : Set.InjOn f (W:Set V) := by
    intro v vm w wm eq; have := scores v vm; have := scores w wm
    apply fi; unfold f at eq; split_ifs at eq <;> omega
  have low (v : V) (vm : v∈W) : 2≤f v := by have := scores v vm; unfold f; split_ifs <;> omega
  let r := rank W f
  have rm (v : V) (vm : v∈W) : r v<m p := by
    have t := mem_image_of_mem (rank W f) vm
    rw [rank_range W f inj,show W.card=m p from ws,mem_range] at t; exact t
  have score (v : V) (vm : v∈W) : mark p (r v)≤trianglesAt G v := by
    have b := rank_lower W f inj 2 low vm
    change 2+r v≤f v at b; dsimp [f] at b; have := scores v vm
    unfold mark; split_ifs at * <;> omega
  have test (v : V) (vm : v∈W) :
      (mark p (r v)≤RankTable.cap (min (G.degree v) 10) 3 ∨ min (G.degree v) 10=10) ∧
        (3≤mark p (r v) → 4≤min (G.degree v) 10) := by
    have lo := score v vm
    refine ⟨?_,fun h => le_min (small v vm (h.trans lo)) (by decide)⟩
    by_cases d : G.degree v≤10
    · rw [min_eq_left d]
      exact Or.inl (lo.trans ((RankTuran.local_turan G 3 (by decide) free v).trans_eq
        (RankTable.cap_table ⟨G.degree v,by omega⟩ ⟨3,by decide⟩ (by decide))))
    · exact Or.inr (min_eq_right (by omega))
  let K := W.powersetCard (draws p)
  let bill (v : V) := (K.filter (fun k => v∈FiniteRange.bad G W k)).card
  have line (v : V) (vm : v∈W) : bill v+credit G p P r v≤cost p (r v) := by
    let d := min (G.degree v) 10
    have ds : d≤10 := min_le_right ..
    have dr : d≤G.degree v := min_le_left ..
    have j := rm v vm; unfold m at j
    obtain ⟨a,b,_⟩ := (table ⟨p,by omega⟩).1 ⟨r v,by omega⟩ ⟨d,by omega⟩ (test v vm).1 (test v vm).2
    unfold credit; split_ifs with pos
    · obtain ⟨z,zm⟩ := card_pos.mp pos
      obtain ⟨zp,vz⟩ := mem_filter.mp zm
      have c := credited G vm (fun h => mem_compl.mp h zp) vz (draws p)
      change bill v≤(W.card-G.degree v).choose (draws p) at c
      rw [show W.card=m p from ws] at c
      have h := Nat.choose_le_choose (draws p) (Nat.sub_le_sub_left dr (m p))
      exact (Nat.add_le_add_right (c.trans h) _).trans b
    · rw [Nat.add_zero]
      have cap := FiniteRange.count_bad G W (draws p) d v vm dr (by change d<Pᶜ.card; rw [ws]; unfold m; omega)
      rw [show W.card=m p from ws] at cap; exact cap.trans a
  have upper := sum_le_sum line
  rw [sum_add_distrib,sum_by_rank W f inj (cost p),show W.card=m p from ws] at upper
  have lower := sum_count G (draws p) n hi sc ind
  dsimp only at lower
  rw [ws,bonus] at lower
  change _≤15*(m p).choose (draws p)+∑ v∈W,bill v at lower
  have eq := (table ⟨p,by omega⟩).2
  change (m p-draws p)*(m p).choose (draws p)+CliqueSample.bonus (m p) (draws p) 2+
      p*CliqueSample.bonus (m p) (draws p) 3+gap p=15*(m p).choose (draws p)+∑ i∈range (m p),cost p i at eq
  refine ⟨r,rank_inj W f inj,rm,test,?_⟩
  change (∑ v∈W,credit G p P r v)≤gap p
  omega

end Graffiti384b.EarCredit
#print axioms Graffiti384b.EarCredit.table
#print axioms Graffiti384b.EarCredit.account
