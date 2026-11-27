import AlternatingGuard
import SparseCubic
namespace Graffiti384b.SparsePairs
open Finset SimpleGraph JointRank
open private Squares29.pair_at from SquareTriple29
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 1200000 in
/-- An anchor on a triangle of anchors, with the stated sampling saving,
forces at least ten exterior contacts outside its private row. The hypotheses describing the rank
sum and the links are all instantiated on the original graph in sparse_frontier. -/
theorem ten_contacts (A : Finset V) {e f w : V}
    (t : (types G).card=31) (q : (nonleaves G).card=31) (bad : bound G<gamma G) (de : G.degree e=2) (df : G.degree f=2) (ef : e≠f)
    (Aeq : G.neighborFinset e∪G.neighborFinset f=A) (dis : Disjoint (G.neighborFinset e) (G.neighborFinset f))
    (ac : A.card=4) (ah : A⊆high G) (wn : w∈G.neighborFinset e) 
    (privateRow : ∀ i∈high G\A,G.Adj w i → nbr G i A=1)
    (triangle : ∃ i∈A,∃j∈A,G.Adj w i ∧ G.Adj w j ∧ G.Adj i j)
    (low : ∀ a∈A,nbr G a (LowSample.twos G)≤1)
    (pExists : ∃p∈A,nbr G p A≤1)
    (cr : V → ℕ)
    (pays : ∀a∈A,739024≤cr a ∧ (trianglesAt G a≤5 → 4975245≤cr a) ∧
      (trianglesAt G a≤14 → 3233230≤cr a) ∧ (trianglesAt G a≤20 → 2116296≤cr a) ∧
      (trianglesAt G a≤23 → 1293292≤cr a))
    (sumCap : 8042111+(∑a∈A.erase w,cr a)≤12407000) :
    nbr G w (high G\A)+10≤((high G\A).filter (fun v => 0<nbr G v A)).card := by
  classical
  let X := high G\A
  let H := X.filter (fun v => 0<nbr G v A)
  let k := fun a => nbr G a X
  change k w+10≤H.card
  apply Nat.le_of_not_gt; intro small
  have wa : w∈A := Aeq ▸ mem_union_left _ wn
  obtain ⟨b,wb,be⟩ := Squares29.pair_at ((card_neighborFinset_eq_degree ..).trans de) wn
  obtain ⟨c,d,cd,cf⟩ := card_eq_two.mp ((card_neighborFinset_eq_degree ..).trans df)
  have bn : b∈G.neighborFinset e := be ▸ mem_insert_of_mem (mem_singleton_self _)
  have cn : c∈G.neighborFinset f := cf ▸ mem_insert_self ..
  have dn : d∈G.neighborFinset f := cf ▸ mem_insert_of_mem (mem_singleton_self _)
  have ba : b∈A := Aeq ▸ mem_union_left _ bn
  have ca : c∈A := Aeq ▸ mem_union_right _ cn
  have da : d∈A := Aeq ▸ mem_union_right _ dn
  have apart {i j : V} (ie : i∈G.neighborFinset e) (jf : j∈G.neighborFinset f) : i≠j :=
    fun eq => disjoint_left.mp dis ie (eq.symm ▸ jf)
  have wc := apart wn cn
  have wd := apart wn dn
  have bc := apart bn cn
  have bd := apart bn dn
  have blind {a i : V} (aa : a∈A) (aw : a≠w) (ix : i∈X) (ai : G.Adj a i) : ¬G.Adj i w := by
    intro iw; have one := privateRow i ix iw.symm
    have two := PinnedColor34.two G aw ai.symm iw aa wa; omega
  let row := fun a => X.filter (G.Adj a)
  have into (a : V) (aa : a∈A) : row a⊆H := fun i im =>
    mem_filter.mpr ⟨(mem_filter.mp im).1,card_pos.mpr ⟨a,mem_filter.mpr ⟨aa,(mem_filter.mp im).2.symm⟩⟩⟩
  have sep (a : V) (aa : a∈A) (aw : a≠w) : Disjoint (row a) (row w) := disjoint_left.mpr
    (fun i ai wi => blind aa aw (mem_filter.mp ai).1 (mem_filter.mp ai).2 (mem_filter.mp wi).2.symm)
  have lim (a : V) (aa : a∈A) (aw : a≠w) : k a≤9 := by
    have ct := card_le_card (union_subset (into a aa) (into w wa))
    rw [card_union_of_disjoint (sep a aa aw)] at ct
    change k a+k w≤H.card at ct; omega
  have must (a : V) (aa : a∈A) (aw : a≠w) : 15≤trianglesAt G a := by
    apply Nat.le_of_not_gt; intro neg
    have pay := (pays a aa).2.2.1 (by omega)
    have aw' : a∈A.erase w := mem_erase.mpr ⟨aw,aa⟩
    let T := (A.erase w).erase a
    have sz : T.card=2 := by dsimp [T]; rw [card_erase_of_mem aw',card_erase_of_mem wa,ac]
    have rem := sum_le_sum (s:=T) (fun i im => (pays i (mem_erase.mp (mem_erase.mp im).2).2).1)
    rw [sum_const,sz,smul_eq_mul] at rem
    have s2 := sum_erase_add (A.erase w) cr aw'; change (∑i∈T,cr i)+_= _ at s2
    omega
  obtain ⟨p,pa,pd⟩ := pExists
  have ex : ∃ j∈X,G.Adj c j ∧ G.Adj d j := by
    apply Classical.byContradiction; intro no
    have dj : Disjoint (row c) (row d) := disjoint_left.mpr (fun j cm dm =>
      no ⟨j,(mem_filter.mp cm).1,(mem_filter.mp cm).2,(mem_filter.mp dm).2⟩)
    have djw := disjoint_union_left.mpr ⟨sep c ca wc.symm,sep d da wd.symm⟩
    have ct := card_le_card (union_subset (union_subset (into c ca) (into d da)) (into w wa))
    rw [card_union_of_disjoint djw,card_union_of_disjoint dj] at ct
    change k c+k d+k w≤H.card at ct
    have dense (a z : V) (an : a∈G.neighborFinset f) (_az : a≠z) (eqf : G.neighborFinset f={a,z})
        (none : ∀ i∈X,G.Adj a i → ¬G.Adj z i) : 5≤k a := by
      apply Nat.le_of_not_gt; intro neg
      have aa : a∈A := Aeq ▸ mem_union_right _ an
      have aw := (apart wn an).symm
      have allow : ∀i∈X,∀u∈A,G.Adj a i → G.Adj a u → G.Adj i u → u∈({b}:Finset V) := by
        intro i ix u ua ai au iu; rw [←Aeq] at ua
        rcases mem_union.mp ua with ue|uf
        · rw [be,mem_insert,mem_singleton] at ue
          exact ue.elim (fun eq => False.elim (blind aa aw ix ai (eq ▸ iu))) (fun eq => mem_singleton.mpr eq)
        · rw [eqf,mem_insert,mem_singleton] at uf
          exact False.elim (uf.elim (fun eq => au.ne eq.symm) (fun eq => none i ix ai (eq ▸ iu.symm)))
      have cap := link_local G A {b} ac aa pa pd (low a aa) true false (by simp) allow (by simp)
      simp only [if_true,Bool.false_eq_true,if_false] at cap
      change trianglesAt G a≤1+(if a=p then 0 else 1)+(k a).choose 2+k a*nbr G a {b} at cap
      have sz : nbr G a {b}≤1 := (card_le_card (filter_subset ..)).trans_eq (card_singleton b)
      have ck := Nat.choose_le_choose 2 (show k a≤4 by omega)
      rw [show (4:ℕ).choose 2=6 by decide] at ck
      have prod := Nat.mul_le_mul (show k a≤4 by omega) sz
      have lo := must a aa aw
      split at cap <;> omega
    have lc := dense c d cn cd cf (fun i ix ci di => no ⟨i,ix,ci,di⟩)
    have ld := dense d c dn cd.symm (cf.trans (pair_comm ..)) (fun i ix di ci => no ⟨i,ix,ci,di⟩)
    omega
  obtain ⟨j,jx,cj,dj⟩ := ex
  have thick : Squares29.Opposite G f j := by
    refine ⟨df,?_,?_⟩
    · rintro rfl; have h := (mem_filter.mp (mem_sdiff.mp jx).1).2; omega
    · rw [cf]; exact insert_subset ((G.mem_neighborFinset ..).mpr cj.symm) (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr dj.symm))
  have thin {i : V} (ia : i∈A) (wi : G.Adj w i) : ¬G.Adj b i := by
    intro bi
    have op : Squares29.Opposite G e i := by
      refine ⟨de,?_,?_⟩
      · rintro rfl; have h := (mem_filter.mp (ah ia)).2; omega
      · rw [be]; exact insert_subset ((G.mem_neighborFinset ..).mpr wi.symm) (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr bi.symm))
    obtain ⟨v,vm⟩ := (Squares29.contact G (Squares29.sparse G bad) ef op thick).1
    exact disjoint_left.mp dis (mem_inter.mp vm).1 (mem_inter.mp vm).2
  obtain ⟨i,ia,l,la,wi,wl,il⟩ := triangle
  have outside {u v : V} (ua : u∈A) (va : v∈A) (wu : G.Adj w u) (wv : G.Adj w v) (uv : G.Adj u v) : u∈G.neighborFinset f := by
    rw [←Aeq] at ua
    rcases mem_union.mp ua with ue|uf
    · rw [be,mem_insert,mem_singleton] at ue
      exact False.elim (ue.elim (fun eq => wu.ne eq.symm) (fun eq => thin va wv (eq ▸ uv)))
    · exact uf
  have both : G.neighborFinset f⊆G.neighborFinset w := by
    have inc := insert_subset (outside ia la wi wl il) (singleton_subset_iff.mpr (outside la ia wl wi il.symm))
    have eq := eq_of_subset_of_card_le inc (by rw [card_neighborFinset_eq_degree,df,card_pair il.ne])
    rw [←eq]; exact insert_subset ((G.mem_neighborFinset ..).mpr wi) (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr wl))
  have noB {a : V} (an : a∈G.neighborFinset f) : ¬G.Adj b a := by
    rcases AnchorPairs.missing_cross G t q bad ef de df with ⟨u,um,no⟩|⟨u,um,no⟩
    · rw [be,mem_insert,mem_singleton] at um
      exact um.elim (fun eq => False.elim (no a an (eq ▸ (G.mem_neighborFinset ..).mp (both an)))) (fun eq => eq ▸ no a an)
    · exact False.elim (no w wn ((G.mem_neighborFinset ..).mp (both um)).symm)
  have onlyB {a : V} (aa : a∈A) (ba' : G.Adj b a) : a=w := by
    rw [←Aeq] at aa; rcases mem_union.mp aa with ae|af
    · rw [be,mem_insert,mem_singleton] at ae; exact ae.resolve_right ba'.ne.symm
    · exact False.elim (noB af ba')
  have bdeg : nbr G b A≤1 := by
    have sub : A.filter (G.Adj b)⊆{w} := fun a am => mem_singleton.mpr (onlyB (mem_filter.mp am).1 (mem_filter.mp am).2)
    exact (card_le_card sub).trans_eq (card_singleton w)
  let T := row c∩row d
  let S := row b\T
  let Y := H\row w
  have inY (a : V) (aa : a∈A) (aw : a≠w) : row a⊆Y := fun i im =>
    mem_sdiff.mpr ⟨into a aa im,fun wm => disjoint_left.mp (sep a aa aw) im wm⟩
  have yc : Y.card+k w=H.card := card_sdiff_add_card_eq_card (into w wa)
  have tc : T.card+S.card≤Y.card := by
    have sub := card_le_card (union_subset ((inter_subset_left (s₁:=row c) (s₂:=row d)).trans (inY c ca wc.symm))
      ((show S⊆row b from sdiff_subset).trans (inY b ba wb.symm)))
    rwa [card_union_of_disjoint (show Disjoint T S from disjoint_left.mpr (fun _ tm sm => (mem_sdiff.mp sm).2 tm))] at sub
  have uv := card_le_card (union_subset (inY c ca wc.symm) (inY d da wd.symm))
  have un := card_union_add_card_inter (row c) (row d)
  change _+T.card=k c+k d at un
  have budget : S.card+k c+k d≤18 := by omega
  have off {u : V} (uh : u∈high G) {z : V} (deg : G.degree z=2) : u≠z := by
    rintro rfl; have h := (mem_filter.mp uh).2; omega
  have wc' := (G.mem_neighborFinset ..).mp (both cn)
  have wd' := (G.mem_neighborFinset ..).mp (both dn)
  have cross : Disjoint ({e,c,d}:Finset V) {f,w,b} := by
    simp [disjoint_left,ef,off (ah wa) de,off (ah ba) de,off (ah ca) df,off (ah da) df,
      Ne.symm (off (ah wa) de),Ne.symm (off (ah ba) de),wc.symm,bc.symm,wd.symm,bd.symm]
  have forbidden {i j : V} (im : i∈row b) (jm : j∈T) : ¬G.Adj i j := by
    obtain ⟨ix,bi⟩ := mem_filter.mp im
    obtain ⟨cm,dm⟩ := mem_inter.mp jm
    obtain ⟨jx,cj⟩ := mem_filter.mp cm
    have ih := (mem_sdiff.mp ix).1
    have jh := (mem_sdiff.mp jx).1
    have chk {a u : V} (ua : u∈X) (am : a∈A) : u≠a := fun h => (mem_sdiff.mp ua).2 (h ▸ am)
    have freshI : i∉({f,w,b}:Finset V) := by simp [off ih df,chk ix wa,chk ix ba]
    have freshJ : j∉({e,c,d}:Finset V) := by simp [off jh de,chk jx ca,chk jx da]
    exact forbidden_edge G bad de df ef (off ih de) (chk jx ba).symm (off (ah wa) df).symm wb cd
      ((G.mem_neighborFinset ..).mp wn) ((G.mem_neighborFinset ..).mp bn)
      ((G.mem_neighborFinset ..).mp cn) ((G.mem_neighborFinset ..).mp dn) wc' wd' bi cj (mem_filter.mp dm).2
      cross freshI freshJ
  have sb : trianglesAt G b≤2+S.card.choose 2 := by
    have twos := (TwoEars.profile G t q bad).2
    have cap := Shared.score_cap G b S S.card (card_le_card (filter_subset ..)) (by
      intro u v bu bv swap uh vh
      have inner {a z : V} (ba' : G.Adj b a) (bz : G.Adj b z) (az : G.Adj a z)
          (ah' : a∈high G) (zh : z∈high G) : a∈row b := by
        apply mem_filter.mpr; refine ⟨mem_sdiff.mpr ⟨ah',?_⟩,ba'⟩
        intro aa; have eq := onlyB aa ba'
        by_cases za : z∈A
        · exact az.ne (eq.trans (onlyB za bz).symm)
        · exact blind ba wb.symm (mem_sdiff.mpr ⟨zh,za⟩) bz (eq ▸ az.symm)
      have um := inner bu bv swap uh vh
      have vm := inner bv bu swap.symm vh uh
      exact mem_sdiff.mpr ⟨um,fun ut => forbidden vm ut swap.symm⟩)
    rwa [twos] at cap
  have sf (a : V) (an : a∈G.neighborFinset f) : trianglesAt G a≤2+(k a).choose 2+k a := by
    have aa : a∈A := Aeq ▸ mem_union_right _ an
    have aw := (apart wn an).symm
    have allowed : ∀i∈high G\A,∀u∈A,G.Adj a i → G.Adj a u → G.Adj i u → u∈G.neighborFinset f := by
      intro i ix u ua ai au iu; rw [←Aeq] at ua
      rcases mem_union.mp ua with ue|uf
      · rw [be,mem_insert,mem_singleton] at ue
        exact False.elim (ue.elim (fun eq => blind aa aw ix ai (eq ▸ iu)) (fun eq => noB an (eq ▸ au.symm)))
      · exact uf
    have cap := link_local G A (G.neighborFinset f) ac aa ba bdeg (low a aa) true false (by simp) allowed (by simp)
    simp only [if_true,Bool.false_eq_true,if_false] at cap
    have inc : (G.neighborFinset f).filter (G.Adj a)⊆(G.neighborFinset f).erase a :=
      fun i im => mem_erase.mpr ⟨(mem_filter.mp im).2.ne.symm,(mem_filter.mp im).1⟩
    have y := card_le_card inc; rw [card_erase_of_mem an,card_neighborFinset_eq_degree,df] at y
    change nbr G a (G.neighborFinset f)≤1 at y
    have prod := Nat.mul_le_mul_left (k a) y
    change trianglesAt G a≤1+(if a=b then 0 else 1)+(k a).choose 2+k a*nbr G a (G.neighborFinset f) at cap
    split at cap <;> omega
  let priceB (n : ℕ) := if n≤6 then 2116296 else if n≤7 then 1293292 else 739024
  let priceF (n : ℕ) := if n≤5 then 2116296 else if n≤6 then 1293292 else 739024
  have pb : priceB S.card≤cr b := by
    unfold priceB; split_ifs with h u
    · have ck := Nat.choose_le_choose 2 h; rw [show (6:ℕ).choose 2=15 by decide] at ck
      exact (pays b ba).2.2.2.1 (by omega)
    · have ck := Nat.choose_le_choose 2 u; rw [show (7:ℕ).choose 2=21 by decide] at ck
      exact (pays b ba).2.2.2.2 (by omega)
    · exact (pays b ba).1
  have pe (a : V) (an : a∈G.neighborFinset f) : priceF (k a)≤cr a := by
    have aa : a∈A := Aeq ▸ mem_union_right _ an
    have z := sf a an
    unfold priceF; split_ifs with h u
    · have ck := Nat.choose_le_choose 2 h; rw [show (5:ℕ).choose 2=10 by decide] at ck
      exact (pays a aa).2.2.2.1 (by omega)
    · have ck := Nat.choose_le_choose 2 u; rw [show (6:ℕ).choose 2=15 by decide] at ck
      exact (pays a aa).2.2.2.2 (by omega)
    · exact (pays a aa).1
  have pc := pe c cn; have pd' := pe d dn
  have lc := lim c ca wc.symm; have ld := lim d da wd.symm
  have nn : S.card≤9 := by omega
  have bs : 6≤S.card := by
    apply Nat.le_of_not_gt; intro n
    have ck := Nat.choose_le_choose 2 (show S.card≤5 by omega)
    rw [show (5:ℕ).choose 2=10 by decide] at ck
    have high := must b ba wb.symm; omega
  have fs (a : V) (an : a∈G.neighborFinset f) : 5≤k a := by
    apply Nat.le_of_not_gt; intro n
    have ck := Nat.choose_le_choose 2 (show k a≤4 by omega)
    rw [show (4:ℕ).choose 2=6 by decide] at ck
    have bound := sf a an
    have high := must a (Aeq ▸ mem_union_right _ an) (apart wn an).symm; omega
  have tab : ∀ (i j l : Fin 10), 6 ≤ i.val → 5≤j.val → 5≤l.val → i.val+j.val+l.val≤18 →
      4364890≤priceB i+priceF j+priceF l := by unfold priceB priceF; decide
  have z := tab ⟨S.card,by omega⟩ ⟨k c,by omega⟩ ⟨k d,by omega⟩ bs (fs c cn) (fs d dn) budget
  dsimp only at z
  have ae : A={w,b,c,d} := by rw [←Aeq,be,cf]; ext u; simp only [mem_union,mem_insert,mem_singleton]; tauto
  have ae' : A.erase w={b,c,d} := by rw [ae,erase_insert]; simp [wb,wc,wd]
  rw [ae'] at sumCap
  simp only [sum_insert,mem_insert,mem_singleton,bc,bd,cd,or_self,not_false_eq_true,sum_singleton] at sumCap
  omega
end Graffiti384b.SparsePairs
#print axioms Graffiti384b.SparsePairs.ten_contacts
