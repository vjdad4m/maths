import ReservedRanks
import AnchorScores
namespace Graffiti384b.Reserved16
open Finset SimpleGraph Simplicial16
open private Joint17.transpose from JointEarRank
open private FiniteRange.bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In the independent-ear branch thirteen or more contacts suffice for
the catalogue inequality. No assumption on the leaf attachment or the
degrees of the fixed neighbors is required. -/
theorem exact_of_thirteen (n : Fintype.card V=33) (q : (nonleaves G).card=32) (t : (types G).card=31)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : a≠b)
    (thin : G.neighborFinset a∩G.neighborFinset b={e})
    (ind : ∀ u v,G.degree u=2 → G.degree v=2 → ¬G.Adj u v)
    (contacts : 13≤(((insert e ({a,b}:Finset V))ᶜ).filter (fun v => 0<nbr G v {a,b})).card) :
    gamma G≤bound G := by
  classical
  by_contra! bad
  let A : Finset V := {a,b}
  let W := (insert e A)ᶜ
  let X := high G\A
  let E := LowSample.twos G
  let F := E.erase e
  let Z := W\(X∪F)
  let hit := fun v => 0<nbr G v A
  let bn := fun v => (27-nbr G v X).choose (10-nbr G v X)
  have ah : A⊆high G := high_anchors G n q t ear ab thin W rfl bad ind contacts
  have hh : (W.filter hit).card=13 := by
    change 13≤(W.filter hit).card at contacts
    have no : ¬14≤(W.filter hit).card := fun h => (not_lt_of_ge (exact_of_fourteen G n q t ear ab thin ind h)) bad
    omega
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  have de : G.degree e=2 := by rw [←card_neighborFinset_eq_degree,ear,card_pair ab]
  have ws : W.card=30 := by dsimp [W,A]; rw [card_compl,card_insert_of_not_mem (by simp [ea.ne,eb.ne]),card_pair ab,n]
  obtain ⟨hs,es⟩ := Cover31.residual G t q bad
  have xs : X.card=27 := by dsimp [X]; rw [card_sdiff ah,hs,show A.card=2 from card_pair ab]
  have mE {v : V} (d : G.degree v=2) : v∈E := mem_sdiff.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  have two (v : V) (m : v∈E) : G.degree v=2 := by
    obtain ⟨nl,nh⟩ := mem_sdiff.mp m
    have lower := (mem_filter.mp nl).2
    have upper := Nat.le_of_not_gt (fun h : 2<G.degree v => nh (mem_filter.mpr ⟨mem_univ _,h⟩))
    omega
  have fs : F.card=2 := by dsimp [F,E]; rw [card_erase_of_mem (mE de),es]
  have xe : Disjoint X E := disjoint_left.mpr (fun _ m z => (mem_sdiff.mp z).2 (mem_sdiff.mp m).1)
  have xf := xe.mono_right (show F⊆E from erase_subset ..)
  have ax : Disjoint A X := disjoint_left.mpr (fun _ m x => (mem_sdiff.mp x).2 m)
  have af : Disjoint A F := disjoint_left.mpr (fun _ m f => (mem_sdiff.mp (mem_erase.mp f).2).2 (ah m))
  have xw : X⊆W := by
    intro v vm; apply mem_compl.mpr; intro m
    rcases mem_insert.mp m with rfl|va
    · exact disjoint_left.mp xe vm (mE de)
    · exact (mem_sdiff.mp vm).2 va
  have fw : F⊆W := by
    intro v vm; apply mem_compl.mpr; intro m
    exact (mem_insert.mp m).elim (mem_erase.mp vm).1 (fun va => disjoint_left.mp af va vm)
  have both : X∪F⊆W := union_subset xw fw
  have zs : Z.card=1 := by dsimp [Z]; rw [card_sdiff both,card_union_of_disjoint xf,ws,xs,fs]
  obtain ⟨all,zwit⟩ := all_pools G n q t ear ab thin W rfl bad ind contacts X Subset.rfl xs
  have other (v : V) (dv : G.degree v=2) (ve : v≠e) : G.neighborFinset v⊆X := all v (mem_erase.mpr ⟨ve,mE dv⟩)
  have ca (v : V) (vm : v∈X) : nbr G v A≤1 := (PortRepair29.thin_degrees G ear thin v (xw vm)).1
  have fzero (i : V) (m : i∈F) : nbr G i A=0 := card_eq_zero.mpr (eq_empty_of_forall_not_mem (by
    intro y ym
    obtain ⟨ya,iy⟩ := mem_filter.mp ym
    exact disjoint_left.mp ax ya (all i m ((G.mem_neighborFinset ..).mpr iy))))
  have fx (v : V) (vm : v∈F) : nbr G v X=2 := by
    have eq : X.filter (G.Adj v)=G.neighborFinset v := by
      ext y; simp only [mem_filter,mem_neighborFinset]; exact ⟨And.right,fun vy => ⟨all v vm ((G.mem_neighborFinset ..).mpr vy),vy⟩⟩
    rw [nbr,eq,card_neighborFinset_eq_degree,two v (mem_erase.mp vm).2]
  have fsum : (∑ v∈F,nbr G v X)=4 := by
    calc _ = ∑ _v∈F,2 := sum_congr rfl fx
         _ = 4 := by simp [fs]
  have pos : (Z.filter hit).card=1 := by
    obtain ⟨i,im,ih⟩ := zwit
    have lower := card_pos.mpr (show (Z.filter hit).Nonempty from ⟨i,mem_filter.mpr ⟨im,ih⟩⟩)
    have upper := card_le_card (filter_subset hit Z)
    omega
  have split := sum_sdiff both (f:=fun v => if hit v then (1:ℕ) else 0)
  rw [sum_union xf] at split
  have marks (S : Finset V) : (∑ v∈S,if hit v then 1 else 0)=(S.filter hit).card := by rw [←sum_filter]; simp
  change (∑ v∈Z,if hit v then 1 else 0)+((∑ v∈X,if hit v then 1 else 0)+∑ v∈F,if hit v then 1 else 0)=∑ v∈W,if hit v then 1 else 0 at split
  have none : F.filter hit=∅ := eq_empty_of_forall_not_mem (by intro i m; have v := (mem_filter.mp m).2; change 0<nbr G i A at v; rw [fzero i (mem_filter.mp m).1] at v; omega)
  rw [marks Z,marks F,marks W,none,card_empty,pos,hh] at split
  have mask : (∑ v∈X,nbr G v A)=12 := by
    have rows (v : V) (m : v∈X) : nbr G v A=(if hit v then 1 else 0) := by have := ca v m; dsimp [hit]; split <;> omega
    rw [sum_congr rfl rows]; omega
  have pairs := Joint17.transpose G X A
  rw [mask,show (∑ v∈A,nbr G v X)=nbr G a X+nbr G b X by simp [A,ab]] at pairs
  have limits := score_alternatives G ear thin X rfl other (by omega)
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by omega)
  have av : a∈A := mem_insert_self ..
  have bv : b∈A := mem_insert_of_mem (mem_singleton_self _)
  have xh : X⊆high G := sdiff_subset
  have injX := inj.mono (show (X:Set V)⊆high G from xh)
  have exclude (v : V) (vm : v∈X) : trianglesAt G v≠trianglesAt G a ∧ trianglesAt G v≠trianglesAt G b :=
    ⟨fun eq => disjoint_left.mp ax av (inj (xh vm) (ah av) eq ▸ vm),
     fun eq => disjoint_left.mp ax bv (inj (xh vm) (ah bv) eq ▸ vm)⟩
  have rank := reserved_rank G X A F xs (disjoint_union_left.mpr ⟨ax,xf.symm⟩) xh af ca fs injX (fun v m => floor v (xh m))
    _ _ (floor a (ah av)) (floor b (ah bv)) (fun eq => ab (inj (ah av) (ah bv) eq)) exclude limits
  rw [mask,Joint17.transpose G X F,fsum] at rank
  have mass := mass_at G 9 (by decide) (by decide) X E xs xe (fun u um v vm => ind u v (two u um) (two v vm)) two xh injX n (by rw [bound,n,t] at bad; omega)
  change 2*(27:ℕ).choose 10+(∑ v∈E,bn v)+_≤_ at mass
  have zero : nbr G e X=0 := card_eq_zero.mpr (eq_empty_of_forall_not_mem (by
    intro v vm; obtain ⟨vx,ev⟩ := mem_filter.mp vm; exact disjoint_left.mp ax (show v∈({a,b}:Finset V) from ear ▸ (G.mem_neighborFinset ..).mpr ev) vx))
  have part := sum_erase_add E bn (mE de)
  change (∑ v∈F,bn v)+bn e=∑ v∈E,bn v at part
  have earBonus : bn e=8436285 := by dsimp [bn]; rw [zero,Nat.choose_eq_fast_choose]; decide
  have second : (∑ v∈F,bn v)=2*1081575 := by
    calc _ = ∑ _v∈F,1081575 := sum_congr rfl (fun v vm => by dsimp [bn]; rw [fx v vm,Nat.choose_eq_fast_choose]; decide)
         _ = _ := by simp [fs]
  rw [second,earBonus] at part
  rw [show (27:ℕ).choose 10=8436285 by rw [Nat.choose_eq_fast_choose]; decide] at mass
  simp only [show (9:ℕ)+1=10 from rfl] at mass
  omega

end Graffiti384b.Reserved16
#print axioms Graffiti384b.Reserved16.exact_of_thirteen
