import Ports180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Outside the closed neighborhood, in particular including any
distinct tip nonadjacent to the center. -/
noncomputable def outer (a : V) (N : Finset V) : Finset V := univ\insert a N

private theorem partition_loss (a : V) (N F H : Finset V) (an : a∉N)
    (fo : F⊆outer a N) (hn : H⊆N) :
    Fintype.card V-(insert a ((outer a N\F)∪H)).card=F.card+(N\H).card := by
  classical
  let Z := insert a ((outer a N\F)∪H)
  have parts : univ\Z=F∪(N\H) := by
    ext x
    have out : x∈outer a N ↔ x≠a ∧ x∉N := by simp [outer]
    have no := fun (h : x∈F) => out.mp (fo h)
    have sub := fun (h : x∈H) => hn h
    have nd : x=a → x∉N := fun e => e ▸ an
    simp only [Z,mem_sdiff,mem_univ,true_and,mem_insert,mem_union,out]
    tauto
  have sep : Disjoint F (N\H) := disjoint_left.mpr fun _ xf xn =>
    (mem_sdiff.mp (fo xf)).2 (mem_insert_of_mem (mem_sdiff.mp xn).1)
  have sum := card_sdiff_add_card_eq_card (subset_univ Z)
  rw [parts,card_union_of_disjoint sep,card_univ] at sum
  change Fintype.card V-Z.card=_
  omega

/-- Exact protected budget at a retained center. For a fixed outside
deletion F, only two-neighbor component conflicts need testing. -/
theorem protected_ports_iff (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (a : V)
    (ak : a∈A∩insert r (parity G r p)) (N : Finset V) (nb : ∀ x,x∈N ↔ G.Adj a x) :
    Protected G r p A ↔ ∃ F H : Finset V,F⊆outer a N ∧ Disjoint F (A∩insert r (parity G r p)) ∧
      H⊆N ∧ F.card+(N\H).card≤allowance G r p A ∧ ∃ c : V→Bool,ProperOn G (outer a N\F) c ∧
        ∀ u∈H,∀ v∈H,PortsFit G (outer a N\F) {u,v} c := by
  classical
  let K := A∩insert r (parity G r p)
  have an : a∉N := fun m => G.loopless a ((nb a).mp m)
  have kn : Disjoint K N := disjoint_left.mpr (fun x xk xn =>
    ai a (mem_inter.mp ak).1 x (mem_inter.mp xk).1 ((nb x).mp xn).ne ((nb x).mp xn))
  have no (F : Finset V) (x : V) (xm : x∈outer a N\F) : ¬G.Adj a x :=
    fun ed => (mem_sdiff.mp (mem_sdiff.mp xm).1).2 (mem_insert_of_mem ((nb x).mpr ed))
  rw [protected_iff G gc hn r p A ai]
  constructor
  · rintro ⟨Z,bi,keep,budget⟩
    let F := outer a N\Z
    let H := N∩Z
    have az := keep ak
    have fo : F⊆outer a N := sdiff_subset
    have hsub : H⊆N := inter_subset_left
    have recov : insert a ((outer a N\F)∪H)=Z := by
      ext x
      have o : x∈outer a N ↔ x≠a ∧ x∉N := by simp [outer]
      have ax : x=a → x∈Z := fun e => e ▸ az
      simp only [F,H,mem_insert,mem_union,mem_sdiff,mem_inter,o]
      tauto
    have charge := partition_loss a N F H an fo hsub
    rw [recov] at charge
    obtain ⟨c,good⟩ := (color_function ..).mp bi
    have sub : outer a N\F⊆Z := fun x xm => recov ▸ mem_insert_of_mem (mem_union_left _ xm)
    have cp : ProperOn G (outer a N\F) c := fun x xm y ym => good x (sub xm) y (sub ym)
    refine ⟨F,H,fo,disjoint_left.mpr (fun _ xf xk => (mem_sdiff.mp xf).2 (keep xk)),
      hsub,charge ▸ budget,c,cp,(ports_pairwise ..).mp ?_⟩
    exact (ports_iff G a _ H c (no F) (fun x xm => (nb x).mp (hsub xm)) cp).mp (recov.symm ▸ bi)
  · rintro ⟨F,H,fo,dis,hsub,bound,c,good,fit⟩
    let Z := insert a ((outer a N\F)∪H)
    refine ⟨Z,(ports_iff G a _ H c (no F) (fun x xm => (nb x).mp (hsub xm)) good).mpr
      ((ports_pairwise ..).mpr fit),?_,?_⟩
    · intro x xk
      by_cases eq : x=a
      · exact eq ▸ mem_insert_self ..
      have sep := disjoint_left.mp kn xk
      have xo : x∈outer a N := by simp [outer,eq,sep]
      exact mem_insert_of_mem (mem_union_left _ (mem_sdiff.mpr ⟨xo,fun xf => disjoint_left.mp dis xf xk⟩))
    · exact (partition_loss a N F H an fo hsub).trans_le bound

#print axioms protected_ports_iff
end Minimal180.PairRepair
