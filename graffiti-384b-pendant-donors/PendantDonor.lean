import ForcedDonors
import PendantBudget
namespace Graffiti384b.Donor
open Finset SimpleGraph
open private FiniteRange.bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Keep the root of a pendant triangle and sample the other high vertices.
Its ears are a qualifying adjacent deficient pair in the resulting sample.
The raw number of retained vertices is at most n−14; the pair saves the
fifteenth omission, including for disconnected graphs. -/
theorem pendant_sample (t : (types G).card=29) (h : (high G).card=27)
    {u v w : V} (uv : u≠v) (uw : u≠w) (vw : v≠w)
    (nu : G.neighborFinset u={v,w}) (nv : G.neighborFinset v={u,w}) (wh : w∈high G)
    (regime : let X := (high G).erase w
      14≤(exposed G X).card ∨ (12≤(exposed G X).card ∧ ∀x∈X,4≤G.degree x) ∨
        (1≤(exposed G X).card ∧ ∀x∈X,5≤G.degree x)) :
    ∃s : Finset V,u∈deficient G s ∧ v∈deficient G s ∧ nbr G u s=1 ∧
      s.card+(deficient G s).card+14≤Fintype.card V ∧ gamma G≤Fintype.card V-15 := by
  classical
  let X := (high G).erase w
  have sz : X.card=26 := by rw [show X=(high G).erase w from rfl,card_erase_of_mem wh,h]
  obtain ⟨inj,rich,_,_⟩ := Repair.maximal_diversity G (by omega)
  have xh : X⊆high G := erase_subset ..
  obtain ⟨k,ks,good⟩ := sample26 G X sz (inj.mono xh) (fun x xm => rich x (xh xm))
    (fun x xm => (mem_filter.mp (xh xm)).2) regime
  let F := (insert u (insert v X))ᶜ
  let s := F∪k
  have du : G.degree u=2 := by rw [←card_neighborFinset_eq_degree,nu,card_pair vw]
  have dv : G.degree v=2 := by rw [←card_neighborFinset_eq_degree,nv,card_pair uw]
  have ux : u∉X := fun m => by have d := (mem_filter.mp (xh m)).2; omega
  have vx : v∉X := fun m => by have d := (mem_filter.mp (xh m)).2; omega
  have wx : w∉X := not_mem_erase w (high G)
  have pc : (insert u (insert v X)).card=28 := by
    rw [card_insert_of_not_mem (by simpa only [mem_insert,not_or] using And.intro uv ux),
      card_insert_of_not_mem vx,sz]
  have fc := card_compl (insert u (insert v X))
  change F.card=Fintype.card V-(insert u (insert v X)).card at fc
  have nlim := card_le_univ (insert u (insert v X))
  have sep : Disjoint F X := disjoint_left.mpr (fun x xf xx => mem_compl.mp xf
    (mem_insert_of_mem (mem_insert_of_mem xx)))
  have us : u∉s := fun m => (mem_union.mp m).elim (fun f => mem_compl.mp f (mem_insert_self ..)) (fun km => ux (ks km))
  have vs : v∉s := fun m => (mem_union.mp m).elim (fun f => mem_compl.mp f (mem_insert_of_mem (mem_insert_self ..))) (fun km => vx (ks km))
  have ws : w∈s := mem_union_left _ (mem_compl.mpr (by simp [uw.symm,vw.symm,wx]))
  have support {x y : V} (yn : y∉s) (N : G.neighborFinset x={y,w}) : nbr G x s=1 := by
    have eq : s.filter (G.Adj x)={w} := by
      ext a; simp only [mem_filter,mem_singleton]
      constructor
      · rintro ⟨as',xa⟩
        have m := (G.mem_neighborFinset ..).mpr xa
        rw [N,mem_insert,mem_singleton] at m
        exact m.resolve_left (fun eq => yn (eq ▸ as'))
      · rintro rfl
        exact ⟨ws,(G.mem_neighborFinset ..).mp (N ▸ mem_insert_of_mem (mem_singleton_self _))⟩
    simp [nbr,eq]
  have ou := support vs nu
  have ov := support us nv
  have ub : u∈deficient G s := mem_filter.mpr ⟨mem_univ _,us,by omega⟩
  have vb : v∈deficient G s := mem_filter.mpr ⟨mem_univ _,vs,by omega⟩
  have pool (x : V) (xm : x∈X) : nbr G x s=nbr G x (Xᶜ∪k) := by
    have xn {a b : V} (N : G.neighborFinset a={b,w}) (bx : b∉X) : ¬G.Adj x a := by
      intro edge
      have m := (G.mem_neighborFinset ..).mpr edge.symm
      rw [N,mem_insert,mem_singleton] at m
      exact m.elim (fun eq => bx (eq ▸ xm)) (fun eq => wx (eq ▸ xm))
    have xu := xn nu vx; have xv := xn nv ux
    unfold nbr; congr 1; ext y
    simp only [s,F,mem_filter,mem_union,mem_compl,mem_insert]
    constructor
    · rintro ⟨out,adj⟩
      exact ⟨out.imp_left (fun h m => h (Or.inr (Or.inr m))),adj⟩
    · rintro ⟨out,adj⟩
      exact ⟨out.imp_left (fun no m => m.elim (fun eq => xu (eq ▸ adj)) (fun mm => mm.elim (fun eq => xv (eq ▸ adj)) no)),adj⟩
  let B := FiniteRange.bad G X k
  have inc : deficient G s⊆insert u (insert v B) := by
    intro x xm
    obtain ⟨out,low⟩ := (mem_filter.mp xm).2
    by_cases a : x=u
    · exact mem_insert.mpr (Or.inl a)
    by_cases d : x=v
    · exact mem_insert_of_mem (mem_insert.mpr (Or.inl d))
    have xx : x∈X := Classical.byContradiction (fun nx => out (mem_union_left _ (mem_compl.mpr (by simp [a,d,nx]))))
    exact mem_insert_of_mem (mem_insert_of_mem (mem_filter.mpr ⟨mem_sdiff.mpr ⟨xx,fun km => out (mem_union_right _ km)⟩,pool x xx ▸ low⟩))
  have count := card_le_card inc
  have ca := card_insert_le u (insert v B)
  have cb := card_insert_le v B
  have sc : s.card=F.card+k.card := card_union_of_disjoint (sep.mono_right ks)
  change k.card+B.card≤12 at good
  have raw : s.card+(deficient G s).card+14≤Fintype.card V := by omega
  have edge := (G.mem_neighborFinset _ _).mp (nu ▸ mem_insert_self v {w})
  have win := pair_repair_saves G s u v edge us vs ou (by omega)
  change gamma G≤s.card+(deficient G s).card-1 at win
  exact ⟨s,ub,vb,ou,raw,by omega⟩
end Graffiti384b.Donor
#print axioms Graffiti384b.Donor.pendant_sample
