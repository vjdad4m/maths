import SixThirteenClassify189
import ThirteenBatch00
import ThirteenBatch10
import ThirteenBatch20
import ThirteenBatch30
import ThirteenBatch40
import ThirteenBatch50
import ThirteenProfile56
import ThirteenProfile57
import ThirteenProfile58
import ThirteenProfile59

namespace Graffiti189LongestPath.SixThirteenSat
open SimpleGraph Finset
set_option maxHeartbeats 40000000
set_option maxRecDepth 30000

def profileAt (i : Fin 60) : Profile :=
  (#[
    ThirteenProfile00.profile,
    ThirteenProfile01.profile,
    ThirteenProfile02.profile,
    ThirteenProfile03.profile,
    ThirteenProfile04.profile,
    ThirteenProfile05.profile,
    ThirteenProfile06.profile,
    ThirteenProfile07.profile,
    ThirteenProfile08.profile,
    ThirteenProfile09.profile,
    ThirteenProfile10.profile,
    ThirteenProfile11.profile,
    ThirteenProfile12.profile,
    ThirteenProfile13.profile,
    ThirteenProfile14.profile,
    ThirteenProfile15.profile,
    ThirteenProfile16.profile,
    ThirteenProfile17.profile,
    ThirteenProfile18.profile,
    ThirteenProfile19.profile,
    ThirteenProfile20.profile,
    ThirteenProfile21.profile,
    ThirteenProfile22.profile,
    ThirteenProfile23.profile,
    ThirteenProfile24.profile,
    ThirteenProfile25.profile,
    ThirteenProfile26.profile,
    ThirteenProfile27.profile,
    ThirteenProfile28.profile,
    ThirteenProfile29.profile,
    ThirteenProfile30.profile,
    ThirteenProfile31.profile,
    ThirteenProfile32.profile,
    ThirteenProfile33.profile,
    ThirteenProfile34.profile,
    ThirteenProfile35.profile,
    ThirteenProfile36.profile,
    ThirteenProfile37.profile,
    ThirteenProfile38.profile,
    ThirteenProfile39.profile,
    ThirteenProfile40.profile,
    ThirteenProfile41.profile,
    ThirteenProfile42.profile,
    ThirteenProfile43.profile,
    ThirteenProfile44.profile,
    ThirteenProfile45.profile,
    ThirteenProfile46.profile,
    ThirteenProfile47.profile,
    ThirteenProfile48.profile,
    ThirteenProfile49.profile,
    ThirteenProfile50.profile,
    ThirteenProfile51.profile,
    ThirteenProfile52.profile,
    ThirteenProfile53.profile,
    ThirteenProfile54.profile,
    ThirteenProfile55.profile,
    ThirteenProfile56.profile,
    ThirteenProfile57.profile,
    ThirteenProfile58.profile,
    ThirteenProfile59.profile
  ] : Array Profile).getD i.val ThirteenProfile00.profile

def fiberCard (P : Profile) (i : Fin 8) : ℕ :=
  ((univ : Finset V).filter (fun j=>P.role j=i)).card

def lowCode (P : Profile) : ℕ := match P.low with
  | none=>0
  | some j=>(P.role j).val+1

def profileShape (P : Profile) : List ℕ :=
  [P.p,P.q,fiberCard P 0,fiberCard P 1,fiberCard P 2,fiberCard P 3,
    fiberCard P 4,fiberCard P 5,fiberCard P 6,fiberCard P 7,lowCode P]

theorem profile_matches : ∀ i : Fin 60, profileShape (profileAt i)=shapeData[i.val]! := by intro i; fin_cases i <;> decide


theorem each_profile_impossible (i : Fin 60) {H : SimpleGraph V} [DecidableRel H.Adj]
    {Near : V→V→Prop} (M : Model (profileAt i) H Near) : False := by
  fin_cases i
  · exact ThirteenProfile00.impossible M
  · exact ThirteenProfile01.impossible M
  · exact ThirteenProfile02.impossible M
  · exact ThirteenProfile03.impossible M
  · exact ThirteenProfile04.impossible M
  · exact ThirteenProfile05.impossible M
  · exact ThirteenProfile06.impossible M
  · exact ThirteenProfile07.impossible M
  · exact ThirteenProfile08.impossible M
  · exact ThirteenProfile09.impossible M
  · exact ThirteenProfile10.impossible M
  · exact ThirteenProfile11.impossible M
  · exact ThirteenProfile12.impossible M
  · exact ThirteenProfile13.impossible M
  · exact ThirteenProfile14.impossible M
  · exact ThirteenProfile15.impossible M
  · exact ThirteenProfile16.impossible M
  · exact ThirteenProfile17.impossible M
  · exact ThirteenProfile18.impossible M
  · exact ThirteenProfile19.impossible M
  · exact ThirteenProfile20.impossible M
  · exact ThirteenProfile21.impossible M
  · exact ThirteenProfile22.impossible M
  · exact ThirteenProfile23.impossible M
  · exact ThirteenProfile24.impossible M
  · exact ThirteenProfile25.impossible M
  · exact ThirteenProfile26.impossible M
  · exact ThirteenProfile27.impossible M
  · exact ThirteenProfile28.impossible M
  · exact ThirteenProfile29.impossible M
  · exact ThirteenProfile30.impossible M
  · exact ThirteenProfile31.impossible M
  · exact ThirteenProfile32.impossible M
  · exact ThirteenProfile33.impossible M
  · exact ThirteenProfile34.impossible M
  · exact ThirteenProfile35.impossible M
  · exact ThirteenProfile36.impossible M
  · exact ThirteenProfile37.impossible M
  · exact ThirteenProfile38.impossible M
  · exact ThirteenProfile39.impossible M
  · exact ThirteenProfile40.impossible M
  · exact ThirteenProfile41.impossible M
  · exact ThirteenProfile42.impossible M
  · exact ThirteenProfile43.impossible M
  · exact ThirteenProfile44.impossible M
  · exact ThirteenProfile45.impossible M
  · exact ThirteenProfile46.impossible M
  · exact ThirteenProfile47.impossible M
  · exact ThirteenProfile48.impossible M
  · exact ThirteenProfile49.impossible M
  · exact ThirteenProfile50.impossible M
  · exact ThirteenProfile51.impossible M
  · exact ThirteenProfile52.impossible M
  · exact ThirteenProfile53.impossible M
  · exact ThirteenProfile54.impossible M
  · exact ThirteenProfile55.impossible M
  · exact ThirteenProfile56.impossible M
  · exact ThirteenProfile57.impossible M
  · exact ThirteenProfile58.impossible M
  · exact ThirteenProfile59.impossible M

#print axioms profile_matches
#print axioms each_profile_impossible
end Graffiti189LongestPath.SixThirteenSat
