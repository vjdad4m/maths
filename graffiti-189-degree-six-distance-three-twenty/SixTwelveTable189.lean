import SixTwelveClassify189
import TwelveProfile00
import TwelveProfile01
import TwelveProfile02
import TwelveProfile03
import TwelveProfile04
import TwelveProfile05
import TwelveProfile06
import TwelveProfile07
import TwelveProfile08
import TwelveProfile09
import TwelveProfile10
import TwelveProfile11
import TwelveProfile12
import TwelveProfile13
import TwelveProfile14
import TwelveProfile15
import TwelveProfile16
import TwelveProfile17
import TwelveProfile18
import TwelveProfile19
import TwelveProfile20
import TwelveProfile21
import TwelveProfile22
import TwelveProfile23
import TwelveProfile24
import TwelveProfile25
import TwelveProfile26
import TwelveProfile27
import TwelveProfile28
import TwelveProfile29
import TwelveProfile30
import TwelveProfile31
import TwelveProfile32
import TwelveProfile33
import TwelveProfile34
import TwelveProfile35
import TwelveProfile36
import TwelveProfile37
import TwelveProfile38
import TwelveProfile39
import TwelveProfile40
import TwelveProfile41
import TwelveProfile42
import TwelveProfile43
import TwelveProfile44
import TwelveProfile45
import TwelveProfile46
import TwelveProfile47
import TwelveProfile48
import TwelveProfile49
import TwelveProfile50
import TwelveProfile51
import TwelveProfile52

namespace Graffiti189LongestPath.SixTwelveSat
open SimpleGraph Finset
set_option maxHeartbeats 40000000
set_option maxRecDepth 30000

def profileAt (i : Fin 53) : Profile :=
  (#[
    TwelveProfile00.profile,
    TwelveProfile01.profile,
    TwelveProfile02.profile,
    TwelveProfile03.profile,
    TwelveProfile04.profile,
    TwelveProfile05.profile,
    TwelveProfile06.profile,
    TwelveProfile07.profile,
    TwelveProfile08.profile,
    TwelveProfile09.profile,
    TwelveProfile10.profile,
    TwelveProfile11.profile,
    TwelveProfile12.profile,
    TwelveProfile13.profile,
    TwelveProfile14.profile,
    TwelveProfile15.profile,
    TwelveProfile16.profile,
    TwelveProfile17.profile,
    TwelveProfile18.profile,
    TwelveProfile19.profile,
    TwelveProfile20.profile,
    TwelveProfile21.profile,
    TwelveProfile22.profile,
    TwelveProfile23.profile,
    TwelveProfile24.profile,
    TwelveProfile25.profile,
    TwelveProfile26.profile,
    TwelveProfile27.profile,
    TwelveProfile28.profile,
    TwelveProfile29.profile,
    TwelveProfile30.profile,
    TwelveProfile31.profile,
    TwelveProfile32.profile,
    TwelveProfile33.profile,
    TwelveProfile34.profile,
    TwelveProfile35.profile,
    TwelveProfile36.profile,
    TwelveProfile37.profile,
    TwelveProfile38.profile,
    TwelveProfile39.profile,
    TwelveProfile40.profile,
    TwelveProfile41.profile,
    TwelveProfile42.profile,
    TwelveProfile43.profile,
    TwelveProfile44.profile,
    TwelveProfile45.profile,
    TwelveProfile46.profile,
    TwelveProfile47.profile,
    TwelveProfile48.profile,
    TwelveProfile49.profile,
    TwelveProfile50.profile,
    TwelveProfile51.profile,
    TwelveProfile52.profile
  ] : Array Profile).getD i.val TwelveProfile00.profile

def fiberCard (P : Profile) (i : Fin 8) : ℕ :=
  ((univ : Finset V).filter (fun j=>P.role j=i)).card

def lowCode (P : Profile) : ℕ := match P.low with
  | none=>0
  | some j=>(P.role j).val+1

def profileShape (P : Profile) : List ℕ :=
  [P.p,P.q,fiberCard P 0,fiberCard P 1,fiberCard P 2,fiberCard P 3,
    fiberCard P 4,fiberCard P 5,fiberCard P 6,lowCode P]

theorem profile_matches : ∀ i : Fin 53, profileShape (profileAt i)=shapeData[i.val]! := by intro i; fin_cases i <;> decide

theorem profile_not_hidden : ∀ (i : Fin 53) (j : V),((profileAt i).role j).val<7 := by intro i; fin_cases i <;> decide

theorem each_profile_impossible (i : Fin 53) {H : SimpleGraph V} [DecidableRel H.Adj]
    {Near : V→V→Prop} (M : Model (profileAt i) H Near) : False := by
  fin_cases i
  · exact TwelveProfile00.impossible M
  · exact TwelveProfile01.impossible M
  · exact TwelveProfile02.impossible M
  · exact TwelveProfile03.impossible M
  · exact TwelveProfile04.impossible M
  · exact TwelveProfile05.impossible M
  · exact TwelveProfile06.impossible M
  · exact TwelveProfile07.impossible M
  · exact TwelveProfile08.impossible M
  · exact TwelveProfile09.impossible M
  · exact TwelveProfile10.impossible M
  · exact TwelveProfile11.impossible M
  · exact TwelveProfile12.impossible M
  · exact TwelveProfile13.impossible M
  · exact TwelveProfile14.impossible M
  · exact TwelveProfile15.impossible M
  · exact TwelveProfile16.impossible M
  · exact TwelveProfile17.impossible M
  · exact TwelveProfile18.impossible M
  · exact TwelveProfile19.impossible M
  · exact TwelveProfile20.impossible M
  · exact TwelveProfile21.impossible M
  · exact TwelveProfile22.impossible M
  · exact TwelveProfile23.impossible M
  · exact TwelveProfile24.impossible M
  · exact TwelveProfile25.impossible M
  · exact TwelveProfile26.impossible M
  · exact TwelveProfile27.impossible M
  · exact TwelveProfile28.impossible M
  · exact TwelveProfile29.impossible M
  · exact TwelveProfile30.impossible M
  · exact TwelveProfile31.impossible M
  · exact TwelveProfile32.impossible M
  · exact TwelveProfile33.impossible M
  · exact TwelveProfile34.impossible M
  · exact TwelveProfile35.impossible M
  · exact TwelveProfile36.impossible M
  · exact TwelveProfile37.impossible M
  · exact TwelveProfile38.impossible M
  · exact TwelveProfile39.impossible M
  · exact TwelveProfile40.impossible M
  · exact TwelveProfile41.impossible M
  · exact TwelveProfile42.impossible M
  · exact TwelveProfile43.impossible M
  · exact TwelveProfile44.impossible M
  · exact TwelveProfile45.impossible M
  · exact TwelveProfile46.impossible M
  · exact TwelveProfile47.impossible M
  · exact TwelveProfile48.impossible M
  · exact TwelveProfile49.impossible M
  · exact TwelveProfile50.impossible M
  · exact TwelveProfile51.impossible M
  · exact TwelveProfile52.impossible M

#print axioms profile_matches
#print axioms each_profile_impossible
end Graffiti189LongestPath.SixTwelveSat
