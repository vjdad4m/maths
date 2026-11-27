import P5CliqueMixedPairKernel133

namespace Graffiti133P5CliqueArms.MixedPairCertificate
open SimpleGraph Graffiti133 Graffiti133Camby
set_option maxRecDepth 140000
set_option maxHeartbeats 20000000

def fivePairOmitModel0 : Model 17 := ⟨[(4,5),(4,6),(4,7),(4,8),(5,6),(5,7),(5,8),(5,15),(5,16),(6,7),(6,8),(6,13),(6,14),(7,8),(7,11),(7,12),(8,9),(8,10),(9,11),(9,12),(9,14),(10,11),(10,13),(10,14),(11,16),(12,15),(12,16),(13,15),(13,16),(14,15)], ![41072,2960,69792,17728,3,1541,6153,24582,98314,34,40,66,68,129,136,257,260]⟩
def fivePairOmitRows0 : List (Row 17) := [⟨0,272769036,Sum.inr ![4,0,13,7,2,16,8,3,10]⟩,
⟨536870912,0,Sum.inl ![3,8,15,14]⟩,
⟨268435456,0,Sum.inl ![2,7,13,16]⟩,
⟨33554432,0,Sum.inl ![0,6,12,15]⟩,
⟨16777216,0,Sum.inl ![1,8,16,11]⟩,
⟨75497472,172384,Sum.inr ![0,5,10,14,7,1,8,16,12]⟩,
⟨4194304,0,Sum.inl ![0,5,10,13]⟩,
⟨2097152,0,Sum.inl ![3,6,11,10]⟩,
⟨1048576,0,Sum.inl ![1,7,14,9]⟩,
⟨524288,0,Sum.inl ![2,5,9,12]⟩,
⟨134479872,68816,Sum.inr ![2,5,9,11,6,3,8,15,13]⟩,
⟨0,570466316,Sum.inr ![4,0,15,8,3,14,7,2,12]⟩,
⟨67108864,268476428,Sum.inr ![4,0,13,7,14,3,8,16,12]⟩,
⟨8519680,0,Sum.inl ![3,8,10,14]⟩,
⟨2228224,0,Sum.inl ![1,8,10,11]⟩,
⟨327680,0,Sum.inl ![1,8,9,11]⟩,
⟨196608,0,Sum.inl ![5,9,8,10]⟩,
⟨67141632,0,Sum.inl ![2,7,12,16]⟩,
⟨557056,0,Sum.inl ![1,7,12,9]⟩,
⟨0,1576979,Sum.inr ![4,1,9,5,2,12,6,3,14]⟩,
⟨98304,1581165,Sum.inr ![4,0,5,9,8,3,14,7,12]⟩,
⟨278528,0,Sum.inl ![1,7,11,9]⟩,
⟨147456,18884110,Sum.inr ![4,0,6,11,7,2,16,8,10]⟩,
⟨81920,1319021,Sum.inr ![4,0,5,9,8,3,14,7,11]⟩,
⟨49152,0,Sum.inl ![6,11,7,12]⟩,
⟨8192,0,Sum.inl ![2,7,8,16]⟩,
⟨536875008,0,Sum.inl ![0,6,14,15]⟩,
⟨8392704,0,Sum.inl ![3,6,14,10]⟩,
⟨135168,8398350,Sum.inr ![4,0,6,14,7,2,16,8,10]⟩,
⟨69632,1058318,Sum.inr ![4,0,6,14,7,2,16,8,9]⟩,
⟨36864,0,Sum.inl ![6,12,7,14]⟩,
⟨20480,0,Sum.inl ![6,11,7,14]⟩,
⟨134219776,0,Sum.inl ![0,6,13,15]⟩,
⟨34816,0,Sum.inl ![6,12,7,13]⟩,
⟨18432,0,Sum.inl ![6,11,7,13]⟩,
⟨6144,0,Sum.inl ![6,13,7,14]⟩,
⟨1024,0,Sum.inl ![0,6,8,15]⟩,
⟨512,0,Sum.inl ![0,6,7,13]⟩,
⟨268435712,0,Sum.inl ![0,5,16,13]⟩,
⟨67109120,0,Sum.inl ![2,5,16,12]⟩,
⟨131328,0,Sum.inl ![5,10,8,16]⟩,
⟨65792,0,Sum.inl ![5,9,8,16]⟩,
⟨33024,67117165,Sum.inr ![4,0,5,16,8,3,14,7,12]⟩,
⟨16640,16785517,Sum.inr ![4,0,5,16,8,3,14,7,11]⟩,
⟨134217856,0,Sum.inl ![0,5,15,13]⟩,
⟨131200,0,Sum.inl ![5,10,8,15]⟩,
⟨65664,0,Sum.inl ![5,9,8,15]⟩,
⟨384,0,Sum.inl ![5,15,8,16]⟩,
⟨64,0,Sum.inl ![0,5,8,15]⟩,
⟨32,0,Sum.inl ![0,5,7,13]⟩,
⟨16,0,Sum.inl ![2,5,6,12]⟩,
⟨8,0,Sum.inl ![0,4,8,15]⟩,
⟨4,0,Sum.inl ![0,4,7,13]⟩,
⟨2,0,Sum.inl ![1,4,6,11]⟩,
⟨1,0,Sum.inl ![1,4,5,9]⟩]
def fivePairOmitTree0 : Tree := .fork 13 (.fork 2 (.fork 3 (.fork 15 (.fork 17 (.fork 8 (.fork 12 (.fork 6 (.fork 16 (.fork 4 (.fork 11 (.fork 28 (.fork 0 (.fork 1 (.fork 5 (.fork 7 (.fork 10 (.fork 18 (.fork 19 (.fork 20 (.leaf 19) (.leaf 8)) (.leaf 9)) (.fork 19 (.fork 20 (.leaf 19) (.leaf 8)) (.leaf 9))) (.leaf 36)) (.fork 19 (.fork 20 (.leaf 19) (.leaf 8)) (.leaf 9))) (.leaf 49)) (.leaf 53)) (.leaf 54)) (.leaf 2)) (.fork 28 (.fork 0 (.fork 1 (.fork 5 (.fork 14 (.fork 19 (.fork 20 (.leaf 19) (.leaf 8)) (.leaf 9)) (.leaf 34)) (.leaf 49)) (.leaf 53)) (.leaf 54)) (.leaf 2))) (.leaf 50)) (.fork 0 (.fork 5 (.fork 14 (.fork 28 (.fork 1 (.fork 4 (.fork 7 (.fork 19 (.fork 20 (.leaf 19) (.leaf 8)) (.leaf 9)) (.leaf 46)) (.leaf 50)) (.leaf 53)) (.leaf 2)) (.fork 18 (.fork 20 (.leaf 23) (.leaf 8)) (.leaf 15))) (.leaf 49)) (.leaf 54))) (.leaf 48)) (.fork 16 (.fork 11 (.fork 6 (.fork 28 (.fork 29 (.fork 4 (.fork 5 (.fork 7 (.fork 10 (.fork 14 (.fork 22 (.leaf 0) (.leaf 6)) (.leaf 31)) (.leaf 36)) (.fork 14 (.fork 22 (.leaf 0) (.leaf 6)) (.leaf 31))) (.leaf 49)) (.leaf 50)) (.leaf 1)) (.leaf 2)) (.leaf 48)) (.leaf 35)) (.fork 14 (.fork 28 (.fork 29 (.fork 1 (.fork 5 (.fork 6 (.fork 7 (.fork 9 (.fork 10 (.fork 11 (.fork 20 (.leaf 29) (.leaf 8)) (.leaf 35)) (.leaf 36)) (.leaf 37)) (.leaf 46)) (.leaf 48)) (.leaf 49)) (.leaf 53)) (.leaf 1)) (.leaf 2)) (.leaf 31)))) (.fork 12 (.fork 16 (.fork 28 (.fork 0 (.fork 4 (.fork 6 (.fork 7 (.fork 11 (.fork 1 (.fork 5 (.fork 10 (.fork 14 (.fork 19 (.fork 20 (.leaf 19) (.leaf 8)) (.leaf 9)) (.fork 18 (.fork 19 (.fork 20 (.leaf 19) (.leaf 8)) (.leaf 9)) (.leaf 21))) (.leaf 36)) (.leaf 49)) (.leaf 53)) (.fork 14 (.fork 1 (.fork 19 (.fork 20 (.leaf 19) (.leaf 8)) (.leaf 9)) (.leaf 53)) (.leaf 34))) (.leaf 47)) (.leaf 48)) (.leaf 50)) (.leaf 54)) (.leaf 2)) (.leaf 41)) (.fork 16 (.fork 11 (.fork 28 (.fork 6 (.fork 7 (.fork 14 (.fork 29 (.fork 4 (.fork 10 (.fork 22 (.leaf 0) (.leaf 6)) (.leaf 36)) (.leaf 50)) (.leaf 1)) (.leaf 31)) (.leaf 47)) (.leaf 48)) (.leaf 2)) (.leaf 35)) (.leaf 41)))) (.fork 12 (.fork 8 (.fork 16 (.fork 1 (.fork 4 (.fork 7 (.fork 10 (.fork 11 (.fork 21 (.fork 0 (.fork 6 (.fork 9 (.fork 14 (.fork 19 (.fork 20 (.leaf 19) (.leaf 8)) (.leaf 9)) (.fork 18 (.fork 19 (.fork 20 (.leaf 19) (.leaf 8)) (.leaf 9)) (.leaf 21))) (.leaf 37)) (.leaf 48)) (.leaf 54)) (.leaf 7)) (.fork 14 (.fork 0 (.fork 19 (.fork 20 (.leaf 19) (.leaf 8)) (.leaf 9)) (.leaf 54)) (.leaf 34))) (.leaf 36)) (.leaf 45)) (.leaf 50)) (.leaf 53)) (.leaf 16)) (.leaf 40)) (.fork 16 (.fork 8 (.fork 10 (.fork 11 (.fork 1 (.fork 7 (.fork 9 (.fork 14 (.fork 23 (.leaf 28) (.leaf 13)) (.leaf 31)) (.leaf 37)) (.leaf 45)) (.leaf 53)) (.leaf 35)) (.leaf 36)) (.leaf 40)) (.leaf 16)))) (.fork 12 (.fork 8 (.fork 16 (.fork 17 (.fork 11 (.fork 4 (.fork 19 (.fork 0 (.fork 1 (.fork 6 (.fork 7 (.fork 10 (.fork 14 (.fork 20 (.leaf 19) (.leaf 8)) (.leaf 24)) (.leaf 36)) (.fork 14 (.fork 20 (.leaf 19) (.leaf 8)) (.leaf 24))) (.leaf 48)) (.leaf 53)) (.leaf 54)) (.leaf 9)) (.leaf 50)) (.leaf 33)) (.fork 11 (.fork 1 (.fork 4 (.fork 7 (.fork 10 (.fork 14 (.fork 19 (.fork 0 (.fork 6 (.fork 20 (.leaf 19) (.leaf 8)) (.leaf 48)) (.leaf 54)) (.leaf 9)) (.leaf 24)) (.leaf 36)) (.leaf 45)) (.leaf 50)) (.leaf 53)) (.leaf 33))) (.fork 17 (.fork 0 (.fork 14 (.fork 19 (.fork 20 (.fork 1 (.fork 4 (.leaf 19) (.leaf 50)) (.leaf 53)) (.leaf 8)) (.leaf 9)) (.leaf 24)) (.leaf 54)) (.leaf 16))) (.fork 16 (.fork 17 (.fork 0 (.fork 6 (.fork 11 (.fork 4 (.fork 5 (.fork 7 (.fork 14 (.fork 19 (.fork 26 (.leaf 42) (.leaf 17)) (.leaf 9)) (.leaf 24)) (.leaf 47)) (.leaf 49)) (.leaf 50)) (.leaf 33)) (.leaf 48)) (.leaf 54)) (.leaf 40)) (.leaf 41))) (.leaf 30))) (.leaf 51)) (.leaf 52)) (.leaf 25)

theorem five_pair_omit_0_forbidden {V : Type*} {G : SimpleGraph V}
    (h4 : FourCycleFree G) (h9 : NoPath G 9)
    (m : Nat) (e : Fin 17→V) (eI : Function.Injective e)
    (fit : ∀ x y,G.Adj (e x) (e y)↔edge fivePairOmitModel0 m x y=true) : False := by
  apply actual_model_forbidden (by decide) h4 h9 fivePairOmitModel0 fivePairOmitRows0 fivePairOmitTree0 _ _ m e eI fit
  · decide
  · decide

#print axioms five_pair_omit_0_forbidden
end Graffiti133P5CliqueArms.MixedPairCertificate
