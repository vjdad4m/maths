import QuarticCollisions

namespace Erdos324

theorem coefficients_1_through_256 (c : Nat) (lo : 1 ≤ c) (hi : c ≤ 256) :
    HasCollision (evenQuartic c) := by
  by_cases le128 : c ≤ 128
  ·
    by_cases le64 : c ≤ 64
    ·
      by_cases le32 : c ≤ 32
      ·
        exact coefficients_1_through_32 c lo (by omega)
      ·
        by_cases le48 : c ≤ 48
        ·
          by_cases le40 : c ≤ 40
          ·
            by_cases le36 : c ≤ 36
            ·
              by_cases le34 : c ≤ 34
              ·
                by_cases le33 : c ≤ 33
                ·
                  have eq : c = 33 := by omega
                  subst c
                  exact ⟨671,939,57,995,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 34 := by omega
                  subst c
                  exact ⟨39,43,3,49,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le35 : c ≤ 35
                ·
                  have eq : c = 35 := by omega
                  subst c
                  exact ⟨15,18,4,20,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 36 := by omega
                  subst c
                  exact ⟨26,38,4,40,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le38 : c ≤ 38
              ·
                by_cases le37 : c ≤ 37
                ·
                  have eq : c = 37 := by omega
                  subst c
                  exact ⟨18,23,6,25,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 38 := by omega
                  subst c
                  exact ⟨9,12,4,13,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le39 : c ≤ 39
                ·
                  have eq : c = 39 := by omega
                  subst c
                  exact ⟨9,32,22,30,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 40 := by omega
                  subst c
                  exact ⟨0,7,5,6,by decide,by decide,by decide,by decide⟩
          ·
            by_cases le44 : c ≤ 44
            ·
              by_cases le42 : c ≤ 42
              ·
                by_cases le41 : c ≤ 41
                ·
                  have eq : c = 41 := by omega
                  subst c
                  exact ⟨19,25,1,27,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 42 := by omega
                  subst c
                  exact ⟨235,632,32,635,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le43 : c ≤ 43
                ·
                  have eq : c = 43 := by omega
                  subst c
                  exact ⟨2,45,24,44,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 44 := by omega
                  subst c
                  exact ⟨3,41,31,37,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le46 : c ≤ 46
              ·
                by_cases le45 : c ≤ 45
                ·
                  have eq : c = 45 := by omega
                  subst c
                  exact ⟨51,81,18,84,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 46 := by omega
                  subst c
                  exact ⟨3,17,13,15,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le47 : c ≤ 47
                ·
                  have eq : c = 47 := by omega
                  subst c
                  exact ⟨2,14,11,12,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 48 := by omega
                  subst c
                  exact ⟨44,60,0,64,by decide,by decide,by decide,by decide⟩
        ·
          by_cases le56 : c ≤ 56
          ·
            by_cases le52 : c ≤ 52
            ·
              by_cases le50 : c ≤ 50
              ·
                by_cases le49 : c ≤ 49
                ·
                  have eq : c = 49 := by omega
                  subst c
                  exact ⟨26,49,1,50,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 50 := by omega
                  subst c
                  exact ⟨8,11,1,12,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le51 : c ≤ 51
                ·
                  have eq : c = 51 := by omega
                  subst c
                  exact ⟨1,22,16,20,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 52 := by omega
                  subst c
                  exact ⟨11,12,3,14,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le54 : c ≤ 54
              ·
                by_cases le53 : c ≤ 53
                ·
                  have eq : c = 53 := by omega
                  subst c
                  exact ⟨15,24,4,25,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 54 := by omega
                  subst c
                  exact ⟨14,41,34,35,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le55 : c ≤ 55
                ·
                  have eq : c = 55 := by omega
                  subst c
                  exact ⟨4,23,14,22,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 56 := by omega
                  subst c
                  exact ⟨34,42,10,46,by decide,by decide,by decide,by decide⟩
          ·
            by_cases le60 : c ≤ 60
            ·
              by_cases le58 : c ≤ 58
              ·
                by_cases le57 : c ≤ 57
                ·
                  have eq : c = 57 := by omega
                  subst c
                  exact ⟨37,1635,1097,1545,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 58 := by omega
                  subst c
                  exact ⟨26,49,7,50,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le59 : c ≤ 59
                ·
                  have eq : c = 59 := by omega
                  subst c
                  exact ⟨13,14,8,16,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 60 := by omega
                  subst c
                  exact ⟨36,51,3,54,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le62 : c ≤ 62
              ·
                by_cases le61 : c ≤ 61
                ·
                  have eq : c = 61 := by omega
                  subst c
                  exact ⟨9,13,0,14,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 62 := by omega
                  subst c
                  exact ⟨2,7,5,6,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le63 : c ≤ 63
                ·
                  have eq : c = 63 := by omega
                  subst c
                  exact ⟨11,16,5,17,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 64 := by omega
                  subst c
                  exact ⟨17,20,11,22,by decide,by decide,by decide,by decide⟩
    ·
      by_cases le96 : c ≤ 96
      ·
        by_cases le80 : c ≤ 80
        ·
          by_cases le72 : c ≤ 72
          ·
            by_cases le68 : c ≤ 68
            ·
              by_cases le66 : c ≤ 66
              ·
                by_cases le65 : c ≤ 65
                ·
                  have eq : c = 65 := by omega
                  subst c
                  exact ⟨1,9,6,8,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 66 := by omega
                  subst c
                  exact ⟨238,257,10,295,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le67 : c ≤ 67
                ·
                  have eq : c = 67 := by omega
                  subst c
                  exact ⟨38,45,3,50,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 68 := by omega
                  subst c
                  exact ⟨15,18,7,20,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le70 : c ≤ 70
              ·
                by_cases le69 : c ≤ 69
                ·
                  have eq : c = 69 := by omega
                  subst c
                  exact ⟨176,203,44,227,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 70 := by omega
                  subst c
                  exact ⟨14,17,2,19,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le71 : c ≤ 71
                ·
                  have eq : c = 71 := by omega
                  subst c
                  exact ⟨8,9,6,10,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 72 := by omega
                  subst c
                  exact ⟨42,48,0,54,by decide,by decide,by decide,by decide⟩
          ·
            by_cases le76 : c ≤ 76
            ·
              by_cases le74 : c ≤ 74
              ·
                by_cases le73 : c ≤ 73
                ·
                  have eq : c = 73 := by omega
                  subst c
                  exact ⟨14,44,31,41,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 74 := by omega
                  subst c
                  exact ⟨25,26,15,30,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le75 : c ≤ 75
                ·
                  have eq : c = 75 := by omega
                  subst c
                  exact ⟨3,14,9,13,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 76 := by omega
                  subst c
                  exact ⟨0,16,12,14,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le78 : c ≤ 78
              ·
                by_cases le77 : c ≤ 77
                ·
                  have eq : c = 77 := by omega
                  subst c
                  exact ⟨84,90,52,102,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 78 := by omega
                  subst c
                  exact ⟨81,106,29,114,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le79 : c ≤ 79
                ·
                  have eq : c = 79 := by omega
                  subst c
                  exact ⟨6,8,2,9,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 80 := by omega
                  subst c
                  exact ⟨7,10,0,11,by decide,by decide,by decide,by decide⟩
        ·
          by_cases le88 : c ≤ 88
          ·
            by_cases le84 : c ≤ 84
            ·
              by_cases le82 : c ≤ 82
              ·
                by_cases le81 : c ≤ 81
                ·
                  have eq : c = 81 := by omega
                  subst c
                  exact ⟨6,60,39,57,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 82 := by omega
                  subst c
                  exact ⟨10,11,2,13,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le83 : c ≤ 83
                ·
                  have eq : c = 83 := by omega
                  subst c
                  exact ⟨4,5,0,6,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 84 := by omega
                  subst c
                  exact ⟨159,196,120,209,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le86 : c ≤ 86
              ·
                by_cases le85 : c ≤ 85
                ·
                  have eq : c = 85 := by omega
                  subst c
                  exact ⟨22,40,5,41,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 86 := by omega
                  subst c
                  exact ⟨1,20,12,19,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le87 : c ≤ 87
                ·
                  have eq : c = 87 := by omega
                  subst c
                  exact ⟨43,53,35,56,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 88 := by omega
                  subst c
                  exact ⟨24,26,8,30,by decide,by decide,by decide,by decide⟩
          ·
            by_cases le92 : c ≤ 92
            ·
              by_cases le90 : c ≤ 90
              ·
                by_cases le89 : c ≤ 89
                ·
                  have eq : c = 89 := by omega
                  subst c
                  exact ⟨13,21,0,22,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 90 := by omega
                  subst c
                  exact ⟨23,32,28,29,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le91 : c ≤ 91
                ·
                  have eq : c = 91 := by omega
                  subst c
                  exact ⟨5,19,14,17,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 92 := by omega
                  subst c
                  exact ⟨18,24,2,26,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le94 : c ≤ 94
              ·
                by_cases le93 : c ≤ 93
                ·
                  have eq : c = 93 := by omega
                  subst c
                  exact ⟨109,324,48,325,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 94 := by omega
                  subst c
                  exact ⟨7,10,2,11,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le95 : c ≤ 95
                ·
                  have eq : c = 95 := by omega
                  subst c
                  exact ⟨17,22,6,24,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 96 := by omega
                  subst c
                  exact ⟨15,16,11,18,by decide,by decide,by decide,by decide⟩
      ·
        by_cases le112 : c ≤ 112
        ·
          by_cases le104 : c ≤ 104
          ·
            by_cases le100 : c ≤ 100
            ·
              by_cases le98 : c ≤ 98
              ·
                by_cases le97 : c ≤ 97
                ·
                  have eq : c = 97 := by omega
                  subst c
                  exact ⟨129,170,63,182,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 98 := by omega
                  subst c
                  exact ⟨31,34,6,39,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le99 : c ≤ 99
                ·
                  have eq : c = 99 := by omega
                  subst c
                  exact ⟨101,132,36,142,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 100 := by omega
                  subst c
                  exact ⟨15,44,33,40,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le102 : c ≤ 102
              ·
                by_cases le101 : c ≤ 101
                ·
                  have eq : c = 101 := by omega
                  subst c
                  exact ⟨11,17,4,18,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 102 := by omega
                  subst c
                  exact ⟨9,55,33,53,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le103 : c ≤ 103
                ·
                  have eq : c = 103 := by omega
                  subst c
                  exact ⟨10,26,16,25,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 104 := by omega
                  subst c
                  exact ⟨4,5,1,6,by decide,by decide,by decide,by decide⟩
          ·
            by_cases le108 : c ≤ 108
            ·
              by_cases le106 : c ≤ 106
              ·
                by_cases le105 : c ≤ 105
                ·
                  have eq : c = 105 := by omega
                  subst c
                  exact ⟨89,133,41,139,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 106 := by omega
                  subst c
                  exact ⟨16,35,28,31,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le107 : c ≤ 107
                ·
                  have eq : c = 107 := by omega
                  subst c
                  exact ⟨0,8,5,7,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 108 := by omega
                  subst c
                  exact ⟨71,81,21,91,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le110 : c ≤ 110
              ·
                by_cases le109 : c ≤ 109
                ·
                  have eq : c = 109 := by omega
                  subst c
                  exact ⟨20,67,43,64,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 110 := by omega
                  subst c
                  exact ⟨6,19,14,17,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le111 : c ≤ 111
                ·
                  have eq : c = 111 := by omega
                  subst c
                  exact ⟨13,71,34,70,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 112 := by omega
                  subst c
                  exact ⟨48,68,8,72,by decide,by decide,by decide,by decide⟩
        ·
          by_cases le120 : c ≤ 120
          ·
            by_cases le116 : c ≤ 116
            ·
              by_cases le114 : c ≤ 114
              ·
                by_cases le113 : c ≤ 113
                ·
                  have eq : c = 113 := by omega
                  subst c
                  exact ⟨40,42,9,49,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 114 := by omega
                  subst c
                  exact ⟨107,134,13,146,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le115 : c ≤ 115
                ·
                  have eq : c = 115 := by omega
                  subst c
                  exact ⟨6,28,16,27,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 116 := by omega
                  subst c
                  exact ⟨9,10,1,12,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le118 : c ≤ 118
              ·
                by_cases le117 : c ≤ 117
                ·
                  have eq : c = 117 := by omega
                  subst c
                  exact ⟨24,30,3,33,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 118 := by omega
                  subst c
                  exact ⟨2,15,9,14,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le119 : c ≤ 119
                ·
                  have eq : c = 119 := by omega
                  subst c
                  exact ⟨5,7,1,8,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 120 := by omega
                  subst c
                  exact ⟨36,67,41,66,by decide,by decide,by decide,by decide⟩
          ·
            by_cases le124 : c ≤ 124
            ·
              by_cases le122 : c ≤ 122
              ·
                by_cases le121 : c ≤ 121
                ·
                  have eq : c = 121 := by omega
                  subst c
                  exact ⟨1,17,10,16,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 122 := by omega
                  subst c
                  exact ⟨5,32,25,28,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le123 : c ≤ 123
                ·
                  have eq : c = 123 := by omega
                  subst c
                  exact ⟨4,64,46,59,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 124 := by omega
                  subst c
                  exact ⟨10,30,24,26,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le126 : c ≤ 126
              ·
                by_cases le125 : c ≤ 125
                ·
                  have eq : c = 125 := by omega
                  subst c
                  exact ⟨3,9,6,8,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 126 := by omega
                  subst c
                  exact ⟨13,43,35,37,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le127 : c ≤ 127
                ·
                  have eq : c = 127 := by omega
                  subst c
                  exact ⟨2,12,9,10,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 128 := by omega
                  subst c
                  exact ⟨9,12,6,13,by decide,by decide,by decide,by decide⟩
  ·
    by_cases le192 : c ≤ 192
    ·
      by_cases le160 : c ≤ 160
      ·
        by_cases le144 : c ≤ 144
        ·
          by_cases le136 : c ≤ 136
          ·
            by_cases le132 : c ≤ 132
            ·
              by_cases le130 : c ≤ 130
              ·
                by_cases le129 : c ≤ 129
                ·
                  have eq : c = 129 := by omega
                  subst c
                  exact ⟨81,139,105,131,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 130 := by omega
                  subst c
                  exact ⟨23,25,5,29,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le131 : c ≤ 131
                ·
                  have eq : c = 131 := by omega
                  subst c
                  exact ⟨4,8,6,7,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 132 := by omega
                  subst c
                  exact ⟨112,187,107,188,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le134 : c ≤ 134
              ·
                by_cases le133 : c ≤ 133
                ·
                  have eq : c = 133 := by omega
                  subst c
                  exact ⟨209,219,132,250,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 134 := by omega
                  subst c
                  exact ⟨1,10,6,9,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le135 : c ≤ 135
                ·
                  have eq : c = 135 := by omega
                  subst c
                  exact ⟨22,46,31,44,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 136 := by omega
                  subst c
                  exact ⟨23,26,19,28,by decide,by decide,by decide,by decide⟩
          ·
            by_cases le140 : c ≤ 140
            ·
              by_cases le138 : c ≤ 138
              ·
                by_cases le137 : c ≤ 137
                ·
                  have eq : c = 137 := by omega
                  subst c
                  exact ⟨19,90,67,82,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 138 := by omega
                  subst c
                  exact ⟨35,42,21,46,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le139 : c ≤ 139
                ·
                  have eq : c = 139 := by omega
                  subst c
                  exact ⟨7,20,16,17,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 140 := by omega
                  subst c
                  exact ⟨10,17,14,15,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le142 : c ≤ 142
              ·
                by_cases le141 : c ≤ 141
                ·
                  have eq : c = 141 := by omega
                  subst c
                  exact ⟨18,32,5,33,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 142 := by omega
                  subst c
                  exact ⟨13,22,2,23,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le143 : c ≤ 143
                ·
                  have eq : c = 143 := by omega
                  subst c
                  exact ⟨5,23,16,21,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 144 := by omega
                  subst c
                  exact ⟨36,39,6,45,by decide,by decide,by decide,by decide⟩
        ·
          by_cases le152 : c ≤ 152
          ·
            by_cases le148 : c ≤ 148
            ·
              by_cases le146 : c ≤ 146
              ·
                by_cases le145 : c ≤ 145
                ·
                  have eq : c = 145 := by omega
                  subst c
                  exact ⟨15,23,10,24,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 146 := by omega
                  subst c
                  exact ⟨3,30,22,27,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le147 : c ≤ 147
                ·
                  have eq : c = 147 := by omega
                  subst c
                  exact ⟨46,65,32,68,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 148 := by omega
                  subst c
                  exact ⟨18,31,9,32,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le150 : c ≤ 150
              ·
                by_cases le149 : c ≤ 149
                ·
                  have eq : c = 149 := by omega
                  subst c
                  exact ⟨10,33,22,31,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 150 := by omega
                  subst c
                  exact ⟨23,33,27,31,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le151 : c ≤ 151
                ·
                  have eq : c = 151 := by omega
                  subst c
                  exact ⟨32,66,6,67,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 152 := by omega
                  subst c
                  exact ⟨3,12,9,10,by decide,by decide,by decide,by decide⟩
          ·
            by_cases le156 : c ≤ 156
            ·
              by_cases le154 : c ≤ 154
              ·
                by_cases le153 : c ≤ 153
                ·
                  have eq : c = 153 := by omega
                  subst c
                  exact ⟨96,105,9,120,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 154 := by omega
                  subst c
                  exact ⟨49,104,80,95,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le155 : c ≤ 155
                ·
                  have eq : c = 155 := by omega
                  subst c
                  exact ⟨11,29,22,26,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 156 := by omega
                  subst c
                  exact ⟨5,30,22,27,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le158 : c ≤ 158
              ·
                by_cases le157 : c ≤ 157
                ·
                  have eq : c = 157 := by omega
                  subst c
                  exact ⟨3,62,30,61,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 158 := by omega
                  subst c
                  exact ⟨38,39,13,46,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le159 : c ≤ 159
                ·
                  have eq : c = 159 := by omega
                  subst c
                  exact ⟨27,40,14,42,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 160 := by omega
                  subst c
                  exact ⟨0,14,10,12,by decide,by decide,by decide,by decide⟩
      ·
        by_cases le176 : c ≤ 176
        ·
          by_cases le168 : c ≤ 168
          ·
            by_cases le164 : c ≤ 164
            ·
              by_cases le162 : c ≤ 162
              ·
                by_cases le161 : c ≤ 161
                ·
                  have eq : c = 161 := by omega
                  subst c
                  exact ⟨1,42,31,38,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 162 := by omega
                  subst c
                  exact ⟨53,68,32,73,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le163 : c ≤ 163
                ·
                  have eq : c = 163 := by omega
                  subst c
                  exact ⟨17,30,6,31,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 164 := by omega
                  subst c
                  exact ⟨8,11,5,12,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le166 : c ≤ 166
              ·
                by_cases le165 : c ≤ 165
                ·
                  have eq : c = 165 := by omega
                  subst c
                  exact ⟨86,87,18,103,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 166 := by omega
                  subst c
                  exact ⟨8,9,0,11,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le167 : c ≤ 167
                ·
                  have eq : c = 167 := by omega
                  subst c
                  exact ⟨9,15,0,16,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 168 := by omega
                  subst c
                  exact ⟨39,46,35,48,by decide,by decide,by decide,by decide⟩
          ·
            by_cases le172 : c ≤ 172
            ·
              by_cases le170 : c ≤ 170
              ·
                by_cases le169 : c ≤ 169
                ·
                  have eq : c = 169 := by omega
                  subst c
                  exact ⟨28,30,3,35,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 170 := by omega
                  subst c
                  exact ⟨11,22,18,19,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le171 : c ≤ 171
                ·
                  have eq : c = 171 := by omega
                  subst c
                  exact ⟨0,24,18,21,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 172 := by omega
                  subst c
                  exact ⟨20,37,5,38,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le174 : c ≤ 174
              ·
                by_cases le173 : c ≤ 173
                ·
                  have eq : c = 173 := by omega
                  subst c
                  exact ⟨77,84,27,96,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 174 := by omega
                  subst c
                  exact ⟨29,114,69,110,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le175 : c ≤ 175
                ·
                  have eq : c = 175 := by omega
                  subst c
                  exact ⟨2,14,8,13,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 176 := by omega
                  subst c
                  exact ⟨5,36,23,34,by decide,by decide,by decide,by decide⟩
        ·
          by_cases le184 : c ≤ 184
          ·
            by_cases le180 : c ≤ 180
            ·
              by_cases le178 : c ≤ 178
              ·
                by_cases le177 : c ≤ 177
                ·
                  have eq : c = 177 := by omega
                  subst c
                  exact ⟨142,152,113,167,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 178 := by omega
                  subst c
                  exact ⟨26,61,50,53,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le179 : c ≤ 179
                ·
                  have eq : c = 179 := by omega
                  subst c
                  exact ⟨1,18,10,17,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 180 := by omega
                  subst c
                  exact ⟨18,21,3,24,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le182 : c ≤ 182
              ·
                by_cases le181 : c ≤ 181
                ·
                  have eq : c = 181 := by omega
                  subst c
                  exact ⟨5,7,2,8,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 182 := by omega
                  subst c
                  exact ⟨14,15,3,18,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le183 : c ≤ 183
                ·
                  have eq : c = 183 := by omega
                  subst c
                  exact ⟨50,58,8,65,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 184 := by omega
                  subst c
                  exact ⟨6,19,15,16,by decide,by decide,by decide,by decide⟩
          ·
            by_cases le188 : c ≤ 188
            ·
              by_cases le186 : c ≤ 186
              ·
                by_cases le185 : c ≤ 185
                ·
                  have eq : c = 185 := by omega
                  subst c
                  exact ⟨16,18,3,21,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 186 := by omega
                  subst c
                  exact ⟨30,109,82,99,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le187 : c ≤ 187
                ·
                  have eq : c = 187 := by omega
                  subst c
                  exact ⟨3,7,5,6,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 188 := by omega
                  subst c
                  exact ⟨22,24,4,28,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le190 : c ≤ 190
              ·
                by_cases le189 : c ≤ 189
                ·
                  have eq : c = 189 := by omega
                  subst c
                  exact ⟨53,606,458,549,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 190 := by omega
                  subst c
                  exact ⟨1,19,13,17,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le191 : c ≤ 191
                ·
                  have eq : c = 191 := by omega
                  subst c
                  exact ⟨5,31,24,27,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 192 := by omega
                  subst c
                  exact ⟨88,120,0,128,by decide,by decide,by decide,by decide⟩
    ·
      by_cases le224 : c ≤ 224
      ·
        by_cases le208 : c ≤ 208
        ·
          by_cases le200 : c ≤ 200
          ·
            by_cases le196 : c ≤ 196
            ·
              by_cases le194 : c ≤ 194
              ·
                by_cases le193 : c ≤ 193
                ·
                  have eq : c = 193 := by omega
                  subst c
                  exact ⟨11,19,2,20,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 194 := by omega
                  subst c
                  exact ⟨4,17,12,15,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le195 : c ≤ 195
                ·
                  have eq : c = 195 := by omega
                  subst c
                  exact ⟨17,19,7,22,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 196 := by omega
                  subst c
                  exact ⟨13,94,74,83,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le198 : c ≤ 198
              ·
                by_cases le197 : c ≤ 197
                ·
                  have eq : c = 197 := by omega
                  subst c
                  exact ⟨37,48,13,52,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 198 := by omega
                  subst c
                  exact ⟨0,41,21,40,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le199 : c ≤ 199
                ·
                  have eq : c = 199 := by omega
                  subst c
                  exact ⟨10,12,3,14,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 200 := by omega
                  subst c
                  exact ⟨8,9,2,11,by decide,by decide,by decide,by decide⟩
          ·
            by_cases le204 : c ≤ 204
            ·
              by_cases le202 : c ≤ 202
              ·
                by_cases le201 : c ≤ 201
                ·
                  have eq : c = 201 := by omega
                  subst c
                  exact ⟨223,358,113,370,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 202 := by omega
                  subst c
                  exact ⟨16,27,9,28,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le203 : c ≤ 203
                ·
                  have eq : c = 203 := by omega
                  subst c
                  exact ⟨21,26,1,29,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 204 := by omega
                  subst c
                  exact ⟨2,44,32,40,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le206 : c ≤ 206
              ·
                by_cases le205 : c ≤ 205
                ·
                  have eq : c = 205 := by omega
                  subst c
                  exact ⟨10,16,5,17,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 206 := by omega
                  subst c
                  exact ⟨3,18,10,17,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le207 : c ≤ 207
                ·
                  have eq : c = 207 := by omega
                  subst c
                  exact ⟨3,39,27,36,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 208 := by omega
                  subst c
                  exact ⟨4,11,7,10,by decide,by decide,by decide,by decide⟩
        ·
          by_cases le216 : c ≤ 216
          ·
            by_cases le212 : c ≤ 212
            ·
              by_cases le210 : c ≤ 210
              ·
                by_cases le209 : c ≤ 209
                ·
                  have eq : c = 209 := by omega
                  subst c
                  exact ⟨5,107,82,96,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 210 := by omega
                  subst c
                  exact ⟨223,234,162,263,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le211 : c ≤ 211
                ·
                  have eq : c = 211 := by omega
                  subst c
                  exact ⟨9,10,4,12,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 212 := by omega
                  subst c
                  exact ⟨10,19,13,18,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le214 : c ≤ 214
              ·
                by_cases le213 : c ≤ 213
                ·
                  have eq : c = 213 := by omega
                  subst c
                  exact ⟨21,71,54,64,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 214 := by omega
                  subst c
                  exact ⟨4,31,20,29,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le215 : c ≤ 215
                ·
                  have eq : c = 215 := by omega
                  subst c
                  exact ⟨9,11,7,12,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 216 := by omega
                  subst c
                  exact ⟨33,38,0,43,by decide,by decide,by decide,by decide⟩
          ·
            by_cases le220 : c ≤ 220
            ·
              by_cases le218 : c ≤ 218
              ·
                by_cases le217 : c ≤ 217
                ·
                  have eq : c = 217 := by omega
                  subst c
                  exact ⟨24,35,12,37,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 218 := by omega
                  subst c
                  exact ⟨11,64,52,55,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le219 : c ≤ 219
                ·
                  have eq : c = 219 := by omega
                  subst c
                  exact ⟨3,43,33,38,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 220 := by omega
                  subst c
                  exact ⟨8,46,28,44,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le222 : c ≤ 222
              ·
                by_cases le221 : c ≤ 221
                ·
                  have eq : c = 221 := by omega
                  subst c
                  exact ⟨11,33,24,30,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 222 := by omega
                  subst c
                  exact ⟨17,18,10,21,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le223 : c ≤ 223
                ·
                  have eq : c = 223 := by omega
                  subst c
                  exact ⟨0,11,6,10,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 224 := by omega
                  subst c
                  exact ⟨6,41,21,40,by decide,by decide,by decide,by decide⟩
      ·
        by_cases le240 : c ≤ 240
        ·
          by_cases le232 : c ≤ 232
          ·
            by_cases le228 : c ≤ 228
            ·
              by_cases le226 : c ≤ 226
              ·
                by_cases le225 : c ≤ 225
                ·
                  have eq : c = 225 := by omega
                  subst c
                  exact ⟨9,96,72,87,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 226 := by omega
                  subst c
                  exact ⟨0,13,7,12,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le227 : c ≤ 227
                ·
                  have eq : c = 227 := by omega
                  subst c
                  exact ⟨12,21,4,22,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 228 := by omega
                  subst c
                  exact ⟨193,216,132,239,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le230 : c ≤ 230
              ·
                by_cases le229 : c ≤ 229
                ·
                  have eq : c = 229 := by omega
                  subst c
                  exact ⟨19,34,10,35,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 230 := by omega
                  subst c
                  exact ⟨0,9,5,8,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le231 : c ≤ 231
                ·
                  have eq : c = 231 := by omega
                  subst c
                  exact ⟨8,29,16,28,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 232 := by omega
                  subst c
                  exact ⟨3,26,17,24,by decide,by decide,by decide,by decide⟩
          ·
            by_cases le236 : c ≤ 236
            ·
              by_cases le234 : c ≤ 234
              ·
                by_cases le233 : c ≤ 233
                ·
                  have eq : c = 233 := by omega
                  subst c
                  exact ⟨14,24,7,25,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 234 := by omega
                  subst c
                  exact ⟨6,75,54,69,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le235 : c ≤ 235
                ·
                  have eq : c = 235 := by omega
                  subst c
                  exact ⟨44,52,11,58,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 236 := by omega
                  subst c
                  exact ⟨3,24,19,20,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le238 : c ≤ 238
              ·
                by_cases le237 : c ≤ 237
                ·
                  have eq : c = 237 := by omega
                  subst c
                  exact ⟨33,67,18,68,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 238 := by omega
                  subst c
                  exact ⟨9,16,0,17,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le239 : c ≤ 239
                ·
                  have eq : c = 239 := by omega
                  subst c
                  exact ⟨1,11,6,10,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 240 := by omega
                  subst c
                  exact ⟨1,44,22,43,by decide,by decide,by decide,by decide⟩
        ·
          by_cases le248 : c ≤ 248
          ·
            by_cases le244 : c ≤ 244
            ·
              by_cases le242 : c ≤ 242
              ·
                by_cases le241 : c ≤ 241
                ·
                  have eq : c = 241 := by omega
                  subst c
                  exact ⟨60,71,0,79,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 242 := by omega
                  subst c
                  exact ⟨8,39,27,36,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le243 : c ≤ 243
                ·
                  have eq : c = 243 := by omega
                  subst c
                  exact ⟨25,26,5,31,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 244 := by omega
                  subst c
                  exact ⟨0,28,18,26,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le246 : c ≤ 246
              ·
                by_cases le245 : c ≤ 245
                ·
                  have eq : c = 245 := by omega
                  subst c
                  exact ⟨4,82,37,81,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 246 := by omega
                  subst c
                  exact ⟨35,59,7,61,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le247 : c ≤ 247
                ·
                  have eq : c = 247 := by omega
                  subst c
                  exact ⟨15,17,3,20,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 248 := by omega
                  subst c
                  exact ⟨10,12,4,14,by decide,by decide,by decide,by decide⟩
          ·
            by_cases le252 : c ≤ 252
            ·
              by_cases le250 : c ≤ 250
              ·
                by_cases le249 : c ≤ 249
                ·
                  have eq : c = 249 := by omega
                  subst c
                  exact ⟨2,36,25,33,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 250 := by omega
                  subst c
                  exact ⟨11,18,6,19,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le251 : c ≤ 251
                ·
                  have eq : c = 251 := by omega
                  subst c
                  exact ⟨12,14,7,16,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 252 := by omega
                  subst c
                  exact ⟨22,32,10,34,by decide,by decide,by decide,by decide⟩
            ·
              by_cases le254 : c ≤ 254
              ·
                by_cases le253 : c ≤ 253
                ·
                  have eq : c = 253 := by omega
                  subst c
                  exact ⟨44,106,71,101,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 254 := by omega
                  subst c
                  exact ⟨17,20,4,23,by decide,by decide,by decide,by decide⟩
              ·
                by_cases le255 : c ≤ 255
                ·
                  have eq : c = 255 := by omega
                  subst c
                  exact ⟨9,13,6,14,by decide,by decide,by decide,by decide⟩
                ·
                  have eq : c = 256 := by omega
                  subst c
                  exact ⟨8,27,18,25,by decide,by decide,by decide,by decide⟩

theorem coefficients_1_through_256_times_square (c k : Nat) (lo : 1 ≤ c)
    (hi : c ≤ 256) (hk : 0 < k) : HasCollision (evenQuartic (c*k^2)) :=
  scaled_collision c k hk (coefficients_1_through_256 c lo hi)

#print axioms coefficients_1_through_256_times_square
end Erdos324
