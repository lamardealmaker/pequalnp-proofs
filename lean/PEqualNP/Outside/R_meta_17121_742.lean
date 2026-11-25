import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_17121_742

abbrev V := BitVec 32

def bank0 : List V :=
  [0, 2592243715, 133562380, 2844803120, 84754625, 403292932,
   102861840, 1347294240, 1617961282, 2273325568, 4160751752]

def bank1 : List V :=
  [8372227, 0, 32849932, 714129456, 26198208, 101352196,
   19074064, 340530208, 410001728, 562049537, 1040189578]

def bank2 : List V :=
  [8372227, 1292189708, 0, 1418772528, 42631364, 202359552,
   52628496, 676074528, 812654920, 1132474881, 2080376962]

def bank3 : List V :=
  [16760835, 353714188, 63750192, 0, 36339908, 70451984,
   54774784, 213652480, 146809160, 318779905, 469764258]

def Good (x1 : List V) : Prop :=
  ∀ (x3 : List V),
    x3.length ≤ 18 →
      (∀ (x5 : Fin x3.length),
        let x6 : List V := x1 ++ List.take (x5 : ℕ) x3
        (∃ x7 ∈ x6, ∃ x8 ∈ x6,
            x3.get x5 = x7 &&& x8 ∨ x3.get x5 = x7 ||| x8) ∧
          ∀ x7 ∈ x6,
            (x7 ^^^ (16383 : V)) &&& (x3.get x5 ^^^ (16383 : V)) ≠
              x7 ^^^ (16383 : V)) →
      (16383 : V) ∉ x1 ++ x3

end PEqualNP.Outside.R_meta_17121_742

open PEqualNP.Outside.R_meta_17121_742 in
/-- Split the finite lower-bound search into its four independent initial banks. -/
theorem PEqualNP.Outside.R_meta_17121_742
    (case0 : Good bank0)
    (case1 : Good bank1)
    (case2 : Good bank2)
    (case3 : Good bank3) :
    ∀ x1 ∈ [bank0, bank1, bank2, bank3], Good x1 := by
  intro x1 hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact case0
  · exact case1
  · exact case2
  · exact case3
