%default total


equalMulAssoc : {a, x, y, c : Nat} -> (a = mult x (mult y c)) -> a = mult (mult x y) c
equalMulAssoc {a} {x} {y} {c} prf = (replace {P = \w => a = w} (multAssociative x y c) prf)


main_proof : {a, b, c : Nat} -> (divAB : Nat ** a = divAB * b) -> (divBC : Nat ** b = divBC * c) -> (divAC : Nat ** a = divAC * c)
main_proof {a} {b} {c} (x ** pf) (y ** pf2) = ((x * y) ** (equalMulAssoc $ (replace {P = \w => a = x * w} pf2 pf)))
