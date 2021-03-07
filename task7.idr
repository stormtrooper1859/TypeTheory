%default total


lteReflPrf : {a, b : Nat} -> a = b -> LTE a b
lteReflPrf {a} {b} prf = replace {P = \e => Nat.LTE a e} prf (lteRefl {n = a})


-- a <= b -> a ^ 2 <= b ^ 2

lteReflLeft : {a, b, c: Nat} -> a=b -> LTE a c -> LTE b c
lteReflLeft {c} prf x = replace {P = \e => LTE e c} prf x


lteReflRight : {a, b, c: Nat} -> a=b -> LTE c a -> LTE c b
lteReflRight {c} prf x = replace {P = \e => LTE c e} prf x


lteAddLeft : {a, b, c : Nat} -> LTE a b -> LTE (c + a) (c + b)
lteAddLeft {c = Z} prf = prf
lteAddLeft {c = (S k)} prf = LTESucc (lteAddLeft prf)


lteAddRight_ : {a, b, c : Nat} -> LTE a b -> LTE (a + c) (b + c)
lteAddRight_ {a} {b} {c} x = lteReflRight (plusCommutative c b) $ lteReflLeft (plusCommutative c a) $ lteAddLeft {c=c} x


lteAdd : {a, b, c, d : Nat} -> LTE a b -> LTE c d -> LTE (a + c) (b + d)
lteAdd {a} {b} {c} {d} prfAB prfCD = lteTransitive (lteAddRight_ {c=c} prfAB) (lteAddLeft {c=b}  prfCD)


lteMulLeft : {a, b, c : Nat} -> LTE a b -> LTE (c * a) (c * b)
lteMulLeft {c = Z} prf = LTEZero
lteMulLeft {c = (S k)} prf = lteAdd (prf) (lteMulLeft {c = k} prf)


lteMulRight : {a, b, c : Nat} -> LTE a b -> LTE (a * c) (b * c)
lteMulRight {a} {b} {c} x = lteReflRight (multCommutative c b) $ lteReflLeft (multCommutative c a) $ lteMulLeft {c=c} x

-- a * a <= b * a <= b * b
lteSquare : {a, b : Nat} -> LTE a b -> LTE (a * a) (b * b)
lteSquare {a} {b} prf = lteTransitive (lteMulRight {c = a} prf) (lteMulLeft {c = b} prf)


-- a <= b -> a - b = 0

lteSub : {a, b : Nat} -> LTE a b -> (minus a b) = Z
lteSub LTEZero = Refl
lteSub (LTESucc prf) = lteSub prf


-- a - b <= a + b

minus0plus0 : (a : Nat) -> (minus a 0) = (plus a 0)
minus0plus0 Z = Refl
minus0plus0 (S k) = rewrite plusZeroRightNeutral k in Refl


lteMinus0plus0 : (a : Nat) -> LTE (minus a 0) (plus a 0)
lteMinus0plus0 a = lteReflPrf $ minus0plus0 a


ltePrevious : {a : Nat} -> LTE (pred a) a
ltePrevious {a = Z} = LTEZero
ltePrevious {a = (S k)} = lteSuccRight $ lteRefl {n = k}


lteMinusSuccRight : (a : Nat) -> (k : Nat) -> LTE (minus a (S k)) (minus a k)
lteMinusSuccRight a k = lteTransitive (lteReflPrf $ minusSuccPred a k) ltePrevious


ltePlusSuccRight : (a : Nat) -> (k : Nat) -> LTE (a + k) (plus a (S k))
ltePlusSuccRight a k = lteTransitive (lteSuccRight $ lteRefl {n = (a + k)}) (lteReflPrf $ plusSuccRightSucc a k)


lteMinusPlus : {a, b : Nat} -> LTE (minus a b) (a + b)
lteMinusPlus {a} {b = Z} = lteMinus0plus0 a
lteMinusPlus {a} {b = (S k)} = lteTransitive (lteTransitive (lteMinusSuccRight a k) (lteMinusPlus {a=a} {b=k})) (ltePlusSuccRight a k)


-- (a - b) ^ 2 - (a + b) ^ 2 = 0

main_proof : {a, b : Nat} -> (minus ((minus a b) * (minus a b)) ((a + b) * (a + b))) = 0
main_proof = lteSub $ lteSquare $ lteMinusPlus
