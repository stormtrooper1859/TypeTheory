%default total


-- a <= b -> a ^ 2 <= b ^ 2  - доказательство как в задании 7
------------------------------------
lteReflPrf : {a, b : Nat} -> a = b -> LTE a b
lteReflPrf {a} {b} prf = replace {P = \e => Nat.LTE a e} prf (lteRefl {n = a})


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
------------------------------------

-- (1 + a) ^ 2 > a ^ 2 

gtSucc_expandBracket_rewrited : (a : Nat) -> S (plus a (mult a (S a))) = S (plus a (plus a (mult a a)))
gtSucc_expandBracket_rewrited a = rewrite multRightSuccPlus a a in Refl


gtSucc_expandBracket : (a : Nat) -> ((S a) * (S a) = 1 + (a + (a + a * a)))
gtSucc_expandBracket a = gtSucc_expandBracket_rewrited a


gtSucc_expandBracket_commutative : (a : Nat) -> 1 + (a + (a + a * a)) = 1 + a + a + a * a
gtSucc_expandBracket_commutative a = cong {f = S} (plusAssociative a a (a * a))


gtReflLeft : {a, b, c: Nat} -> a=b -> GT a c -> GT b c
gtReflLeft {c} prf x = replace {P = \e => Nat.GT e c} prf x


gtReflRight : {a, b, c: Nat} -> a=b -> GT c a -> GT c b
gtReflRight {c} prf x = replace {P = \e => Nat.GT c e} prf x


gtAddLeft : {a, b, c : Nat} -> GT a b -> GT (c + a) (c + b)
gtAddLeft {c = Z} x = x
gtAddLeft {c = (S k)} x = LTESucc (gtAddLeft x)


gtAddRight : {a, b, c : Nat} -> GT a b -> GT (a + c) (b + c)
gtAddRight {a} {b} {c} x = gtReflRight (plusCommutative c b) $ gtReflLeft (plusCommutative c a) $ gtAddLeft x


gtSucc_addLeft_addNotZero : {a : Nat} -> GT (1 + a + a) 0
gtSucc_addLeft_addNotZero = LTESucc LTEZero


gtSucc_addLeft : (a : Nat) -> GT (1 + a + a + a * a) (a * a)
gtSucc_addLeft a = gtAddRight {c = a * a} $ gtSucc_addLeft_addNotZero {a=a}


-- (1 + a + a) + a * a > a * a
-- 1 + (a + (a + (a * a))) > a * a
-- (1 + a) * (1 + a) > a * a

gtSuccSquare : (a : Nat) -> (GT ((S a) * (S a)) (a * a))
gtSuccSquare a = gtReflLeft (sym (trans (gtSucc_expandBracket a) (gtSucc_expandBracket_commutative a))) (gtSucc_addLeft a)


-- a > b && b >= c  ->  a > c
gtgteTransitive : (a `GT` b) -> (b `GTE` c) -> (a `GT` c)
gtgteTransitive (LTESucc x) LTEZero = LTESucc LTEZero
gtgteTransitive (LTESucc x) (LTESucc y) = LTESucc (gtgteTransitive x y)


-- a > b  ->  (a - 1) >= b  ->  (a - 1) ^ 2 >= b ^ 2  ->  a ^ 2 > b ^ 2
main_proof : (a : Nat) -> (b: Nat) -> (GT a b) -> (GT (a * a) (b * b))
main_proof (S a) b (LTESucc x) = gtgteTransitive (gtSuccSquare a) (lteSquare x)
