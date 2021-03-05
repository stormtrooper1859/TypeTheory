%default total


main_proof : {a, b : Nat} -> maximum a (minimum a b) = a
main_proof {a = Z} {b = Z} = Refl
main_proof {a = Z} {b = (S k)} = Refl
main_proof {a = (S k)} {b = Z} = Refl
main_proof {a = (S k)} {b = (S j)} = cong $ main_proof
