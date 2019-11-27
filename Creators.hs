module Creators where

import Lex
import Synt
import Data.List

doParsing = parse . alexScanTokens
showMe proof = putStrLn $ intercalate "\n" (map (\b -> (show b)) proof)

makeAxiom1 a b   = (Impl a (Impl b a))
makeAxiom2 a b c = (Impl (Impl a b) (Impl (Impl a (Impl b c)) (Impl a c)))
makeAxiom3 a b   = (Impl a (Impl b (And a b)))
makeAxiom4 a b   = (Impl (And a b) a)
makeAxiom5 a b   = (Impl (And a b) b)
makeAxiom6 a b   = (Impl a (Or a b))
makeAxiom7 a b   = (Impl b (Or a b))
makeAxiom8 a b c = (Impl (Impl a c) (Impl (Impl b c) (Impl (Or a b) c)))
makeAxiom9 a b   = (Impl (Impl a b) (Impl (Impl a (Not b)) (Not a)))
makeAxiom10  a   = (Impl (Not (Not a)) a)

reduceImpl (Impl a b) = b

proof_AtoB_NotBtoNotA expr1 expr2 =
        [(Impl expr1 expr2)]++
        [(Impl (Impl expr1 expr2) (Impl (Not expr2) (Impl expr1 expr2)))]++
        [(Impl (Not expr2) (Impl expr1 expr2))]++
        [(Impl (Not expr2) (Impl expr1 (Not expr2)))]++
        [(Impl (Impl expr1 expr2) (Impl (Impl expr1 (Not expr2)) (Not expr1)))]++
        [(Impl (Impl (Impl expr1 expr2) (Impl (Impl expr1 (Not expr2)) (Not expr1))) (Impl (Not expr2) (Impl (Impl expr1 expr2) (Impl (Impl expr1 (Not expr2)) (Not expr1)))))]++
        [(Impl (Not expr2) (Impl (Impl expr1 expr2) (Impl (Impl expr1 (Not expr2)) (Not expr1))))]++
        [(Impl (Impl (Not expr2) (Impl expr1 expr2)) (Impl (Impl (Not expr2) (Impl (Impl expr1 expr2) (Impl (Impl expr1 (Not expr2)) (Not expr1)))) (Impl (Not expr2) (Impl (Impl expr1 (Not expr2)) (Not expr1)))))]++
        [(Impl (Impl (Not expr2) (Impl (Impl expr1 expr2) (Impl (Impl expr1 (Not expr2)) (Not expr1)))) (Impl (Not expr2) (Impl (Impl expr1 (Not expr2)) (Not expr1))))]++
        [(Impl (Not expr2) (Impl (Impl expr1 (Not expr2)) (Not expr1)))]++
        [(Impl (Impl (Not expr2) (Impl expr1 (Not expr2))) (Impl (Impl (Not expr2) (Impl (Impl expr1 (Not expr2)) (Not expr1))) (Impl (Not expr2) (Not expr1))))]++
        [(Impl (Impl (Not expr2) (Impl (Impl expr1 (Not expr2)) (Not expr1))) (Impl (Not expr2) (Not expr1)))]++
        [(Impl (Not expr2) (Not expr1))]

proof_AtoA expr = 
        [(Impl expr (Impl expr expr))]++
        [(Impl expr (Impl (Impl expr expr) expr))]++
        [(Impl (Impl expr (Impl expr expr)) (Impl (Impl expr (Impl (Impl expr expr) expr)) (Impl expr expr)))]++
        [(Impl (Impl expr (Impl (Impl expr expr) expr)) (Impl expr expr))]++
        [(Impl expr expr)]

proof_A_NotNotA expr =
        [expr]++[makeAxiom1 expr (Not expr)]++[(Impl (Not expr) expr)]++(proof_AtoA (Not expr))++
        [makeAxiom9 (Not expr) expr]++[reduceImpl $ makeAxiom9 (Not expr) expr]++[(Not (Not expr))]

proof_AtoNotAtoB expr1 expr2 =
        [(Impl expr1 (Impl (Not expr1) expr1))]++
        [(Impl expr1 (Impl (Not expr2) expr1))]++
        [(Impl (Impl expr1 (Impl (Not expr2) expr1)) (Impl expr1 (Impl expr1 (Impl (Not expr2) expr1))))]++
        [(Impl expr1 (Impl expr1 (Impl (Not expr2) expr1)))]++
        [(Impl (Impl expr1 (Impl (Not expr2) expr1)) (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))))]++
        [(Impl (Impl (Impl expr1 (Impl (Not expr2) expr1)) (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1)))) (Impl expr1 (Impl (Impl expr1 (Impl (Not expr2) expr1)) (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))))))]++
        [(Impl expr1 (Impl (Impl expr1 (Impl (Not expr2) expr1)) (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1)))))]++
        [(Impl (Impl expr1 (Impl expr1 (Impl (Not expr2) expr1))) (Impl (Impl expr1 (Impl (Impl expr1 (Impl (Not expr2) expr1)) (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))))) (Impl expr1 (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))))))]++
        [(Impl (Impl expr1 (Impl (Impl expr1 (Impl (Not expr2) expr1)) (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))))) (Impl expr1 (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1)))))]++
        [(Impl expr1 (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))))]++
        [(Impl (Impl (Not expr1) expr1) (Impl (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))) (Impl (Not expr1) (Impl (Not expr2) expr1))))]++
        [(Impl (Impl (Impl (Not expr1) expr1) (Impl (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))) (Impl (Not expr1) (Impl (Not expr2) expr1)))) (Impl expr1 (Impl (Impl (Not expr1) expr1) (Impl (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))) (Impl (Not expr1) (Impl (Not expr2) expr1))))))]++
        [(Impl expr1 (Impl (Impl (Not expr1) expr1) (Impl (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))) (Impl (Not expr1) (Impl (Not expr2) expr1)))))]++
        [(Impl (Impl expr1 (Impl (Not expr1) expr1)) (Impl (Impl expr1 (Impl (Impl (Not expr1) expr1) (Impl (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))) (Impl (Not expr1) (Impl (Not expr2) expr1))))) (Impl expr1 (Impl (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))) (Impl (Not expr1) (Impl (Not expr2) expr1))))))]++
        [(Impl (Impl expr1 (Impl (Impl (Not expr1) expr1) (Impl (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))) (Impl (Not expr1) (Impl (Not expr2) expr1))))) (Impl expr1 (Impl (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))) (Impl (Not expr1) (Impl (Not expr2) expr1)))))]++
        [(Impl expr1 (Impl (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))) (Impl (Not expr1) (Impl (Not expr2) expr1))))]++
        [(Impl (Impl expr1 (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1)))) (Impl (Impl expr1 (Impl (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))) (Impl (Not expr1) (Impl (Not expr2) expr1)))) (Impl expr1 (Impl (Not expr1) (Impl (Not expr2) expr1)))))]++
        [(Impl (Impl expr1 (Impl (Impl (Not expr1) (Impl expr1 (Impl (Not expr2) expr1))) (Impl (Not expr1) (Impl (Not expr2) expr1)))) (Impl expr1 (Impl (Not expr1) (Impl (Not expr2) expr1))))]++
        [(Impl expr1 (Impl (Not expr1) (Impl (Not expr2) expr1)))]++
        [(Impl (Not expr1) (Impl (Not expr2) (Not expr1)))]++
        [(Impl (Impl (Not expr1) (Impl (Not expr2) (Not expr1))) (Impl expr1 (Impl (Not expr1) (Impl (Not expr2) (Not expr1)))))]++
        [(Impl expr1 (Impl (Not expr1) (Impl (Not expr2) (Not expr1))))]++
        [(Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))]++
        [(Impl (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl expr1 (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))))]++
        [(Impl expr1 (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))))]++
        [(Impl (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))))]++
        [(Impl (Impl (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))))) (Impl expr1 (Impl (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))))))]++
        [(Impl expr1 (Impl (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))))))]++
        [(Impl (Impl expr1 (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))) (Impl (Impl expr1 (Impl (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))))) (Impl expr1 (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))))))]++
        [(Impl (Impl expr1 (Impl (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))))) (Impl expr1 (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))))))]++
        [(Impl expr1 (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))))]++
        [(Impl (Impl (Not expr1) (Impl (Not expr2) expr1)) (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))) (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))))]++
        [(Impl (Impl (Impl (Not expr1) (Impl (Not expr2) expr1)) (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))) (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))))) (Impl expr1 (Impl (Impl (Not expr1) (Impl (Not expr2) expr1)) (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))) (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))))))]++
        [(Impl expr1 (Impl (Impl (Not expr1) (Impl (Not expr2) expr1)) (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))) (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))))))]++
        [(Impl (Impl expr1 (Impl (Not expr1) (Impl (Not expr2) expr1))) (Impl (Impl expr1 (Impl (Impl (Not expr1) (Impl (Not expr2) expr1)) (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))) (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))))) (Impl expr1 (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))) (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))))))]++
        [(Impl (Impl expr1 (Impl (Impl (Not expr1) (Impl (Not expr2) expr1)) (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))) (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))))) (Impl expr1 (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))) (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))))))]++
        [(Impl expr1 (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))) (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))))]++
        [(Impl (Impl expr1 (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))))) (Impl (Impl expr1 (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))) (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))))) (Impl expr1 (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))))))]++
        [(Impl (Impl expr1 (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))) (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))))) (Impl expr1 (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))))]++
        [(Impl expr1 (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))))]++
        [(Impl (Impl (Not expr1) (Impl (Not expr2) (Not expr1))) (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Not (Not expr2)))))]++
        [(Impl (Impl (Impl (Not expr1) (Impl (Not expr2) (Not expr1))) (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Not (Not expr2))))) (Impl expr1 (Impl (Impl (Not expr1) (Impl (Not expr2) (Not expr1))) (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Not (Not expr2)))))))]++
        [(Impl expr1 (Impl (Impl (Not expr1) (Impl (Not expr2) (Not expr1))) (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Not (Not expr2))))))]++
        [(Impl (Impl expr1 (Impl (Not expr1) (Impl (Not expr2) (Not expr1)))) (Impl (Impl expr1 (Impl (Impl (Not expr1) (Impl (Not expr2) (Not expr1))) (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Not (Not expr2)))))) (Impl expr1 (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Not (Not expr2)))))))]++
        [(Impl (Impl expr1 (Impl (Impl (Not expr1) (Impl (Not expr2) (Not expr1))) (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Not (Not expr2)))))) (Impl expr1 (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Not (Not expr2))))))]++
        [(Impl expr1 (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Not (Not expr2)))))]++
        [(Impl (Impl expr1 (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2))))) (Impl (Impl expr1 (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Not (Not expr2))))) (Impl expr1 (Impl (Not expr1) (Not (Not expr2))))))]++
        [(Impl (Impl expr1 (Impl (Impl (Not expr1) (Impl (Impl (Not expr2) (Not expr1)) (Not (Not expr2)))) (Impl (Not expr1) (Not (Not expr2))))) (Impl expr1 (Impl (Not expr1) (Not (Not expr2)))))]++
        [(Impl expr1 (Impl (Not expr1) (Not (Not expr2))))]++
        [(Impl (Not (Not expr2)) expr2)]++
        [(Impl (Impl (Not (Not expr2)) expr2) (Impl expr1 (Impl (Not (Not expr2)) expr2)))]++
        [(Impl expr1 (Impl (Not (Not expr2)) expr2))]++
        [(Impl (Impl (Not (Not expr2)) expr2) (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)))]++
        [(Impl (Impl (Impl (Not (Not expr2)) expr2) (Impl (Not expr1) (Impl (Not (Not expr2)) expr2))) (Impl expr1 (Impl (Impl (Not (Not expr2)) expr2) (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)))))]++
        [(Impl expr1 (Impl (Impl (Not (Not expr2)) expr2) (Impl (Not expr1) (Impl (Not (Not expr2)) expr2))))]++
        [(Impl (Impl expr1 (Impl (Not (Not expr2)) expr2)) (Impl (Impl expr1 (Impl (Impl (Not (Not expr2)) expr2) (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)))) (Impl expr1 (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)))))]++
        [(Impl (Impl expr1 (Impl (Impl (Not (Not expr2)) expr2) (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)))) (Impl expr1 (Impl (Not expr1) (Impl (Not (Not expr2)) expr2))))]++
        [(Impl expr1 (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)))]++
        [(Impl (Impl (Not expr1) (Not (Not expr2))) (Impl (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)) (Impl (Not expr1) expr2)))]++
        [(Impl (Impl (Impl (Not expr1) (Not (Not expr2))) (Impl (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)) (Impl (Not expr1) expr2))) (Impl expr1 (Impl (Impl (Not expr1) (Not (Not expr2))) (Impl (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)) (Impl (Not expr1) expr2)))))]++
        [(Impl expr1 (Impl (Impl (Not expr1) (Not (Not expr2))) (Impl (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)) (Impl (Not expr1) expr2))))]++
        [(Impl (Impl expr1 (Impl (Not expr1) (Not (Not expr2)))) (Impl (Impl expr1 (Impl (Impl (Not expr1) (Not (Not expr2))) (Impl (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)) (Impl (Not expr1) expr2)))) (Impl expr1 (Impl (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)) (Impl (Not expr1) expr2)))))]++
        [(Impl (Impl expr1 (Impl (Impl (Not expr1) (Not (Not expr2))) (Impl (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)) (Impl (Not expr1) expr2)))) (Impl expr1 (Impl (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)) (Impl (Not expr1) expr2))))]++
        [(Impl expr1 (Impl (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)) (Impl (Not expr1) expr2)))]++
        [(Impl (Impl expr1 (Impl (Not expr1) (Impl (Not (Not expr2)) expr2))) (Impl (Impl expr1 (Impl (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)) (Impl (Not expr1) expr2))) (Impl expr1 (Impl (Not expr1) expr2))))]++
        [(Impl (Impl expr1 (Impl (Impl (Not expr1) (Impl (Not (Not expr2)) expr2)) (Impl (Not expr1) expr2))) (Impl expr1 (Impl (Not expr1) expr2)))]++
        [(Impl expr1 (Impl (Not expr1) expr2))]

proof_AorNotA expr = 
        [makeAxiom6 expr (Not expr)]++(proof_AtoB_NotBtoNotA expr (Or expr (Not expr)))++
        [makeAxiom7 expr (Not expr)]++(proof_AtoB_NotBtoNotA (Not expr) (Or expr (Not expr)))++
        [makeAxiom9 (Not (Or expr (Not expr))) (Not expr)]++[reduceImpl $ makeAxiom9 (Not (Or expr (Not expr))) (Not expr)]++
        [(Not (Not (Or expr (Not expr))))]++[makeAxiom10 (Or expr (Not expr))]++
        [(Or expr (Not expr))]

proof_11_AandB expr1 expr2 =
        [expr1]++[expr2]++[makeAxiom3 expr1 expr2]++[reduceImpl $ makeAxiom3 expr1 expr2]++[(And expr1 expr2)]

proof_01_Not_AandB expr1 expr2 = 
        [makeAxiom4 expr1 expr2]++[(Not expr1)]++
        [makeAxiom1 (Not expr1) (And expr1 expr2)]++[reduceImpl $ makeAxiom1 (Not expr1) (And expr1 expr2)]++
        [makeAxiom9 (And expr1 expr2) expr1]++[reduceImpl $ makeAxiom9 (And expr1 expr2) expr1]++
        [(Not (And expr1 expr2))]

proof_10_Not_AandB expr1 expr2 = 
        [makeAxiom5 expr1 expr2]++[(Not expr2)]++
        [makeAxiom1 (Not expr2) (And expr1 expr2)]++[reduceImpl $ makeAxiom1 (Not expr2) (And expr1 expr2)]++
        [makeAxiom9 (And expr1 expr2) expr2]++[reduceImpl $ makeAxiom9 (And expr1 expr2) expr2]++
        [(Not (And expr1 expr2))]

proof_00_Not_AandB = proof_01_Not_AandB

proof_11_AorB expr1 expr2 = 
        [expr1]++[makeAxiom6 expr1 expr2]++[(Or expr1 expr2)]

proof_01_AorB expr1 expr2 = 
        [expr2]++[makeAxiom7 expr1 expr2]++[(Or expr1 expr2)]

proof_10_AorB = proof_11_AorB

proof_00_Not_AorB expr1 expr2 = 
        [(Not expr1)]++[(Not expr2)]++
        (proof_00_AtoB expr1 expr2)++
        (proof_AtoA expr2)++
        [makeAxiom8 expr1 expr2 expr2]++[reduceImpl $ makeAxiom8 expr1 expr2 expr2]++
        [(Impl (Or expr1 expr2) expr2)]++
        [makeAxiom1 (Not expr2) (Or expr1 expr2)]++
        [(Impl (Or expr1 expr2) (Not expr2))]++
        [makeAxiom9 (Or expr1 expr2) expr2]++[reduceImpl $ makeAxiom9 (Or expr1 expr2) expr2]++
        [(Not (Or expr1 expr2))]    

proof_11_AtoB expr1 expr2 =
        [expr2]++[makeAxiom1 expr2 expr1]++[(Impl expr1 expr2)]

proof_01_AtoB = proof_11_AtoB

proof_10_Not_AtoB expr1 expr2 =
        [expr1]++[makeAxiom1 expr1 (Impl expr1 expr2)]++[(Impl (Impl expr1 expr2) expr1)]++
        (proof_AtoA (Impl expr1 expr2))++
        [makeAxiom2 (Impl expr1 expr2) expr1 expr2]++[reduceImpl $ makeAxiom2 (Impl expr1 expr2) expr1 expr2]++
        [(Impl (Impl expr1 expr2) expr2)]++
        [(Not expr2)]++[makeAxiom1 (Not expr2) (Impl expr1 expr2)]++
        [(Impl (Impl expr1 expr2) (Not expr2))]++
        [makeAxiom9 (Impl expr1 expr2) expr2]++[reduceImpl $ makeAxiom9 (Impl expr1 expr2) expr2]++
        [(Not (Impl expr1 expr2))]

proof_00_AtoB expr1 expr2 =
        [(Not expr1)]++[makeAxiom1 (Not expr1) expr1]++[(Impl expr1 (Not expr1))]++
        (proof_AtoNotAtoB expr1 expr2)++
        [makeAxiom2 expr1 (Not expr1) expr2]++[reduceImpl $ makeAxiom2 expr1 (Not expr1) expr2]++
        [(Impl expr1 expr2)]

reduceHyp (Impl expr1 expr2) (Impl (Not expr3) expr4) | expr1 == expr3 && expr2 == expr4 =
        [makeAxiom8 expr1 (Not expr1) expr2]++[reduceImpl $ makeAxiom8 expr1 (Not expr1) expr2]++
        [(Impl (Or expr1 (Not expr1)) expr2)]++
        (proof_AorNotA expr1)++
        [expr2]