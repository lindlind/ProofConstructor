module Main where

import qualified Data.Map.Strict as Map
import System.IO
import Data.List
import Data.Tuple
import Lex
import Synt
import Creators

type MPMap = Map.Map Expr [Expr] 
type ProofMap = Map.Map Expr (Int, String, [Expr])
type ContextMap = Map.Map Expr Int
type NeedMap = Map.Map Expr Int
type VarMap = Map.Map [Bool] Bool

checkAxiom :: Expr -> Int
checkAxiom (Impl a1 (Impl b2 a2)) 
    | a1 == a2 
        = 1
checkAxiom (Impl (Impl a1 b1) (Impl (Impl a2 (Impl b2 c2)) (Impl a3 c3))) 
    | a1 == a2 && a2 == a3 && b1 == b2 && c2 == c3
        = 2
checkAxiom (Impl a1 (Impl b1 (And a2 b2)))
    | a1 == a2 && b1 == b2
        = 3
checkAxiom (Impl (And a1 b1) a2)
    | a1 == a2
        = 4
checkAxiom (Impl (And a1 b1) b2)
    | b1 == b2
        = 5
checkAxiom (Impl a1 (Or a2 b2))
    | a1 == a2
        = 6
checkAxiom (Impl b1 (Or a2 b2))
    | b1 == b2
        = 7
checkAxiom (Impl (Impl a1 c1) (Impl (Impl b2 c2) (Impl (Or a3 b3) c3)))
    | c1 == c2 && c2 == c3 && a1 == a3 && b2 == b3
        = 8
checkAxiom (Impl (Impl a1 b1) (Impl (Impl a2 (Not b2)) (Not a3)))
    | a1 == a2 && a2 == a3 && b1 == b2
        = 9
checkAxiom (Impl (Not (Not a1)) a2)
    | a1 == a2
        = 10
checkAxiom _ = 0

fst3 (a,_,_) = a

tupleToList ((a,b):s) = a:b:(tupleToList s)
tupleToList [] = []

map2 f (a:s) (b:t) = (f a b):(map2 f s t)
map2 f [] [] = []

merge (a:la) (b:lb) c ((_,e,d):ld) = (a,b,c,(reverse d),e):(merge la lb c ld)
merge [] [] c [] = []

checkMP :: Expr -> MPMap -> ProofMap -> (Bool, Expr, Expr)
checkMP expr mpMP mpProof = 
        if Map.notMember expr mpMP
            then (False, expr, expr)
            else 
                let (ok, a) = checkMPhelp expr (mpMP Map.! expr) mpProof
                in (ok, a, (Impl a expr))
    where
        checkMPhelp :: Expr -> [Expr] -> ProofMap -> (Bool, Expr)
        checkMPhelp expr [] mpProof = (False, expr)
        checkMPhelp expr (h:t) mpProof =
            if Map.member h mpProof
                then (True, h)
                else checkMPhelp expr t mpProof

updateMPMap :: MPMap -> Expr -> MPMap
updateMPMap mp (Impl a b) = Map.insertWith (++) b [a] mp
updateMPMap mp _ = mp 

makeMpContext :: Int -> [Expr] -> ContextMap -> ContextMap
makeMpContext cnt [] mpContext = mpContext
makeMpContext cnt (expr:others) mpContext = 
    if Map.notMember expr mpContext
        then makeMpContext (cnt + 1) others (Map.insert expr cnt mpContext)
        else makeMpContext (cnt + 1) others mpContext

addToProof :: [Expr] -> ContextMap -> MPMap -> ProofMap -> [Expr] -> (Bool, MPMap, ProofMap, [Expr])
addToProof [] mpContext mpMP mpProof readyPart = (True, mpMP, mpProof, readyPart)
addToProof (line:others) mpContext mpMP mpProof readyPart =
        let 
            axiom = checkAxiom line
            (okMP, a, b) = checkMP line mpMP mpProof
            newMpMP = updateMPMap mpMP line
            (okProof, newMpProof) = 
                if axiom /= 0
                    then (True, Map.insert line (0, "Ax. sch.", []) mpProof)
                    else if Map.member line mpContext
                        then (True, Map.insert line (0, "Hypothesis", []) mpProof)
                        else if okMP == True
                            then (True, Map.insert line (0, "M.P.", [a, b]) mpProof)
                            else (False, mpProof)
        in
            if Map.member line mpProof
                then addToProof others mpContext mpMP mpProof readyPart
                else if okProof == False
                    then (False, mpMP, mpProof, [line])
                    else addToProof others mpContext newMpMP newMpProof (line:readyPart)

checkProof :: [Expr] -> ContextMap -> (Bool, ProofMap, [Expr])
checkProof proof mpContext  = 
    let (ok, mpMP, mpProof, checkedProof) = addToProof proof mpContext Map.empty Map.empty []
    in (ok, mpProof, checkedProof)

useDeductionTheorem :: ContextMap -> ProofMap -> Expr -> [Expr] -> MPMap -> ProofMap -> [Expr] -> (Bool, ProofMap, [Expr])
useDeductionTheorem mpContext mpProof reducingExpr [] mpMP mpModifiedProof modifiedProof = (True, mpModifiedProof, modifiedProof)
useDeductionTheorem mpContext mpProof reducingExpr (line:proof) mpMP mpModifiedProof modifiedProof =
        let
            (_,lineType,h) = mpProof Map.! line 
            (a:b:c) = h

            addition = 
                if line == reducingExpr
                then proof_AtoA line
                else case lineType of
                    "Hypothesis" -> [line]++[(Impl line (Impl reducingExpr line))]++[(Impl reducingExpr line)]
                    "Ax. sch." -> [line]++[(Impl line (Impl reducingExpr line))]++[(Impl reducingExpr line)]
                    "M.P." -> 
                            [(Impl (Impl reducingExpr a) (Impl (Impl reducingExpr b) (Impl reducingExpr line)))]++
                            [(Impl (Impl reducingExpr b) (Impl reducingExpr line))]++
                            [(Impl reducingExpr line)]

            (okAdding, newMpMP, newMpModifiedProof, newModifiedProof)
                    = addToProof addition mpContext mpMP mpModifiedProof modifiedProof
        in
            if Map.member (Impl reducingExpr line) mpModifiedProof
                then useDeductionTheorem mpContext mpProof reducingExpr proof mpMP mpModifiedProof modifiedProof
                else if okAdding
                    then useDeductionTheorem mpContext mpProof reducingExpr proof newMpMP newMpModifiedProof newModifiedProof
                    else (False, newMpModifiedProof, newModifiedProof)


getVariableSets :: Expr -> [String] -> (VarMap,VarMap)
getVariableSets (Var name) [n1,n2,n3]
    | name == n1 =
        let 
            trues = Map.fromList [([True,False,False],True),([True,False,True],True),([True,True,False],True),([True,True,True],True)]
            falses = Map.fromList [([False,False,False],True),([False,False,True],True),([False,True,False],True),([False,True,True],True)]
        in (trues,falses)
    | name == n2 =
        let 
            trues = Map.fromList [([False,True,False],True),([False,True,True],True),([True,True,False],True),([True,True,True],True)]
            falses = Map.fromList [([False,False,False],True),([False,False,True],True),([True,False,False],True),([True,False,True],True)]
        in (trues,falses)
    | name == n3 =
        let 
            trues = Map.fromList [([False,False,True],True),([False,True,True],True),([True,False,True],True),([True,True,True],True)]
            falses = Map.fromList [([False,False,False],True),([False,True,False],True),([True,False,False],True),([True,True,False],True)]
        in (trues,falses)

getVariableSets (Var name) [n1,n2]
    | name == n1 =
        let 
            trues = Map.fromList [([True,False],True),([True,True],True)]
            falses = Map.fromList [([False,False],True),([False,True],True)]
        in (trues,falses)
    | name == n2 =
        let 
            trues = Map.fromList [([False,True],True),([True,True],True)]
            falses = Map.fromList [([False,False],True),([True,False],True)]
        in (trues,falses)

getVariableSets (Var name) [n1]
    | name == n1 =
        let 
            trues = Map.fromList [([True],True)]
            falses = Map.fromList [([False],True)]
        in (trues,falses)

getVariableSets (Not expr) vars = swap $ getVariableSets expr vars

getVariableSets (Impl expr1 expr2) vars = 
        let
            (trues1, falses1) = getVariableSets expr1 vars
            (trues2, falses2) = getVariableSets expr2 vars
        in (Map.union falses1 trues2, Map.intersection falses2 trues1)

getVariableSets (And expr1 expr2) vars = 
        let
            (trues1, falses1) = getVariableSets expr1 vars
            (trues2, falses2) = getVariableSets expr2 vars
        in (Map.intersection trues1 trues2, Map.union falses1 falses2)

getVariableSets (Or expr1 expr2) vars = 
        let
            (trues1, falses1) = getVariableSets expr1 vars
            (trues2, falses2) = getVariableSets expr2 vars
        in (Map.union trues1 trues2, Map.intersection falses1 falses2)


checkVariableSets :: VarMap -> VarMap -> [String] -> (Bool, String, [Bool])
checkVariableSets _ _ [] = (True, "Pos", [])

checkVariableSets trues falses [a]
    | falses == Map.empty                
        = (True, "Pos", [False])
    | trues == Map.fromList [([True],True)] 
        = (True, "Pos", [True])
    | trues == Map.empty                
        = (True, "Neg", [False])
    | otherwise = (False,"",[])

checkVariableSets trues falses [a,b]
    | falses == Map.empty                
        = (True, "Pos", [False, False])
    | Map.intersection falses (Map.fromList [([True, True],True), ([True, False],True)]) == Map.empty
        = (True, "Pos", [True, False])
    | Map.intersection falses (Map.fromList [([True, True],True), ([False, True],True)]) == Map.empty
        = (True, "Pos", [False, True])
    | Map.intersection falses (Map.fromList [([True, True],True)]) == Map.empty
        = (True, "Pos", [True, True])
    | trues == Map.empty                
        = (True, "Neg", [False, False])
    | Map.intersection trues (Map.fromList [([False, False],True), ([False, True],True)]) == Map.empty
        = (True, "Neg", [True, False])
    | Map.intersection trues (Map.fromList [([False, False],True), ([True, False],True)]) == Map.empty
        = (True, "Neg", [False, True])
    | Map.intersection trues (Map.fromList [([False, False],True)]) == Map.empty
        = (True, "Neg", [True, True])
    | otherwise = (False,"",[])

checkVariableSets trues falses [a,b,c]
    | falses == Map.empty                
        = (True, "Pos", [False, False, False])      
    | Map.intersection falses (Map.fromList [([True, True, True],True), ([True, True, False],True), ([True, False, True],True), ([True, False, False],True)]) == Map.empty
        = (True, "Pos", [True, False, False])
    | Map.intersection falses (Map.fromList [([True, True, True],True), ([True, True, False],True), ([False, True, True],True), ([False, True, False],True)]) == Map.empty
        = (True, "Pos", [False, True, False])
    | Map.intersection falses (Map.fromList [([True, True, True],True), ([True, False, True],True), ([False, True, True],True), ([False, False, True],True)]) == Map.empty
        = (True, "Pos", [False, False, True])
    | Map.intersection falses (Map.fromList [([True, True, True],True), ([True, True, False],True)]) == Map.empty
        = (True, "Pos", [True, True, False])
    | Map.intersection falses (Map.fromList [([True, True, True],True), ([False, True, True],True)]) == Map.empty
        = (True, "Pos", [False, True, True])
    | Map.intersection falses (Map.fromList [([True, True, True],True), ([True, False, True],True)]) == Map.empty
        = (True, "Pos", [True, False, True])
    | Map.intersection falses (Map.fromList [([True, True, True],True)]) == Map.empty
        = (True, "Pos", [True, True, True])
    | trues == Map.empty                
        = (True, "Neg", [False, False, False])      
    | Map.intersection trues (Map.fromList [([False, False, False],True), ([False, True, False],True), ([False, False, True],True), ([False, True, True],True)]) == Map.empty
        = (True, "Neg", [True, False, False])
    | Map.intersection trues (Map.fromList [([False, False, False],True), ([True, False, False],True), ([False, False, True],True), ([True, False, True],True)]) == Map.empty
        = (True, "Neg", [False, True, False])
    | Map.intersection trues (Map.fromList [([False, False, False],True), ([True, False, False],True), ([False, True, False],True), ([True, True, False],True)]) == Map.empty
        = (True, "Neg", [False, False, True])
    | Map.intersection trues (Map.fromList [([False, False, False],True), ([False, False, True],True)]) == Map.empty
        = (True, "Neg", [True, True, False])
    | Map.intersection trues (Map.fromList [([False, False, False],True), ([True, False, False],True)]) == Map.empty
        = (True, "Neg", [False, True, True])
    | Map.intersection trues (Map.fromList [([False, False, False],True), ([False, True, False],True)]) == Map.empty
        = (True, "Neg", [True, False, True])
    | Map.intersection trues (Map.fromList [([False, False, False],True)]) == Map.empty
        = (True, "Neg", [True, True, True])
    | otherwise = (False,"",[])

getContextList :: [String] -> String -> [Bool] -> [[Expr]] -> [Expr] -> [[Expr]]
getContextList (s:vars) verdict (inHead:boolContext) [headContext] tailContext =
        case (inHead, verdict) of
            (True, "Pos") -> getContextList vars verdict boolContext [(Var s):headContext] tailContext
            (True, "Neg") -> getContextList vars verdict boolContext [(Not (Var s)):headContext] tailContext
            (False, _   ) -> getContextList vars verdict boolContext [headContext] ((Var s):tailContext)


getContextList [] verdict [] headContext (expr:tailContext) = 
        let newHeadContext = tupleToList $ map (\a -> ((expr:a),((Not expr):a))) headContext
        in getContextList [] verdict [] newHeadContext tailContext

getContextList [] _ [] headContext [] = headContext

constructProof :: ContextMap -> Expr -> ([Expr], String)
constructProof mpContext (Var s) = 
    if Map.member (Var s) mpContext
        then ([(Var s)], "Pos")
        else ([(Not (Var s))], "Neg")

constructProof mpContext (Not expr) =
        let
            (proof, verdict) = constructProof mpContext expr
        in if verdict == "Neg"
            then (proof, "Pos")
            else (proof++(proof_A_NotNotA expr), "Neg")

constructProof mpContext (And expr1 expr2) =
        let
            (proof1, verdict1) = constructProof mpContext expr1
            (proof2, verdict2) = constructProof mpContext expr2
        in case (verdict1, verdict2) of
            ("Pos", "Pos") -> (proof1++proof2++(proof_11_AandB     expr1 expr2), "Pos")
            ("Pos", "Neg") -> (proof1++proof2++(proof_10_Not_AandB expr1 expr2), "Neg")
            ("Neg", "Pos") -> (proof1++proof2++(proof_01_Not_AandB expr1 expr2), "Neg")
            ("Neg", "Neg") -> (proof1++proof2++(proof_00_Not_AandB expr1 expr2), "Neg")

constructProof mpContext (Or expr1 expr2) =
        let
            (proof1, verdict1) = constructProof mpContext expr1
            (proof2, verdict2) = constructProof mpContext expr2
        in case (verdict1, verdict2) of
            ("Pos", "Pos") -> (proof1++proof2++(proof_11_AorB     expr1 expr2), "Pos")
            ("Pos", "Neg") -> (proof1++proof2++(proof_10_AorB     expr1 expr2), "Pos")
            ("Neg", "Pos") -> (proof1++proof2++(proof_01_AorB     expr1 expr2), "Pos")
            ("Neg", "Neg") -> (proof1++proof2++(proof_00_Not_AorB expr1 expr2), "Neg")

constructProof mpContext (Impl expr1 expr2) =
        let
            (proof1, verdict1) = constructProof mpContext expr1
            (proof2, verdict2) = constructProof mpContext expr2
        in case (verdict1, verdict2) of
            ("Pos", "Pos") -> (proof1++proof2++(proof_11_AtoB     expr1 expr2), "Pos")
            ("Pos", "Neg") -> (proof1++proof2++(proof_10_Not_AtoB expr1 expr2), "Neg")
            ("Neg", "Pos") -> (proof1++proof2++(proof_01_AtoB     expr1 expr2), "Pos")
            ("Neg", "Neg") -> (proof1++proof2++(proof_00_AtoB     expr1 expr2), "Pos")

combineAllProofs :: [([Expr], ContextMap, Expr, [Expr], ProofMap)] -> ([Expr], ContextMap, Expr, [Expr], ProofMap)
combineAllProofs [(context, mpContext, mainExpr, proof, mpProof)] = 
        let minimizedProof = minimizeProof (reverse proof) (Map.singleton mainExpr 0) mpProof []
        in (context, mpContext, mainExpr, minimizedProof, mpProof)

combineAllProofs allList = 
        let
            deductedList = map (\(a,b,c,d,e) -> getMinimizedDeductedProof a b c d e) allList

            mergeHandler ((_,context1,mpContext1,(Impl c1 expr1),proof1,e1):(_,context2,mpContext2,(Impl c2 expr2),proof2,e2):s) = 
                let
                    (okAdding_1, mpMP_1, mpProof_1, proof_1)
                            = addToProof proof1 mpContext1 Map.empty Map.empty []
                    (okAdding_2, mpMP_2, mpProof_2, proof_2)
                            = addToProof proof2 mpContext1 mpMP_1 mpProof_1 proof_1
                    (okAdding_3, mpMP_3, readyMpProof, readyRevProof)
                            = addToProof (reduceHyp (Impl c1 expr1) (Impl c2 expr2)) mpContext1 mpMP_2 mpProof_2 proof_2
                in 
                    (context1, mpContext1, expr1, (reverse readyRevProof), readyMpProof):(mergeHandler s)

            mergeHandler [] = []

            mergedList = mergeHandler deductedList
        in 
            combineAllProofs mergedList



minimizeProof :: [Expr] -> NeedMap -> ProofMap -> [Expr] -> [Expr]
minimizeProof [] mpNeed mpProof checkedPart = checkedPart
minimizeProof (line:others) mpNeed mpProof checkedPart =
        let 
            (a,b,h) = mpProof Map.! line
            (c:d:e) = h
            aMpNeed = Map.insert c 0 mpNeed
            bMpNeed = Map.insert d 0 aMpNeed
        in
            if Map.notMember line mpNeed
                then minimizeProof others mpNeed mpProof checkedPart
                else if b /= "M.P."
                    then minimizeProof others mpNeed mpProof (line:checkedPart)
                    else minimizeProof others bMpNeed mpProof (line:checkedPart)

finishProof :: Int -> [Expr] -> ProofMap -> ContextMap -> [(String, Expr)] -> [(String, Expr)]
finishProof cnt [] mpProof mpContext readyPart = reverse readyPart
finishProof cnt (line:others) mpProof mpContext readyPart = 
        let
            (a, b, x) = mpProof Map.! line
            newMpProof = Map.insert line (cnt, b, x) mpProof
            (m:p:e) = x
            z = case b of
                "Ax. sch." -> show $ checkAxiom line
                "Hypothesis" -> show $ mpContext Map.! line
                "M.P." -> (show $ fst3 $ mpProof Map.! p) ++ ", " ++ (show $ fst3 $ mpProof Map.! m)
            comment = "[" ++ (show cnt) ++ ". " ++ b ++ " " ++ z ++ "] "
        in
            finishProof (cnt + 1) others newMpProof mpContext ((comment,line):readyPart)

getMinimizedDeductedProof :: [Expr] -> ContextMap -> Expr -> [Expr] -> ProofMap -> (Bool, [Expr], ContextMap, Expr, [Expr], ProofMap)
getMinimizedDeductedProof revContext mpContext mainExpr proof mpProof =
        let
            reducedExpr = head revContext
            dedRevContext = tail revContext
            dedMainExpr = (Impl reducedExpr mainExpr)
            mpDedContext = makeMpContext 1 dedRevContext Map.empty
            (okDeduction, mpDedProof, dedRevProof) =
                useDeductionTheorem mpDedContext mpProof reducedExpr proof Map.empty Map.empty []
            minimizedDedProof = minimizeProof dedRevProof (Map.singleton dedMainExpr 0) mpDedProof []
        in (okDeduction, dedRevContext, mpDedContext, dedMainExpr, minimizedDedProof, mpDedProof)

getFileInput = do
    inh <- openFile "in.txt" ReadMode
    input <- hGetLine inh
    let (mainExpr:context) = parseFirstLine $ alexScanTokens input
    contents <- hGetContents inh
    let proof = ($!) map (parse . alexScanTokens) (filter (/= []) (lines contents))
    return (mainExpr, (reverse context), proof)

getInput = do
    input <- getLine
    let (mainExpr:context) = parseFirstLine $ alexScanTokens input
    contents <- getContents
    let proof = ($!) map (parse . alexScanTokens) (filter (/= []) (lines contents))
    return (mainExpr, (reverse context), proof)

getCommentedOutput context mainExpr proof = do
    putStr $ intercalate ", "  (map show context)
    putStr " |- " 
    putStrLn $ show mainExpr
    putStrLn $ intercalate "\n" (map (\(a,b) -> (a ++ (show b))) proof)

getOutput context mainExpr proof = do
    putStr $ intercalate ", "  (map show context)
    putStr " |- " 
    putStrLn $ show mainExpr
    --putStrLn $ intercalate "\n" (map (\(a,b) -> (show b)) proof)
    putStrLn $ intercalate "\n" (map (\b -> (show b)) proof)

debugOut smth = do
    putStrLn $ show smth

proofWithoutHypothesis = do
        input <- getLine
        let mainExpr = parse $ alexScanTokens input
        let vars = Map.keys $ Map.fromList $ map (\el -> (el, True)) (getVariables $ alexScanTokens input)
        let contextList = getContextList vars "Pos" (map (\_ -> False) vars) [[]] []
        let mpContextList = map (\context -> makeMpContext 1 context Map.empty) contextList
        let proofList = map (\(a,b) -> a) $ map (\mpContext -> constructProof mpContext mainExpr) mpContextList
        let mpProofandCheckedProofList = map2 checkProof proofList mpContextList 
        let allList = merge contextList mpContextList mainExpr mpProofandCheckedProofList
        let (contextR, mpContextR, mainExprR, proofR, mpProofR) = combineAllProofs allList
        let readyProof = finishProof 1 proofR mpProofR mpContextR []
        if proofR == []
            then putStrLn ":("
            else getCommentedOutput contextR mainExprR readyProof

main = do
        input <- getLine
        let mainExpr = parse $ alexScanTokens input
        let vars = Map.keys $ Map.fromList $ map (\el -> (el, True)) (getVariables $ alexScanTokens input)
        let (trues, falses) = getVariableSets mainExpr vars
        let (canGetProof, verdict, boolContext) = checkVariableSets trues falses vars
        let mainExprPreR = if verdict == "Pos" then mainExpr else (Not mainExpr)
        let contextList = getContextList vars verdict boolContext [[]] []
        let mpContextList = map (\context -> makeMpContext 1 context Map.empty) contextList
        let proofList = map (\(a,b) -> a) $ map (\mpContext -> constructProof mpContext mainExprPreR) mpContextList
        let mpProofandCheckedProofList = map2 checkProof proofList mpContextList 
        let allList = merge contextList mpContextList mainExprPreR mpProofandCheckedProofList
        let (contextR, mpContextR, mainExprR, proofR, mpProofR) = combineAllProofs allList
        let readyProof = finishProof 1 proofR mpProofR mpContextR []
        if canGetProof
            then getOutput contextR mainExprR readyProof
            else putStrLn ":("

mainDeduct = do
        (expr, revContext, proof) <- getFileInput
        let mpContext = makeMpContext 1 revContext Map.empty
        let (ok, mpProof, checkedProof) = checkProof proof mpContext
        let (okDed,dedRevContext,_,dedExpr,dedProof,_) = getMinimizedDeductedProof revContext mpContext expr proof mpProof
        if (ok && okDed)
            then getOutput (reverse (tail revContext)) dedExpr dedProof
            else putStrLn ":("

