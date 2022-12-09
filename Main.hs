{-
 - Author: James Pabisz, Jpabisz2020@my.fit.edu
 - Author: Remington Greko, Rgreko2020@my.fit.edu
 - Course: CSE 4250, Fall 2021
 - Project: Proj4, Tautology Checker
 - Language implementation: Glorious Glasgow Haskell Compilation System, version 8.6.5
 -}


module Main where

    import Data.List
    import Data.List.Split
    
    data Proposition =
          Const Bool
        | Var String 
        | A Proposition Proposition
        | C Proposition Proposition
        | D Proposition Proposition
        | E Proposition Proposition
        | J Proposition Proposition
        | K Proposition Proposition
        | N Proposition
        deriving (Eq, Read)
        
    -- not used right now ---------    
    logicify :: String -> String
    logicify = intercalate " " . chunksOf 2
    ------------------------------
    
    type Attribution = [(String, Bool)]
    
    instance Show Proposition where
      show (K p q) = "(" ++ show p ++ " & " ++ show q ++ ")"
      show (A p q) = "(" ++ show p ++ " v " ++ show q ++ ")"
      show (C p q) = "(" ++ show p ++ " => " ++ show q ++ ")"
      show (D p q) = "(" ++ show p ++ " | " ++ show q ++ ")"
      show (E p q) = "(" ++ show p ++ " <=> " ++ show q ++ ")"
      show (J p q) = "(" ++ show p ++ " + " ++ show q ++ ")"
      show (N p) = "~" ++ show p
      show (Var s) = s


    -- given a proposition, return a list with all the variables that show up
    concatProp :: Proposition -> [String]
    concatProp (Const  _   ) = []
    concatProp (Var    s   ) = [s]
    concatProp (N    prop) = concatProp prop
    concatProp (A    p1 p2) = (concatProp p1) ++ (concatProp p2)
    concatProp (C    p1 p2) = (concatProp p1) ++ (concatProp p2)
    concatProp (D    p1 p2) = (concatProp p1) ++ (concatProp p2)
    concatProp (E    p1 p2) = (concatProp p1) ++ (concatProp p2)
    concatProp (J    p1 p2) = (concatProp p1) ++ (concatProp p2)
    concatProp (K    p1 p2) = (concatProp p1) ++ (concatProp p2)

    -- given a list of variables, returns a list with all possible attributions
    varAttributions :: [String] -> [Attribution]
    --varAttributions vars = map (zipWith (,) vars) tables
    varAttributions vars = map (zip vars) tables
        where
            tables = allTruthTables $ length vars

    -- generates all 2^n truth tables for n variables
    allTruthTables :: Int -> [[Bool]]
    allTruthTables 0 = [[]]
    allTruthTables n = ((True:) <$> prevTables) ++ ((False:) <$> prevTables)
        where
            prevTables = allTruthTables (n-1)

    -- given a proposition and an attribution, return its truth value
    truthValue :: Proposition -> Attribution -> Maybe Bool
    truthValue (Const bool) _ = Just bool
    truthValue (Var   v   ) attrs = lookup v attrs
    truthValue (N   p   ) attrs = not <$> (truthValue p attrs)
    -- implement short-circuiting for the And, Or and Impl propositions
    truthValue (K   p1 p2) attrs
        | valuep1 == (Just False) = Just False
        | otherwise               = (&&) <$> valuep1 <*> (truthValue p2 attrs)
        where valuep1 = truthValue p1 attrs
    truthValue (A    p1 p2) attrs
        | valuep1 == (Just True) = Just True
        | otherwise              = (||) <$> valuep1 <*> (truthValue p2 attrs)
        where valuep1 = truthValue p1 attrs
    -- maybe it is cheating, but b1 <= b2 as "less than or equal to" evaluates to the same thing
    -- as "b1 implies b2"!
    truthValue (C  p1 p2) attrs
        | valuep1 == (Just False) = Just True
        | otherwise               = (<=) <$> valuep1 <*> (truthValue p2 attrs)
        where valuep1 = truthValue p1 attrs
    truthValue (E p1 p2) attrs = (==) <$> (truthValue p1 attrs) <*> (truthValue p2 attrs)

    -- given a proposition, evaluate it at all of its attributions
    extensiveEvaluation :: Proposition -> [Bool]
    extensiveEvaluation prop = unwrap values
        where
            vars = concatProp prop
            attributions = varAttributions vars
            -- use sequence to make this [Maybe Bool] a Maybe [Bool]
            values = sequence $ map (truthValue prop) attributions
            unwrap (Just j) = j
            -- if "attributions" is calculated with my varAttributions then "truthValue"
            -- will never return a Nothing, so that "map (truthValue prop) attributions" is
            -- a list of a lot of (Just bool) and no Nothing shows up
            unwrap Nothing = error "everything just crashed!"

    -- checks if a given proposition is a tautology
    tautology :: Proposition -> Bool
    tautology = and . extensiveEvaluation


    {- Show that the "and", "or" and "equivalence"
        operators can be built with negations and implications;
        The only "Equiv" propositions allowed are the middle one
        that actually check if the two sides are equal -}
    -- P v Q <=> (~P => Q)
    prop1 = (Var "P")
    -- P ^ Q <=> ~(P => ~Q)
    prop2 = A (A (Var "P") (Var "Q")) (A (N (Var "P"))  (N (Var "Q")))
    -- (P <=> Q) <=> ~((P => Q) => ~(Q => P))
    prop3 = E
                (E (Var "P") (Var "Q"))
                (N (C
                        (C (Var "P") (Var "Q"))
                        (N (C (Var "Q") (Var "P")))
                    ))
    -- (P => Q) => [(Q => R) => (P => R)]
    prop4 = C
                (C (Var "P") (Var "Q"))
                (C
                    (C (Var "Q") (Var "R"))
                    (C (Var "P") (Var "R"))
                )
    -- this should be falsifiable
    -- [P => (Q => (P => Q))] => (P => Q)
    prop5 = (A (Var "P") (N (Var "P")))
    
    toNNF :: Proposition -> Proposition
    toNNF expr@(Var _)        = expr
    toNNF expr@(N (Var _))    = expr
    toNNF (N (N expr))        = expr

    toNNF (K exp1 exp2)       = toNNF exp1 `conj` toNNF exp2
    toNNF (N (K exp1 exp2))   = toNNF $ neg exp1 `disj` neg exp2

    toNNF (A exp1 exp2)       = toNNF exp1 `disj` toNNF exp2
    toNNF (N (A exp1 exp2))   = toNNF $ neg exp1 `conj` neg exp2
    
    toNNF (D exp1 exp2)       = toNNF $ neg exp1 `disj` neg exp2
    toNNF (N (D exp1 exp2))   = toNNF $ exp1 `conj` exp2
    
    toNNF (J exp1 exp2)       = toNNF $ neg exp1 `equ` exp2
    toNNF (N (J exp1 exp2))   = toNNF $ exp1 `equ` exp2

    toNNF (C exp1 exp2)       = toNNF $ neg exp1 `disj` exp2
    toNNF (N (C exp1 exp2))   = toNNF $ exp1 `conj` neg exp2

    toNNF (E exp1 exp2)       = let a = exp1 `conj` exp2
                                    b = neg exp1 `conj` neg exp2
                              in toNNF $ a `disj` b
    toNNF (N (E exp1 exp2))   = let a = exp1 `disj` exp2
                                    b = neg exp1 `disj` neg exp2
                              in toNNF $ a `conj` b
    
    
    toCNF :: Proposition -> Proposition
    toCNF = toCNF' . toNNF
      where
        toCNF' :: Proposition -> Proposition
        toCNF' (K exp1 exp2) = toCNF' exp1 `conj` toCNF' exp2
        toCNF' (A exp1 exp2) = toCNF' exp1 `dist` toCNF' exp2
        toCNF' expr                    = expr
    
        dist :: Proposition -> Proposition -> Proposition
        dist (K e11 e12) e2 = (e11 `dist` e2) `conj` (e12 `dist` e2)
        dist e1 (K e21 e22) = (e1 `dist` e21) `conj` (e1 `dist` e22)
        dist e1 e2                    = e1 `disj` e2
        
    neg :: Proposition -> Proposition
    neg = N

    disj :: Proposition -> Proposition -> Proposition
    disj = A

    conj :: Proposition -> Proposition -> Proposition
    conj = K
    
    equ :: Proposition -> Proposition -> Proposition
    equ = E

    main = do
        putStrLn $ show (tautology prop1)
        putStr $ " Hello  "
        --print $ tautology prop2
        --print $ concatProp prop2
        let x = prop2
        let t = toCNF prop2
        --let val = sequence $ map (truthValue prop2) t
        print $ x
        print $ tautology x
        print $ tautology prop4
        print $ tautology prop5
        
