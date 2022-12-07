{-
 - Author: James Pabisz, Jpabisz2020@my.fit.edu
 - Author: Remington Greko, Rgreko2020@my.fit.edu
 - Course: CSE 4250, Fall 2021
 - Project: Proj4, Tautology Checker
 - Language implementation: Glorious Glasgow Haskell Compilation System, version 8.6.5
 -}
 
module Main where

    --main :: IO()
    --main = interact (showResults . map Proposition . readTestCases)
    
    --readTestCases :: String -> [(Double,Double,Double,Double)]
    --readTestCases = pairUp . (map read) . words
    
    --showResults ::  [String] -> String
    --showResults = unlines
    
    
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
        deriving (Eq, Show)
        
    concatProp :: Proposition -> [String]
    concatProp (Const  _   ) = []
    concatProp (Var    x   ) = [x]
    concatProp (A    prop1 p2) = (concatProp prop1) ++ (concatProp p2)
    concatProp (C    prop1 p2) = (concatProp prop1) ++ (concatProp p2)
    concatProp (D    prop1 p2) = (concatProp prop1) ++ (concatProp p2)
    concatProp (E    prop1 p2) = (concatProp prop1) ++ (concatProp p2)
    concatProp (J    prop1 p2) = (concatProp prop1) ++ (concatProp p2)
    concatProp (K    prop1 p2) = (concatProp prop1) ++ (concatProp p2)
    concatProp (N    prop) = concatProp proposition
