data PropFormula = K PropFormula PropFormula
                  | A PropFormula PropFormula
                  | C PropFormula PropFormula
                  | D PropFormula PropFormula
                  | E PropFormula PropFormula
                  | J PropFormula PropFormula
                  | N PropFormula
                  | Prop String

instance Eq PropFormula where
  (K p1 q1) == (K p2 q2) = p1 == p2 && q1 == q2
  (A p1 q1) == (A p2 q2) = p1 == p2 && q1 == q2
  (C p1 q1) == (C p2 q2) = p1 == p2 && q1 == q2
  (D p1 q1) == (D p2 q2) = p1 == p2 && q1 == q2
  (E p1 q1) == (E p2 q2) = p1 == p2 && q1 == q2
  (J p1 q1) == (J p2 q2) = p1 == p2 && q1 == q2
  (N p1) == (N p2) = p1 == p2
  (Prop s1) == (Prop s2) = s1 == s2
  _ == _ = False

instance Show PropFormula where
  show (K p q) = "(" ++ show p ++ " & " ++ show q ++ ")"
  show (A p q) = "(" ++ show p ++ " v " ++ show q ++ ")"
  show (C p q) = "(" ++ show p ++ " => " ++ show q ++ ")"
  show (D p q) = "(" ++ show p ++ " | " ++ show q ++ ")"
  show (E p q) = "(" ++ show p ++ " <=> " ++ show q ++ ")"
  show (J p q) = "(" ++ show p ++ " + " ++ show q ++ ")"
  show (N p) = "~" ++ show p
  show (Prop s) = s

-- converts a postfix notation expression to a PropFormula
postfixToProp :: String -> PropFormula
postfixToProp s = head $ foldl applyOperator [] $ words s
  where applyOperator :: [PropFormula] -> String -> [PropFormula]
        applyOperator (p:q:ps) "&" = (K q p):ps
        applyOperator (p:q:ps) "v" = (A q p):ps
        applyOperator (p:q:ps) "=>" = (C q p):ps
        applyOperator (p:q:ps) "|" = (D q p):ps
        applyOperator (p:q:ps) "<=>" = (E q p):ps
        applyOperator (p:q:ps) "+" = (J q p):ps
        applyOperator (p:ps) "~" = (N p):ps
        applyOperator ps s = (Prop s):ps


main :: IO ()
main = interact $ \input -> show (postfixToProp input)