module CS30.Exercises.SetExprProof where
    import CS30.Data
    import CS30.Exercises.Data
    import Data.Void
    import Text.Megaparsec
    import Text.Megaparsec.Char
    import Control.Monad.Combinators.Expr
    import Data.Functor.Identity
    import CS30.Exercises.SetConversionProofs.LawParser
    import CS30.Exercises.SetConversionProofs.SetExprParser (SetExpr)

    data Proof = Proof SetExpr [ProofStep]
                    deriving (Show)
    type ProofStep = (String, SetExpr)

    type Substitution = [(String, SetExpr)]


    generateRandEx :: Int -> ChoiceTree SetExpr 
    generateRandEx i | i < 1 
      = Branch [ Branch [Node (Var varname) | varname <- ["X", "Y", "Z"]] 
               , Branch [Node (Const val) | val <- [2..10]]
               ]
    generateRandEx i 
      = Branch [do e <- generateRandEx (i-1)
                   return (In e)
                , Branch [do e1 <- generateRandEx i'
                             e2 <- generateRandEx (i-i'-1)
                             return (Cap e1 e2)
                         | i' <- [0..i-1]
                         ]
                ]-- generates rand expressions of a given size 
        

           

    -- mapAround f (Node a) = Node (f a)
    -- mapAround f (Branch as) = Branch ((mapAround f) as)

    --  = Branch [ In expr | expr <- generateRandEx (i-1) ]


    -- randomly generates an expression, want to use it in combo with some laws to get a derivation 

    getDerivation:: [Law] -> SetExpr -> Proof
    getDerivation laws e 
     = Proof e (multiSteps e) 
       where multiSteps e' 
              = case [(lawname law, res)
                     | law <- laws 
                     , res <- getStep (lawEq law) e'
                     ]  of 
                  [] -> []
                  ((nm, e''): _) -> (nm, e'') : multiSteps e''
             
    -- first check if there's a match 
    -- subst to get: x = 
    getStep :: Equation -> SetExpr -> [SetExpr]
    getStep (lhs, rhs) expr 
      = case match' lhs expr of 
          Nothing -> recurse expr 
          Just (subst:_) -> [apply subst rhs]
        where recurse (Var _ ) = [] 
              recurse (Cap e1 e2) 
                = [Cap e1' e2 | e1' <- getStep (lhs, rhs) e1] ++ 
                  [Cap e1 e2' | e2' <- getStep (lhs, rhs) e2]
              recurse (Cup e1 e2) 
                = [Cup e1' e2 | e1' <- getStep (lhs, rhs) e1] ++ 
                  [Cup e1 e2' | e2' <- getStep (lhs, rhs) e2]
              recurse (SetMinus e1 e2) 
                = [SetMinus e1' e2 | e1' <- getStep (lhs, rhs) e1] ++ 
                  [SetMinus e1 e2' | e2' <- getStep (lhs, rhs) e2]
              recurse (Wedge e1 e2) 
                = [Wedge e1' e2 | e1' <- getStep (lhs, rhs) e1] ++ 
                  [Wedge e1 e2' | e2' <- getStep (lhs, rhs) e2]
              recurse (Vee e1 e2) 
                = [Vee e1' e2 | e1' <- getStep (lhs, rhs) e1] ++ 
                  [Vee e1 e2' | e2' <- getStep (lhs, rhs) e2]
    
    match' :: SetExpr -> SetExpr -> Maybe Substitution
    match' (Var nm) expr = Just [(nm, expr)]
    match' (Const i) (Const j) | i == j = Just []
    match' (Const i) _ = Nothing 
    match' (Cap e1 e2) (Cap e3 e4) -- | op == op2
      = case (match' e1 e3, match' e2 e4) of 
          (Just s1, Just s2) -> combineTwoSubsts s1 s2
          _ -> Nothing 
    --  = do s1 <- match' e1 e3
    --       s2 <- match' e2 e4 
    --       combineTwoSubsts s1 s2 -- with maybe monad
    match' (Cap _ _) _ = Nothing

    combineTwoSubsts :: Substitution -> Substitution -> Maybe Substitution
    combineTwoSubsts s1 s2 
      = case and [ v1 == v2 | (nm1, v1) <- s1, (nm2, v2) <- s2, nm1 == nm2] of 
          True -> Just (s1 ++ s2)
          False -> Nothing

    apply :: Substitution -> SetExpr -> SetExpr 
    apply subst (Var nm) 
      = lookupInSubst nm subst   
    apply subst (Cap e1 d2) = Cap (apply subst e1) (apply subst e2) -- for all bin operations 

    lookupInSubst:: String -> [(String, p)] -> p
    lookupInSubst nm ((nm',v): rm)
      | nm == nm' = v 
      | otherwise = lookupInSubst nm rm 
    lookupInSubst _ [] = error "Subst not complete or free varrs exisitined in the rhs of the equality"
