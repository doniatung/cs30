module CS30.Exercises.ThursdayLecture where
import CS30.Exercises.Data
import Data.Ratio


law1 :: Law
law1 = Law "Assoc" (EBin Plus (EBin Plus (EVar "X") (EVar "Y")) (EVar "Z")
                  , EBin Plus (EVar "X") (EBin Plus (EVar "Y") (EVar "Z")))

-- aim:
-- laws = map parse ["assoc: (X+Y)+Z=X+(Y+Z)"]

type Distribution = [(Integer, Rational)] -- normalize first, then multiply by normalization coefficient to get weight
--  (weight, change)

evaluate :: (String -> Distribution) -> ProbExpr -> Distribution
evaluate lkp (EVar v ) = lkp v 
evaluate _ (EConst i) = [(1,i % 1)] 
evaluate lkp (EBin op e1 e2) = do_op (evaluate lkp e1) (evaluate lkp e2)
  where do_op  dst1 dst2 = [(occ1 * occ2, f val1 val2) 
                               | (occ1, val1) <- dst1
                               , (occ2, val2) <- dst2
                               ]
        f v1 v2 = case op of {Plus -> v1 + v2; Minus -> v1 - v2 ; Times -> v1 * v2}
        -- though this is buggy because it doesn't account for when we have the same var twice 
evaluate lkp (EExpct e) = [(1, vals / (normlFactor % 1))]
   where list = lkp e
         normlFactor = sum (map fst list)
         vals = sum (map (\(oc, val) -> (oc % 1) * val) list)
  
getVariables :: ProbExpr -> [String]
getVariables (EVar v) = [v]
getVariables (EConst _) = []
getVariables (EBin _ e1 e2) = getVariables e1 ++ getVariables e2
getVariables (EExpct e) = getVariables e 

getDistribution :: [String] -> ChoiceTree (String -> Distribution)
getDistribution [] = Node (\_ -> error "could not find your variable in the distribution")
getDistribution (x:xs)
 = do f <- getDistribution xs 
      randVal <- genDistribution 4 
      return (\varnm -> if varnm == x then randVal else f varnm)

genDistribution :: Int -> ChoiceTree Distribution
genDistribution 0 = Node []
genDistribution n = do rmd <- genDistribution (n-1)
                       occ <- nodes [1..10]
                       val <- nodes [1..100]
                       return ((occ, val): rmd)


-- exs :: [ChoiceTree ExType]

data ProbExpr
 = EVar String -- ^ random variable, like X, or variables in expressions, like 'x'
 | EConst Integer -- ^ constant integer, like 3
 | EBin EOp ProbExpr ProbExpr -- ^ X * 3, or 2 + Y, ...
 | EExpct ProbExpr -- ^ expected value of an expression E[X * 3], for instance
 deriving (Show, Eq)

data EOp
 = Plus | Minus | Times
 deriving (Show, Eq)

generateRandEx :: Int -> ChoiceTree ProbExpr
generateRandEx i | i < 1
 = Branch [ Branch [Node (EVar varName) | varName <- ["X","Y","Z"]]
          , Branch [Node (EConst val) | val <- [2..10]]
          ]
generateRandEx i
 = Branch [do {e1 <- generateRandEx i'
              ;e2 <- generateRandEx (i - i' - 1)
              ;opr <- nodes [Plus,Minus,Times]
              ;return (EBin opr e1 e2)
              }
          | i' <- [0..i-1]
          ]


-- data Law = Law String Equation
-- lawName (Law nm _) = nm
-- lawEq (Law _ eq) = eq
data Law = Law {lawName :: String, lawEq :: Equation}

type Equation = (ProbExpr,ProbExpr)

data Proof = Proof ProbExpr [ProofStep] deriving Show
type ProofStep = (String, ProbExpr)

getDerivation :: [Law] -> ProbExpr -> Proof
getDerivation laws e
 = Proof e (multiSteps e)
 where multiSteps e'
        = case [ (lawName law, res)
               | law <- laws
               , res <- getStep (lawEq law) e'
               ] of
           [] -> []
           ((nm,e''):_) -> (nm,e'') : multiSteps e''

-- as example of getStep:
-- (5 - 3) - 1
-- x - y = x + (negate y)
-- lhs: x - y, rhs: x + (negate y)
-- expr: E[(5 - 3) - 1]
-- subst to get: x = 5 - 3, y = 1
-- x ≥ y ==> (x + 1 > y <--> True)
-- x > 0 ==> (x * y = x * z <--> y = z)

    -- 3 * a = 3 * b
    -- isThisTrue (3>0)
    -- (3>0)
    -- = {3 = 1 + 2}
    --  1 + 2 > 0
    -- = {2 = 1 + 1}
    -- 1 + 1 + 1 > 0
    -- = {1 + 1 ≥ 0?}
    -- True

getStep :: Equation -> ProbExpr -> [ProbExpr]
getStep (lhs, rhs) expr
  = case matchE lhs expr of
      Nothing -> recurse expr
      Just subst -> [apply subst rhs] -- | isThisTrue (apply subst prereq)]
  where recurse (EVar _) = []
        recurse (EConst _) = []
        recurse (EBin op e1 e2)
          = [EBin op e1' e2 | e1' <- getStep (lhs,rhs) e1] ++
            [EBin op e1 e2' | e2' <- getStep (lhs,rhs) e2]
        recurse (EExpct e1)
          = [EExpct e1' | e1' <- getStep (lhs,rhs) e1]
-- 0 + x = x
type Substitution = [(String, ProbExpr)]
matchE :: ProbExpr -> ProbExpr -> Maybe Substitution
matchE (EVar nm) expr = Just [(nm,expr)]
matchE (EConst 0) (EConst 0) = Just []
matchE (EConst i) (EConst j) | i == j = Just []
matchE (EConst _) _ = Nothing
matchE (EBin op1 e1 e2) (EBin op2 e3 e4) | op1 == op2
 = case (matchE e1 e3, matchE e2 e4) of
    (Just s1, Just s2) -> combineTwoSubsts s1 s2
    _ -> Nothing
-- = do s1 <- matchE e1 e3
--      s2 <- matchE e2 e4
--      combineTwoSubsts s1 s2
matchE (EBin _ _ _) _ = Nothing
matchE (EExpct e1) (EExpct e2) = matchE e1 e2
matchE (EExpct _) _ = Nothing
combineTwoSubsts :: Substitution -> Substitution -> Maybe Substitution
combineTwoSubsts s1 s2
  = case and [v1 == v2 | (nm1,v1) <- s1, (nm2,v2) <- s2, nm1 == nm2] of
     True -> Just (s1 ++ s2)
     False -> Nothing
apply :: Substitution -> ProbExpr -> ProbExpr
apply subst (EVar nm) = lookupInSubst nm subst
apply _ (EConst i) = EConst i
apply subst (EExpct e) = EExpct (apply subst e)
apply subst (EBin op e1 e2) = EBin op (apply subst e1) (apply subst e2)

lookupInSubst :: String -> [(String, p)] -> p
lookupInSubst nm ((nm',v):rm)
 | nm == nm' = v
 | otherwise = lookupInSubst nm rm
lookupInSubst _ [] = error "Substitution was not complete, or free variables existed in the rhs of some equality"