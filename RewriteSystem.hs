{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances, StandaloneDeriving, MultiParamTypeClasses, TupleSections, TypeFamilies, GADTs, DataKinds, KindSignatures, ViewPatterns, ScopedTypeVariables #-}
module RewriteSystem where

import GHC.TypeLits
import Data.Maybe
import Data.List
import Data.Monoid
import Data.String
import Control.Applicative hiding (empty)
import qualified Control.Applicative as A
import qualified Data.Vector as V
import Test.QuickCheck
import Debug.Trace
import Data.Graph.Inductive hiding (empty)
import qualified Data.Graph.Inductive as I
import Control.Monad.State
import qualified Data.Set as S
import qualified Data.HashMap.Strict as M
import Data.Hashable
import Data.GraphViz
import Data.GraphViz.Attributes.Complete
import Data.Version
import Data.Graph.Inductive.Query
import Data.Graph.Analysis.Algorithms
import Control.Parallel.Strategies
import Control.DeepSeq

data RuleState = T | I
     deriving Show

data RuleTree (t :: RuleState) c where
   Initial :: [c] -> RuleTree I c
   Transformed :: [c] -> [RuleTree T c] -> RuleTree T c

instance NFData c => NFData (RuleTree t c) where
     rnf (Initial xs) = rnf xs
     rnf (Transformed xs ts) = rnf xs `seq` rnf ts

deriving instance Show c => Show (RuleTree t c)

data Rules c = Rules [([Match c], [Match c])]
data RuleType = P | M | E

instance Show c => Show (Rules c) where
  show (Rules xs) = unlines $ map show' xs
       where show' (x,y) = mconcat (show  `fmap`  x) ++ " -> " ++ mconcat (show `fmap` y)

data Match  c where
       Match :: c -> Match c
       Positional :: Integer -> Match c

instance Eq c => Eq (Match c) where
        (==) (Match p) (Match q) = p == q
        (==) (Positional p) (Positional q) = p == q
        (==) _ _ = False

instance NFData c => NFData (Match c) where
       rnf (Match c) = (rnf c) `seq` ()
       rnf (Positional i) = i `seq` ()




instance Show c => Show (Match c) where
    show (Match c) = show c
    show (Positional i) = "(" ++ show  i ++ ")"

data Side = LHS | RHS

data MatchProxy (q :: RuleType) c where
  MatchP :: c -> MatchProxy M c
  PositionalP :: Integer -> MatchProxy P c

class AddRule a (s :: Side) (t :: RuleType) (p :: RuleType) where
  (|>) :: MatchProxy t a -> RulesBuilder s (C p q) a -> RulesBuilder s (C t (C p q)) a

instance AddRule a LHS p E where
  (|>) = RuleAdd

instance AddRule a LHS M M where
  (|>) = RuleAdd

instance AddRule a LHS P M where
  (|>) = RuleAdd

instance AddRule a LHS M P where
  (|>) = RuleAdd

instance AddRule a RHS p q where
  (|>) = RuleAdd


ruleSystem :: [RulesBuilder p () c] -> Rules c
ruleSystem xs = Rules $ map (\(RulePair x y) -> (toRule x, toRule y)) xs


data C (p :: RuleType) q = CProxy

data RulesBuilder (s :: Side) p c where
    EndRule :: RulesBuilder s (C E ()) c
    RuleAdd :: MatchProxy x c -> RulesBuilder s r c -> RulesBuilder s (C x r) c
    RulePair :: RulesBuilder LHS (C x r) c -> RulesBuilder RHS t c -> RulesBuilder s () c

empty :: RulesBuilder p (C E ()) c
empty = EndRule

p :: Integer -> MatchProxy P c
p = PositionalP

c :: c -> MatchProxy M c
c = MatchP

(|->) :: RulesBuilder LHS (C x r) c -> RulesBuilder RHS t c -> RulesBuilder q () c
(|->) = RulePair

infixr 4 |->

infixr 5 |>
toRule :: RulesBuilder s p c -> [Match c]
toRule (RuleAdd x p) = case x of
                         MatchP c -> Match c : toRule p
                         PositionalP i -> Positional i : toRule p
toRule EndRule = []

type Axiom c = [c]

initialAxiom :: Axiom c -> RuleTree I c
initialAxiom = Initial

-- | Histomorphism like function to allow append to the results (Left  it as it is) or replace the topmost result (make it Right)
histo :: Alternative f => (a -> f b -> Either b (f b)) -> [a] -> f b -> f b
histo f (x:xs) z = histo f xs (zipEither . bimap ((<|>z).pure) id . f x $ z)
histo _ _ z = z

zipEither :: Either a a -> a
zipEither (Left a) = a
zipEither (Right a) = a

mergeRule :: [Match c] -> [Either Integer [c]]
mergeRule (Match x:xs) = case mergeRule xs of
                              (Right s : xs) -> Right (x:s) : xs
                              ts -> Right [x] : ts
mergeRule (Positional x:xs) = Left x : mergeRule xs
mergeRule [] = []

-- | bibind for either
--  f : a -> b + d, g : c -> b + d
--  p : a -> b, q : c -> d, s : a -> d, t : c -> b
--
--    a ------- p \/ s-------------\
--    | ia                         |
--   \|/                          \|/
--   a + c ------- f + g -----> b + d
--   /|\                          /|\
--    |                            |
--    | ic                         |
--    c ------- q \/ t ------------/
--
--    f + g .  ic = f + g . ia
--    p \/ s = f + g . i a
--    q \/ t = f + g . i c

-- | Bimap for either
bimap :: (a -> b) -> (c -> d) -> Either a c -> Either b d
bimap f g (Left a) = Left (f a)
bimap f g (Right c) = Right (g c)


-- | The idea is to form a template from the current string with the matches and positional parameters put into place.
-- Example:
--
-- 1 qq 2 -> 2 qq 1 and start point qq ss qq rr
-- action       |  rule    |  current template  | matches
-- store pos 1  | 1 qq 2   | \1         | {}
-- match qq     |  qq 2    | \1  m      | {{{},{qq},{ss qq rr}},{{qq,ss}, {qq}, {rr}}
-- store pos 2  | 2        | \1 m \2    | {}
--
-- Matching phase:
-- \1 m \2 <> {{{},{qq},{ss}}, {{qq, ss}, {qq}, {rr}}}
-- \1 -> {}, m -> {qq}, \2 -> {ss qq rr}
-- \1 -> {qq, ss}, m -> {qq}, \2 -> {rr}
-- Then apply the template.
-- PositionalHolder 1 {} (MatchHolder {qq} (PositionalHoler 2 {ss, qq, rr} End}
-- PositionalHolder 1 {qq, ss} (MatchHolder {qq} (PositionalHoler 2 {rr} End}
data TemplateState = Partial | Full

data Template (s :: TemplateState) c where
        PositionalHolder :: Integer -> [c] -> [c] -> Template Partial c -> Template Partial c
        MatchHolder :: [c] -> Template Partial c -> Template Partial c
        Template :: Template Partial c -> Template Full c
        EndTemplate :: Template Partial c

instance NFData c => NFData (Template x c) where
         rnf (PositionalHolder i cs xs tp) = i `seq` rnf cs `seq` rnf xs `seq` rnf tp `seq` ()
         rnf (MatchHolder c tp) = rnf c `seq` rnf tp `seq` ()
         rnf (Template tp) = rnf tp
         rnf (EndTemplate) = ()
deriving instance Show c => Show (Template s c)

replace :: (NFData a, Eq a) => a -> a -> [a] -> [a]
replace a r xs = parMap rdeepseq (\x -> ifp (x == a) r x) xs

orL :: [a] -> [a] -> [a]
orL [] xs = xs
orL xs [] = xs
orL a _ = a

transformSystem :: (NFData c, Eq c, Show c) =>
                  RuleTree I c -- ^ The initial axiom(s)
               -> Rules c -- ^ The rules of the rewrite system
               -> Maybe Integer -- ^ Maximal depth specification, Nothing means infinite.
               -> RuleTree T c -- ^ A potentially infinite tree with recursively transformed axiom
transformSystem ia rules@(Rules rs) = workerp ia rs
         where  -- workerp :: (Eq c, Show c) => RuleTree s c -> [([Match c], [Match c])] -> Maybe Integer -> RuleTree T c
                workerp (Initial ia) _ (Just 0) = Transformed ia []
                workerp (Initial ia) rs depth = let tps =  fmap (\(x,y) -> (,y) <$> (buildMatchTemplate' x ia)) rs
                                                in Transformed ia $ (\ia -> transformSystem ia rules (pred <$> depth))  <$> (map step =<< tps)
                step ((ls, tp, rs), ss) = Initial (applyTemplate ls rs tp ss)


applyTemplate :: (NFData c, Eq c, Show c) => [c] -> [c] -> Template Full c -> [Match c] -> [c]
applyTemplate ls rs (Template tp) inp = ls <> guardRights (walkTemplate tp (mergeRule inp)) <> rs

guardRights :: [Either a [b]] -> [b]
guardRights  = fromMaybe [] . foldr step (Just [])
             where step (Left i) (Just _) =  Nothing
                   step (Right xs) (Just z) = Just (xs ++ z)
                   step _ Nothing = Nothing

walkTemplate :: (NFData c, Eq c, Show c) => Template Partial c -> [Either Integer [c]] -> [Either Integer [c]]
walkTemplate (PositionalHolder i ls rs tp) inp = walkTemplate tp ( let x = replace (Left i) (Right $ let p = ls `orL` rs in  p) inp in x )
walkTemplate (MatchHolder _ tp) inp = walkTemplate tp inp
walkTemplate (EndTemplate) inp = inp

tplStrat :: NFData b => Strategy ([a],b,[a])
tplStrat = parTuple3 (evalList rseq) rdeepseq (evalList rseq)

-- | This works correctly
buildMatchTemplate' :: (NFData c, Eq c, Show c) => [Match c] -> [c] -> [([c],(Template Full c), [c])]
buildMatchTemplate' (mergeRule -> ss)  ds = let xs = worker ss ds in fmap (\(x,y,z) -> (x, Template y,z)) xs
     where worker (s:ss) ds = case s of
                                Right ts -> let matches = searchString ts ds
                                            in foldl (flip (step ss)) [] matches
                                Left i -> let xs = worker ss ds
                                          in  fmap (\(x,tp,y) -> ([], PositionalHolder i x y tp, [])) xs
           worker [] ds = [(ds, (EndTemplate), [])]
           step ss (ls, m, rs) z =
                       let xs = worker ss rs
                       in fmap (\ (rest, tp, rs) -> (ls, MatchHolder m tp, rest ++ rs)) xs ++ z


ifp :: Bool -> a -> a -> a
ifp p a b | p = a
          | otherwise = b


-- | Checks if we can apply a rule by finding an relevant substring
-- | and we return the rest to check if we only have a partial match
prematch :: (NFData c, Eq c) => [c] -> [c] -> Maybe ([c], [c], [c])
prematch = (listToMaybe .) . searchString


searchString :: (Eq c, NFData c) => [c] -> [c] -> [([c],[c],[c])]
searchString rs ds = cutout (V.length rs') ds' $ searchString' rs' ds'
   where rs' = V.fromList rs
         ds' = V.fromList ds

cutout :: (NFData c) => Int -> V.Vector c -> [(Int, Int)] -> [([c], [c], [c])]
cutout lm vs = parMap tplStrat (\(ib, ie) ->
          let prefix = V.take ib vs
              infixs = V.take lm $ V.drop ib vs
              suffix = V.drop (ie + 1) vs
          in (V.toList prefix, V.toList infixs, V.toList suffix))

-- This should be a faithful implementation of knuth search algorithm
searchString' :: (Eq c) => V.Vector c -> V.Vector c -> [(Int, Int)]
searchString' rs ds = let lrs = V.length rs
                          matchTable = V.toList $ V.findIndices (rs V.! 0==) ds
                      in join $ fmap (step lrs) matchTable
   where step lrs i  | i + lrs - 1 < V.length ds = ifp (foldr step' True [i .. i + lrs  - 1]) (pure (i, lrs + i - 1)) []
                      | otherwise = []
                  where step' ix =  ((rs V.! (ix - i) == ds V.! ix) &&)

{-- Rule tree to graph --}
type GraphState' c = (Int, M.HashMap [c] Int, M.HashMap Int (S.Set Int), Maybe Int)
type GraphState c = State (GraphState' c)

treeToDot :: (Labellable [c], Hashable c, Ord c) => RuleTree T c -> DotGraph Node
treeToDot rt = graphToDot dotParams $ toGraph rt


dotParams :: Labellable [c] => GraphvizParams Node [c] String () [c]
dotParams = defaultParams { fmtNode = \ (_,l) -> [toLabel l], fmtEdge = \ (_, _, l) -> [toLabel l], isDirected = True, globalAttributes = let x = globalAttributes nonClusteredParams in EdgeAttrs [Dir Back] : x}

mapToGraph :: GraphState' c -> Gr [c] String
mapToGraph (_, ntable, etable, _) = mkGraph ((\(x,y) -> (y,x)) <$> M.toList ntable) $ worker (M.toList etable)
             where worker ((k,sn):xs) = ((\x -> (k,x, "")) <$> (S.toList sn)) ++ worker xs
                   worker [] = []

toGraph :: (Hashable c, Eq c) => RuleTree T c -> Gr [c] String
toGraph (tr) = mapToGraph $ execState (toGraph' tr) (0 :: Int, M.empty, M.empty, Nothing)
   where toGraph' :: (Hashable c, Eq c) => RuleTree T c -> GraphState c ()
         toGraph' (Transformed cr trs) = do
                                            nn <- assignNumber cr
                                            connectEdges nn
                                            withParentNode nn $ forM_ trs toGraph'
         withParentNode :: Int -> GraphState c a -> GraphState c a
         withParentNode nn m = do
                    (nr, ntable, etable, pnode) <- get
                    put (nr, ntable, etable, Just nn)
                    a <- m
                    (nr, ntable, etable, _) <- get
                    put (nr, ntable, etable, pnode)
                    return a
         connectEdges :: Int -> GraphState c ()
         connectEdges nn = do
                       (nr, ntable, etable, pnode)  <- get
                       case pnode of
                          Nothing -> return ()
                          Just p -> case M.lookup nn etable of
                                          Nothing -> put (nr, ntable, M.insert nn (S.singleton p) etable, pnode)
                                          Just x -> put (nr, ntable, M.insert nn (S.insert p x) etable, pnode)
assignNumber :: (Eq c, Hashable c) => [c] -> GraphState c Int
assignNumber node = do
                       (nr, ntable, etable, pnode) <- get
                       case M.lookup node ntable of
                              Nothing -> put (succ nr, M.insert node nr ntable, etable, pnode) >> return nr
                              Just p -> return p


chunkParMap :: Int -> Strategy b -> (a -> b) -> [a] -> [b]
chunkParMap n strat f = withStrategy (parListChunk n strat) . map f

{-- Some tests --}

prop_searchStringValid = property test_searchStringValid

test_searchStringValid :: Int -> [String] -> Bool
test_searchStringValid ix xs = case searchString (show ix) (unwords (show ix : intersperse (show ix) xs)) of
                                 [] -> False
                                 [("", m, "")] -> m == show ix
                                 xs -> and $ check <$> xs

  where check (ls,m,rs) | m /= show ix = False
                        | otherwise = or ((\x -> x `isSuffixOf` ls || x `isSuffixOf` rs) <$> xs)

{-- Utility functions --}

saveAsDot:: (Hashable c, Labellable [c], Ord c) => FilePath -> RuleTree T c -> IO FilePath
saveAsDot fp tr = runGraphviz (treeToDot tr) DotOutput fp


saveAsXDot:: (Hashable c, Labellable [c], Ord c) => FilePath -> RuleTree T c -> IO FilePath
saveAsXDot fp tr = runGraphviz (treeToDot tr) (XDot (Just $ Version [1,4] [])) fp

{-- Analysis --}

transitiveClosure :: Gr c a -> Gr c String
transitiveClosure = emap (\x -> "") . trc

toDotWith f ts fp =  runGraphviz ( graphToDot dotParams $ f $ toGraph  ts ) DotOutput fp

{-- System --}

cyclicSystem :: Rules Char
cyclicSystem = ruleSystem [
       p 1 |> c 'p' |> p 2 |> c 'q' |> empty |-> c 't' |> p 1 |> p 2 |> empty,
       c 't' |> c 'p' |> p 1 |> empty |-> p 1 |> p 1 |> empty,
       c 'p' |> c 'p' |> empty |-> c 'p' |> c 't' |> empty,
       c 'p' |> c 'p' |> empty |-> c 't' |> c 'p' |> empty,
       c 'p' |> c 'p' |> empty |-> c 'q' |> empty,
       p 1 |> c 'q' |> c 't' |> p 2 |> empty |-> p 1 |> c 'q' |> p 2 |> c 't' |> p 2 |> c 't' |> p 1 |> empty,
       c 't' |> p 1 |> c 'q' |> empty |-> c 't' |> c 'q' |> empty,
       c 't' |> c 'q' |> empty |-> c 't' |> c 'p' |> c 'p' |> empty

   ]

testSystem :: Rules Char
testSystem = ruleSystem [
--   c 'c' |> empty |-> c 't' |> empty,
  c 't'  |> p 1 |> empty |-> p 1 |> p 1 |> c 'c' |> empty,
  c 'c' |> c 't' |> empty |-> c 'g' |> empty,
  c 'g' |> p 1 |> c 't' |> empty |-> c 'g' |> c 'a' |> empty,
  c 'a' |> p 1 |> c 'c' |> empty |->  c 't' |> p 1 |> empty,
  c 't' |> c 'a' |> p 1 |> c 'a' |> c 't' |> p 2 |> empty |-> p 2 |> p 1 |> empty
  ]
