module Parser where

import Text.Parsec hiding ((<|>), many, optional)
import Text.Parsec.Combinator hiding (optional)
import Text.Parsec.String
import Text.Parsec.Token
import Text.Parsec.Char
import Data.Monoid
import Control.Applicative
import Control.Monad
import RewriteSystem

parseRuleFile :: FilePath -> IO ([(String, [String])], Rules Char)
parseRuleFile fp = do
     x <- parseFromFile entry fp
     case x of
       Left e -> error (show e)
       Right rs -> let ck = validate (snd rs)
                   in case ck of
                       ([], []) -> return rs
                       ([], xs) -> error $ "Not all positional place holders in RHS are in LHS, eg: 1<>a -> 1<>a<>2. \nAffected rules: " <> (show xs)
                       (xs, []) -> error $ "Positional place holders cannot be placed after each other, eg: 1<>2<>b -> b <> 1.\nAffected rules: " <> (show x)
                       (ds,ps) -> error $ "Positional place holders cannot be placed after each other, eg: 2<>1<>a -> 1<>a<>2\n Affected rules: " <> (show ds)
                                           <> "\n and not all place holders in RHS are in LHS, eg: 1<>2<>a -> 1<>b<>3\nAffected rules: " <> (show ps)


entry :: Parser ([(String, [String])], Rules Char)
entry = whiteSpace transformDef *> (reserved transformDef "start" *> ((,) [] <$> rules)) <|> transforms

transforms :: Parser ([(String, [String])], Rules Char)
transforms = do
    tr <-  manyTill (whiteSpace transformDef *> transform <* whiteSpace transformDef) $ reserved transformDef "start"
    whiteSpace transformDef
    rs <- rules
    return (tr, rs)



transform :: Parser (String, [String])
transform = (,) <$> (keys <* reservedOp transformDef ":") <*> values

values = do
     x <- identifier transformDef
     whiteSpace transformDef
     rest <- option [] (reservedOp transformDef "," *> values)
     return (x:rest)
keys = let res = reserved transformDef
       in res "transforms" *> return "transforms"

validate :: Rules Char -> ([Int], [Int])
validate (Rules xs) =  let (sp, pr) = unzip $ fmap work xs
                       in (fp $ sp `zip` [1..], fp $ pr `zip` [1..])
    where work (ls,rs) = (noSeqPos ls, posRsInLs ls rs)
          fp = fmap snd . filter (\(x,y) -> (not x))

noSeqPos :: [Match p] -> Bool
noSeqPos (x:y:xs) = not (bothPos x y) && noSeqPos (y:xs)
noSeqPos [x] = True
noSeqPos [] = True

posRsInLs :: Eq p => [Match p] -> [Match p] -> Bool
posRsInLs ls rs = let posses = filter fpos rs
                  in and $ fmap (`elem` ls) posses
   where fpos (Positional _) = True
         fpos _ = False
bothPos (Positional _) (Positional _) = True
bothPos _ _ = False

rules :: Parser (Rules Char)
rules = Rules <$> manyTill (whiteSpace rulesDef *> rule) eof

rule :: Parser ([Match Char], [Match Char])
rule = ((,) <$> rule1 <* reservedOp rulesDef "->") <*> rule1 <* optional newline

rule1 :: Parser [Match Char]
rule1 = try position <|> do
                            ids <- fmap Match <$> identifier rulesDef
                            whiteSpace transformDef
                            rest <- option [] (reservedOp rulesDef "<>" *> position)
                            return (ids <> rest)


position :: Parser [Match Char]
position = do
       x <- Positional <$> natural rulesDef
       rest <- option [] $ reservedOp rulesDef "<>" *> rule1
       return (x:rest)


transformDef :: TokenParser st
transformDef = makeTokenParser $ LanguageDef {
     commentStart = "{-",
     commentEnd = "-}",
     commentLine = "--",
     nestedComments = True,
     identStart = alphaNum,
     identLetter = alphaNum,
     opStart = oneOf ":.,",
     opLetter = oneOf "",
     reservedNames = ["transforms"],
     reservedOpNames = [":",",","."],
     caseSensitive = True

  }

rulesDef :: TokenParser st
rulesDef = makeTokenParser $ LanguageDef {
               commentStart = "{-",
               commentEnd = "-}",
               commentLine = "--",
               nestedComments = True,
               identStart = oneOf $ ['a' .. 'z'] <> ['A' .. 'Z'] <> ['0' .. '9'],
               identLetter = oneOf $ ['a' .. 'z'] <> ['A' .. 'Z'] <> ['0' .. '9'],
               opStart = oneOf "-,",
               opLetter = char '>',
               reservedNames = [],
               reservedOpNames = ["->", "<>"],
               caseSensitive = True
                 }
