module Repl.Parse ( parseCmd , parseTy ) where

-- this module defines tools for parsing user input
-- (or input from a Racket process) whose grammar
-- is s-expression based

import qualified Types.Syntax as Stx
import qualified Types.LazyBDD as BDD
import Types.NumericTower
import Repl.Commands
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Char
import Data.Graph (Graph)
import qualified Data.Graph as Graph

-- what characters, aside from AlphaNums, are valid in symbols
allowedChars :: String
allowedChars = "-_+=~!@$%^&*"


-- reads the next identifier from the buffer, returning
-- (sym, rest) where sym is the parsed symbol and rest is
-- the input string after sym.
parseSym :: String -> Either String (String, String)
parseSym str = aux (skipSpace str) []
  where aux [] revSym
          | revSym == [] = Left $ "no characters to read"
          | otherwise = Right (reverse revSym, [])
        aux input@(c:rest) revSym
          -- if we hit a delimiter, return the symbol w/o consuming it
          | isSpace c || c == '(' || c == ')' = Right (reverse revSym, input)
          -- add a valid character to the symbol we're accumulating
          | isAlphaNum c || (any (== c) allowedChars) = aux rest (c:revSym)
          -- unrecognized symbol, error
          | otherwise = Left $
                        "invalid identifier symbol "
                        ++ [c] ++
                        if revSym == []
                        then ""
                        else "after reading " ++ (reverse revSym)



-- trims white space from the left of the given string
skipSpace :: String -> String
skipSpace [] = []
skipSpace str@(c:cs)
  | isSpace c = skipSpace cs
  | otherwise = str


parseCmd :: BDD.Env -> String -> Either String Cmd
parseCmd env [] = Left $ "no command to parse"
parseCmd env (c:body)
  | isSpace c = parseCmd env body
  | c == '(' = do
      (sym, rest) <- parseSym body
      case sym of
        "Inhabited" -> do
          (ts, rest') <- parseTyList env rest
          case ts of
            [t] -> Right $ Inhabited t
            _   -> Left $ "Inhabited command requires 1 argument, given " ++ (show ts)
        "Subtype" -> do
          (ts, rest') <- parseTyList env rest
          case ts of
            [t1, t2] -> Right $ Subtype t1 t2
            _   -> Left $  "Subtype command requires 2 arguments, given " ++ (show ts)
        "Project" -> do
          (i, rest') <- parseSym rest
          case i of
            "1" -> do
              (ts, _) <- parseTyList env rest'
              case ts of
                [t] -> Right $ FstProj t
                _ -> Left $ "Project expects one type after index, given " ++ (show ts)
            "2" -> do
              (ts, _) <- parseTyList env rest'
              case ts of
                [t] -> Right $ SndProj t
                _ -> Left $ "Project expects one type after index, given " ++ (show ts)
            _ -> Left $ "Project requires an index of 1 or 2, given " ++ i 
        "Apply" -> do
          (ts, rest') <- parseTyList env rest
          case ts of
            [t1, t2] -> Right $ FunApp t1 t2
            _   -> Left $ "Apply command requires 2 arguments, given " ++ (show ts)
        "Inversion" -> do
          (ts, rest') <- parseTyList env rest
          case ts of
            [t1, t2, t3] -> Right $ FunInv t1 t2 t3
            _   -> Left $ "Inversion command requires 3 arguments, given " ++ (show ts)
        "Let" -> do
          (name, rest') <- parseSym rest
          case BDD.resolve name env of
            Nothing -> do
              (ts, _) <- parseTyList env rest'
              case ts of
                [t] -> Right $ Let name t
                _ -> Left $ "expected one type after name in Let, found " ++ (show ts)
            Just t -> Left $ "cannot redefine type name " ++ name ++ "(i.e. it is already defined)"
        "LetRec" -> do
          (bindings, _) <- parseLetRec env rest
          validateLetRecBindings bindings
        _ -> Left $ "invalid Command: " ++ sym


parseTyList :: BDD.Env -> String -> Either String ([BDD.Ty], String)
parseTyList env inputStr = parseList inputStr mkOr mkAnd mkNot mkProd mkArrow mkName
  where mkOr ts = BDD.tyOr' ts
        mkAnd ts = BDD.tyAnd' ts
        mkNot t = BDD.tyNot t
        mkProd t1 t2 = BDD.prodTy t1 t2
        mkArrow t1 t2 = BDD.arrowTy t1 t2
        mkName name = BDD.resolve name env

parseTy :: BDD.Env -> String -> Either String (BDD.Ty, String)
parseTy env inputStr = parseSingle inputStr mkOr mkAnd mkNot mkProd mkArrow mkName
  where mkOr ts = BDD.tyOr' ts
        mkAnd ts = BDD.tyAnd' ts
        mkNot t = BDD.tyNot t
        mkProd t1 t2 = BDD.prodTy t1 t2
        mkArrow t1 t2 = BDD.arrowTy t1 t2
        mkName name = BDD.resolve name env

-- makes sure (mutually) recursive LetRec bindings are all
-- productive (i.e. the values they describe are finite and
-- sensical) by parsing them into a graph and ensuring their
-- are no cyclic strongly connected components
validateLetRecBindings :: (Map String Stx.Ty) -> Either String Cmd
validateLetRecBindings bindings = case [names | (Graph.CyclicSCC names) <- sccs] of
                                    [] -> Right $ LetRec bindings
                                    (names:_) -> Left $ "invalid cycle found in LetRec: " ++ show names
  where sccs = Graph.stronglyConnComp $ map nodeInfo nodes
        nodeInfo :: String -> (String, String, [String])
        nodeInfo name = (name, name, Set.toList $ neighbors $ bindings Map.! name)          
        nodes :: [String]
        nodes = Map.keys bindings
        neighbors :: Stx.Ty -> Set String
        neighbors (Stx.Name name)
          | Map.member name bindings = Set.singleton name
          | otherwise = Set.empty
        neighbors (Stx.Or ts)  = foldr (\t ns -> Set.union ns $ neighbors t) Set.empty ts
        neighbors (Stx.And ts) = foldr (\t ns -> Set.union ns $ neighbors t) Set.empty ts
        neighbors (Stx.Not t) = neighbors t
        neighbors _ = Set.empty

-- parses each name/rhs clause in a LetRec
parseLetRec :: BDD.Env -> String -> Either String ((Map String Stx.Ty), String)
parseLetRec env [] = Left "failed to parse LetRec bindings (they ended abruptly!)"
parseLetRec env (c:rest)
  | isSpace c = parseLetRec env rest
  | not $ c == '(' = Left $ "expected to find a left parenthesis, found " ++ [c]
  | otherwise = do
      (rawBindings, rest') <- parseBindings env rest
      parsedBindings <- Map.foldrWithKey (parseRhs (Map.keysSet rawBindings)) (Right Map.empty) rawBindings
      Right (parsedBindings, rest')
        where parseRhs :: Set String -> String -> String -> Either String (Map String Stx.Ty) -> Either String (Map String Stx.Ty)
              parseRhs bound name rhs maybeParsed = do
                (t, _) <- parseStx env bound rhs
                parsed <- maybeParsed
                Right $ Map.insert name t parsed

-- after seeing `(LetRec`, this function is called to
-- initially parse the bindings ((name rhs) ...), HOWEVER
-- the rhss are left unparsed (note they are a String and
-- not a Stx.Ty) so that we can wait to parse them until all
-- of the names being bound by the LetRec have been
-- identified
parseBindings :: BDD.Env -> String -> Either String ((Map String String), String)
parseBindings env [] = Left "failed to parse LetRec bindings (they ended abruptly!)"
parseBindings env (c:rest)
  | isSpace c = parseBindings env rest
  | c == '(' = do
      (name, rhs, rest') <- parseBinding env rest
      (bindings, rest'') <- parseBindings env rest'
      if Map.member name bindings
        then Left $ "duplicate entries given in LetRec bindings for " ++ name
        else Right (Map.insert name rhs bindings, rest'')
  | c == ')' = Right (Map.empty, [])
  | otherwise = Left $ "invalid character in LetRec binding sequence: " ++ [c]


-- parses a single (name rhs) in a LetRec binding (after the
-- initial `(` has already been seen), returning (name, rhs,
-- rest) where rhs is the _unparsed_ rhs (i.e. a String not
-- a Stx.Ty so we can parse them later once we have all the
-- names being bound by the LetRec identified)
parseBinding :: BDD.Env -> String -> Either String (String, String, String)
parseBinding env input = do
  (name, rest) <- parseSym input
  if (BDD.envMember name env)
    then Left $ "name is already bound in environment: " ++ name
    else do
    (rhs, rest') <- parseNextSexp rest
    case (skipSpace rest') of
      (')':rest'') -> Right (name, rhs, rest'')
      _ -> Left "invalid end to LetRec rhs (i.e. no right parenthesis found)"

-- read the next sexpression from stdin, return the rest of the string
parseNextSexp :: String -> Either String (String, String)
parseNextSexp inputStr = aux inputStr [] 0
  where aux :: String -> String -> Int -> Either String (String, String)
        aux (c:rest) [] 0
          | c == '(' = aux rest "(" 1
          | isSpace c = aux rest [] 0
          | isAlphaNum c || (any (== c) allowedChars) = parseSym (c:rest)
          | otherwise = Left "invalid LetRec rhs"
        aux (')':_) rbuff 0 = Left "unexpected right parenthesis in LetRec binding rhs"
        aux (')':rest) rbuff 1 = Right $ (reverse (')':rbuff), rest)
        aux (')':rst) rbuff depth = aux rst (')':rbuff) (depth-1)
        aux ('(':rst) rbuff depth = aux rst ('(':rbuff) (depth+1)
        aux (c:rst) rbuff depth = aux rst (c:rbuff) depth
        aux [] _ _ = Left "unexpected end of string while parsing LetRec rhs"

-- used to parse LetRecs, i.e. we first parse the bodies
-- into Types.Syntax types so we can ensure they are all
-- productive types, then we can use Haskell's
-- laziness/mutual recursion to extend the environment with
-- all of the types simultaneously
parseStx :: BDD.Env -> Set String -> String -> Either String (Stx.Ty, String)
parseStx env bound inputStr = parseSingle inputStr Stx.Or Stx.And Stx.Not Stx.Prod Stx.Arrow mkName
  where mkName name =
          case BDD.resolve name env of
            Nothing -> if Set.member name bound
                       then Just $ Stx.Name name
                       else  Nothing
            Just t -> Just $ Stx.Name name


parseList ::
  (Show a, Ord a, Eq a) =>
  String ->
  ([a] -> a) -> -- Or constructor
  ([a] -> a) -> -- And constructor
  (a -> a) -> -- Not constructor
  (a -> a -> a) -> -- Prod constructor
  (a -> a -> a) -> -- Arrow constructor
  (String -> Maybe a) -> -- how to handle type names
  Either String ([a], String)
parseList initial (mkOr) mkAnd mkNot mkProd mkArrow mkName = aux initial
  where aux [] = Left $ "end of input string, no closing parenthesis"
        aux (')':rest) = Right ([], rest)
        aux str@(c:rest)
          | isSpace c = aux rest
          | otherwise = do
              (t, rest') <- single str
              (ts, rest'') <- aux rest'
              return (t:ts, rest'')
                where single str = parseSingle str mkOr mkAnd mkNot mkProd mkArrow mkName

parseSingle ::
  (Show a, Ord a, Eq a) =>
  String ->
  ([a] -> a) -> -- Or constructor
  ([a] -> a) -> -- And constructor
  (a -> a) -> -- Not constructor
  (a -> a -> a) -> -- Prod constructor
  (a -> a -> a) -> -- Arrow constructor
  (String -> Maybe a) -> -- how to handle type names
  Either String (a, String)
parseSingle input mkOr mkAnd mkNot mkProd mkArrow mkName =
  let single str = parseSingle str mkOr mkAnd mkNot mkProd mkArrow mkName
      multi  str = parseList str mkOr mkAnd mkNot mkProd mkArrow mkName in
    case input of
      [] -> Left $ "no type to parse"
      (c:body) 
        | isSpace c -> single body
        | c == '(' -> do
            (sym, rest) <- parseSym body
            case sym of
              "Or" -> do
                (ts, rest') <- multi rest
                Right (mkOr ts, rest')
              "And" -> do
                (ts, rest') <- multi rest
                Right (mkAnd ts, rest')
              "Not" -> do
                (ts, rest') <- multi rest
                case ts of
                  [t] -> Right (mkNot t, rest')
                  _   -> Left $ "Not requires 1 argument, given " ++ (show ts)
              "Prod" -> do
                (ts, rest') <- multi rest
                case ts of
                  [t1, t2] -> Right (mkProd t1 t2, rest')
                  _   -> Left $ "Prod requires 2 arguments, given " ++ (show ts)
              "Arrow" -> do
                (ts, rest') <- multi rest
                case ts of
                  [t1, t2] -> Right (mkArrow t1 t2, rest')
                  _   -> Left $ "Arrow requires 2 arguments, given " ++ (show ts)
              _ -> Left $ "invalid type constructor: " ++ sym
        | c == ')' -> Left $ "unexpected right parenthesis"
        | otherwise -> do
            (sym, rest) <- parseSym input
            case mkName sym of
              Nothing -> Left $ "unrecognized type name: " ++ sym
              Just t -> Right (t, rest)

