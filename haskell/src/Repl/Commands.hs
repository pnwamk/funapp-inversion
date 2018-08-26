module Repl.Commands where

-- this module defines some simple data structures to
-- represent parsed commands from the user


import Types.LazyBDD
import Types.Subtype
import Types.Metafunctions

data Cmd =
  -- is t empty?
    Inhabited Ty
  -- is t1 a subtype of t2?
  | Subtype Ty Ty
  -- first projection of t
  | FstProj Ty
  -- second projection of t
  | SndProj Ty
  -- return type when applying t1 to t2
  | FunApp Ty Ty
  -- given a value of type t1 applied to a value of type t2,
  -- what must the argument have been if a value of t3 is
  -- produced?
  | FunInv Ty Ty Ty
  -- exit the Repl
  | Quit
  -- get help
  | Help
  deriving (Eq, Show, Ord)

no = "#false"
yes = "#true"
answerBool True = yes
answerBool False = no

answerMaybeTy Nothing = no
answerMaybeTy (Just t) = readBackTy t

execCmd :: Cmd -> String
execCmd (Inhabited t) = answerBool $ not $ isEmpty t
execCmd (Subtype t1 t2) = answerBool $ subtype t1 t2
execCmd (FstProj t) = answerMaybeTy $ fstProj t
execCmd (SndProj t) = answerMaybeTy $ sndProj t
execCmd (FunApp t1 t2) = answerMaybeTy $ rngTy t1 t2
execCmd (FunInv t1 t2 t3) = answerMaybeTy $ inTy t1 t2 t3
execCmd Quit = "Goodbye!"
execCmd Help = "No help yet... (TODO)"
