module Repl.Commands where

-- this module defines some simple data structures to
-- represent parsed commands from the user


import Types.LazyBDD

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
