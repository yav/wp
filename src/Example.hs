{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
import WP
import Data.String
import Text.PrettyPrint
import qualified Data.Map as Map

data Example

instance Language Example where
  type ConnSym Example = Sym
  type PredSym Example = Sym
  type FunSym  Example = Sym
  type VarSym  Example = Sym
  type Label   Example = Sym

  equalSym _         = "=="
  invariantSym _ x y = S $ show $ text "Inv_" <> pp x <> text "_" <> pp y
  okSym _ x          = S $ show $ text "Ok_" <> pp x
  conjSym _          = "/\\"
  impliesSym _       = "=>"
  trueSym _          = "true"






newtype Sym = S String
              deriving (Eq,Ord)



instance IsString Sym where
  fromString = S

instance IsSym Sym where
  symFixity (S x) =
    case x of
      "=="  -> Infix AssocNone  4
      "<"   -> Infix AssocNone  4
      "=>"  -> Infix AssocRight 2
      "/\\" -> Infix AssocRight 3
      "-"   -> Infix AssocLeft  6
      "+"   -> Infix AssocLeft  6
      _     -> Prefix

instance PP Sym where
  ppPrec _ (S x) = text x


example :: Function Example
example = setPredecessors Function
            { blocks = Map.fromList
                [ ("Start",    blk (Assume (Pred "PRECONDITION" []))
                                       [ "LoopHead" ])

                , ("LoopHead", blk Skip
                                       [  "Body",  "After" ])

                , ("Body",     blk (Assume (lt (num 0) x) :::
                                        ("x" := sub x (num 1))
                                   ) [ "LoopHead" ])

                , ("After",    blk (Assume (pNot (lt (num 0) x)) :::
                                        ("r"  := x) :::
                                        Assert (Pred "POSCONDITION" [])
                                        ) [])
                ]
            , entry = "Start"
            , predecessors = error "predecessors"
            }

  where
  blk x y = Block { blockStmt = x, blockNext = y }

  x       = EVar "x" :: Expr Example
  num i   = Fun (fromString (show (i::Integer))) [] :: Expr Example
  lt  x y = Pred "<" [x,y] :: Prop Example
  sub x y = Fun "-" [x,y] :: Expr Example
  pNot p  = Conn "Not" [p] :: Prop Example




