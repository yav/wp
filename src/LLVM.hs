{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module LLVM where

import WP

import qualified Text.LLVM.AST as LLVM
import Text.LLVM.AST hiding (Stmt)

import Data.Maybe(fromMaybe)

import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Map (Map)
import qualified Data.Map as Map
import MonadLib (Id,ExceptionT,StateT,sets_,raise
                , runId, runExceptionT, runStateT )

import Data.LLVM.BitCode
import Text.PrettyPrint
import Data.List(intersperse)




data Var    = Var Ident Type
            | RetVal
            | Mem
              deriving (Eq,Ord)


data Fun    = Value Value Type      -- ^ Does not contain 'Ident'
            | ArithOp ArithOp
            | BitOp BitOp
            | ConvTo ConvOp Type    -- ^ Convet to this type

            | ReadMem Align
            | WriteMem Align

            | ICmpOp ICmpOp
            | FCmpOp FCmpOp

data Conn   = CAnd | CTrue | CImplies
data Pred   = POk Lab
            | PInv Lab Lab
            | PEq

data Lab    = NoName
            | Lab BlockLabel
            | NewLabel Int
              deriving (Eq,Ord)


instance PP Var where
  ppPrec _ var = case var of
                   Var x _ -> ppIdent x
                   RetVal  -> text "__retval"
                   Mem     -> text "__mem"


instance PP Fun where
  ppPrec _ fun =
    case fun of
      Value v _   -> ppValue v
      ArithOp o   -> ppArithOp o
      BitOp b     -> ppBitOp b
      ConvTo p t  -> parens (ppConvOp p <+> text " to " <+> ppType t)

      ReadMem _a  -> text "read_mem"
      WriteMem _a -> text "write_mem"

      ICmpOp p -> ppICmpOp p
      FCmpOp p -> ppFCmpOp p

instance PP Conn where
  ppPrec _ conn =
    case conn of
      CAnd  -> text "/\\"
      CTrue -> text "True"
      CImplies -> text "=>"

instance PP Pred where
  ppPrec _ pred =
    case pred of
      POk l -> text "Ok_" <> pp l
      PInv l1 l2 -> text "inv_" <> pp l1 <> text "_" <> pp l2
      PEq   -> text "=="

instance PP Lab where
  ppPrec _ l =
    case l of
      NoName      -> text "__anon__"
      Lab b       -> ppLabel b
      NewLabel i  -> text "__new_label_" <> int i

instance IsSym Fun where
  symFixity _ = Prefix

instance IsSym Pred where
  symFixity PEq = Infix AssocNone 4
  symFixity _   = Prefix

instance IsSym Conn where
  symFixity CImplies = Infix AssocRight 2
  symFixity CAnd     = Infix AssocRight 3
  symFixity _        = Prefix


data LLVM

instance Language LLVM where
  type ConnSym LLVM = Conn
  type PredSym LLVM = Pred
  type FunSym  LLVM = Fun
  type VarSym  LLVM = Var
  type Label   LLVM = Lab

  equalSym     _ = PEq
  invariantSym _ = PInv
  okSym        _ = POk
  conjSym      _ = CAnd
  impliesSym   _ = CImplies
  trueSym      _ = CTrue




--------------------------------------------------------------------------------
type ConvM = ExceptionT String (StateT ConvS Id)

data ConvS = ConvS { phis  :: Map BlockLabel (Stmt LLVM)
                   , nexts :: Set Lab
                   , newBlocks :: [(Lab, Block LLVM)]
                   , nextBlockName :: !Int
                   }

runConvM :: ConvM () -> Either String ( [(Lab,Block LLVM)]
                                      , Map BlockLabel (Stmt LLVM)
                                      )
runConvM m = case runId $ runStateT s0 $ runExceptionT m of
               (Left err, _) -> Left err
               (Right _, s)  -> Right ( reverse (newBlocks s), phis s )
  where
  s0 = ConvS { phis = Map.empty
             , nexts = Set.empty
             , newBlocks = []
             , nextBlockName = 0
             }

unsupported :: String -> ConvM a
unsupported x = raise ("TODO: " ++ x)

invalid :: String -> ConvM a
invalid x = raise ("ERROR: " ++ x)

addPhi :: (BlockLabel, Stmt LLVM) -> ConvM ()
addPhi (x,s) = sets_ $ \ConvS { .. } ->
                        ConvS { phis = Map.insertWith (:::) x s phis
                              , .. }

addNext :: BlockLabel -> ConvM ()
addNext l = sets_ $ \ConvS { .. } -> ConvS { nexts = Set.insert (Lab l) nexts
                                           , .. }

addAsmpBlock :: BlockLabel -> Prop LLVM -> ConvM ()
addAsmpBlock l p = sets_ $
  \ConvS { .. } ->
   ConvS { newBlocks = (NewLabel nextBlockName,
                                  Block { blockStmt = Assume p
                                        , blockNext = [ Lab l ]
                                        }) :  newBlocks
         , nextBlockName = 1 + nextBlockName
         , nexts = Set.insert (NewLabel nextBlockName) nexts
         , ..
         }

finishBB :: Lab -> Stmt LLVM -> ConvM ()
finishBB l s = sets_ $
  \ConvS { .. } ->
   ConvS { nexts = Set.empty
         , newBlocks = (l, b nexts) : newBlocks
         , .. }
  where
  b ns = Block { blockNext = Set.toList ns, blockStmt = s }



--------------------------------------------------------------------------------

class HasType t where
  getType :: t -> Type

instance HasType Type where
  getType = id

instance HasType (Typed a) where
  getType = typedType


var :: HasType t => Ident -> t -> Var
var x t = Var x (getType t)

value :: Typed Value -> Expr LLVM
value Typed { .. } =
  case typedValue of
    ValIdent i -> EVar (var i typedType)
    _          -> Fun (Value typedValue typedType) []


valBool :: Bool -> Expr LLVM
valBool b = Fun (Value (ValBool b) (PrimType (Integer 1))) []


bin :: Fun -> Typed Value -> Value -> Expr LLVM
bin f x y = Fun f [ value x, value x { typedValue = y } ]

uni :: Fun -> Typed Value -> Expr LLVM
uni f x = Fun f [ value x ]



main :: IO ()
main =
  do mb <- parseBitCodeFromFile "test.bc"
     case mb of
       Right a ->
        case convModule a of
          Left err -> fail err
          Right fs -> print $ vcat $ intersperse (text " ") $ map pp fs
       Left err -> fail (show err)





convModule :: Module -> Either String [ Function LLVM ]
convModule Module { .. } = mapM convDefine modDefines




convDefine :: Define -> Either String (Function LLVM)
convDefine Define { .. } =
  case runConvM (mapM_ convBB defBody) of
    Left err -> Left err
    Right (bs,phs) ->
      case filter notNew (map fst bs) of
        [] -> Left "Missiing entry"
        l : _ ->
           Right $ setPredecessors
                   Function { entry = l
                            , blocks = Map.mapWithKey (addPhis phs)
                                     $ Map.fromList bs
                            , predecessors = error "predecessors"
                            }
  where
  notNew (NewLabel _) = False
  notNew _            = True

  addPhis phs (Lab k) b = case Map.lookup k phs of
                            Nothing -> dropSkipsInBlock b
                            Just s  -> dropSkipsInBlock
                                           b { blockStmt = blockStmt b ::: s }
  addPhis _ _ b = dropSkipsInBlock b

convBB :: BasicBlock -> ConvM ()
convBB BasicBlock { .. } =
  do ss <- mapM convStmt bbStmts
     let name = maybe NoName Lab bbLabel
         s    = case ss of
                  [] -> Skip
                  _  -> foldr1 (:::) ss
     finishBB name s


convStmt :: LLVM.Stmt -> ConvM (Stmt LLVM)
convStmt (Effect i _)   = convInstr Nothing i
convStmt (Result x i _) = convInstr (Just x) i

convInstr :: Maybe Ident -> Instr -> ConvM (Stmt LLVM)
convInstr mb instr =
  case (mb,instr) of
    (Nothing,Ret v)        -> return (RetVal := value v)
    (Just _,Ret {})        -> invalid "Ret with a value?"

    (Nothing,RetVoid)      -> return Skip
    (Just _,RetVoid)       -> invalid "RetVoid with a value?"

    (Nothing, Arith {})    -> invalid "Arith op with no result"
    (Just i, Arith op x y) -> return $
        checks ::: var i x := bin (ArithOp op) x y
      where checks = Skip -- XXX: add checks

    (Nothing, Bit {}) -> invalid "Bit op with no result"
    (Just i, Bit op x y) -> return $
        checks ::: var i x := bin (BitOp op) x y
      where checks = Skip -- XXX: add checks

    (Nothing, Conv {}) -> invalid "Conv with no result"
    (Just i, Conv op x t ) -> return $
        checks ::: var i t := uni (ConvTo op t) x
      where checks = Skip -- XXX: add checks

{-
    ( _, Call _ retT f ps ) -> undefined -- XXX
        -- assert pre of ps and some other params, but which ones
        -- assume post of f, including the result (in mb), if any
        -- What to do if function is not a symbol?
-}

    -- (Just i, Alloca t mbN mbA) -> return $


    (Nothing, Load {}) -> invalid "Load with no result"
    (Just i, Load p mbA) ->
      case typedType p of
        PtrTo t -> return $
          checks ::: var i t := Fun (ReadMem (fromMaybe 1 mbA))
                                    [ EVar Mem, value p ]
            where checks = Skip -- XXX: add checks
        _     -> unsupported "type error: not a pointer in Load"

    (Just _, Store {}) -> invalid "Store with result"
    (Nothing, Store v p mbA) -> return $
       checks ::: Mem := Fun (WriteMem (fromMaybe 1 mbA))
                             [ EVar Mem, value p, value v ]
       where checks = Skip -- XXX: add checks

    (Just i, ICmp cmp x y) -> return $ var i x := bin (ICmpOp cmp) x y
    (Nothing, ICmp {})     -> invalid "ICmp with no result"

    (Just i, FCmp cmp x y) -> return $ var i x := bin (FCmpOp cmp) x y
    (Nothing, FCmp {})     -> invalid "FCmp with no result"

    (Just i, Phi t vs) ->
      do mapM_ addPhi [ (l, var i t := value Typed { typedValue = v
                                                   , typedType = t })
                          | (v,l) <- vs ]
         return Skip
    (Nothing, Phi {}) -> invalid "Phi with no result"



    (Nothing, GEP {}) -> invalid "GEP with no result"
    (Just _, GEP {})  -> unsupported "GEP"

{-
    (Just _, GEP check p ixes) ->
      case 

      where checks = Skip -- XXX: add checks
-}

    (Nothing, Jump l) -> addNext l >> return Skip
    (Just _, Jump _)  -> invalid "Jump: result"

    (Nothing, Br v l1 l2) ->
       do addAsmpBlock l1 (value v === valBool True)
          addAsmpBlock l2 (value v === valBool False)
          return Skip


    (Just _, Br {}) -> invalid "Br: result"







