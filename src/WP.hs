{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}
module WP where

import           Data.Map ( Map )
import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.Maybe ( catMaybes )
import           Data.List (unfoldr,intersperse,delete)
import           MonadLib (StateT, Id, runStateT, runId, sets, sets_, liftM2)

import           Text.PrettyPrint ( Doc,($$),(<>),(<+>), fsep
                                  , text,vcat,hsep,nest,colon,parens,int )
import           GHC.Exts(Constraint)
import           Data.Proxy


infix  4 ===
infixr 3 /\
infixr 2 ==>

infix  2 :=
infixr 1 :::




--------------------------------------------------------------------------------


analyze :: Language l => Function l -> Map (Label l) (Prop (DSA l))
analyze = progEqns . passifyFunction . toDSA . removeLoops


class (Ord (VarSym l), Ord (Label l)) => Language l where
  type ConnSym l
  type PredSym l
  type FunSym  l
  type VarSym  l
  type Label   l

  equalSym     :: proxy l -> PredSym l
  invariantSym :: proxy l -> Label l -> Label l -> PredSym l
  okSym        :: proxy l -> Label l -> PredSym l
  conjSym      :: proxy l -> ConnSym l
  impliesSym   :: proxy l -> ConnSym l
  trueSym      :: proxy l -> ConnSym l


withLang :: (Proxy l -> thing l) -> thing l
withLang k = k Proxy

(===) :: Language l => Expr l -> Expr l -> Prop l
x === y  = withLang $ \l -> Pred (equalSym l) [x,y]

invariant :: Language l => Label l -> Label l -> Prop l
invariant x y = withLang $ \l -> Pred (invariantSym l x y) []

ok :: Language l => Label l -> Prop l
ok x = withLang $ \l -> Pred (okSym l x) []

(/\) :: Language l => Prop l -> Prop l -> Prop l
x /\ y = withLang $ \l -> Conn (conjSym l) [x,y]

(==>) :: Language l => Prop l -> Prop l -> Prop l
x ==> y = withLang $ \l -> Conn (impliesSym l) [x,y]

true :: Language l => Prop l
true = withLang $ \l -> Conn (trueSym l) []

conj :: Language l => [Prop l] -> Prop l
conj [] = true
conj xs = foldr1 (/\) xs




data DSA l

proxyParam :: proxy (f l) -> Proxy l
proxyParam _ = Proxy

instance Language l => Language (DSA l) where
  type ConnSym (DSA l) = ConnSym l
  type PredSym (DSA l) = PredSym l
  type FunSym  (DSA l) = FunSym l
  type VarSym  (DSA l) = Inst (VarSym l)
  type Label   (DSA l) = Label l

  equalSym     = equalSym     . proxyParam
  invariantSym = invariantSym . proxyParam
  okSym        = okSym        . proxyParam
  conjSym      = conjSym      . proxyParam
  impliesSym   = impliesSym   . proxyParam
  trueSym      = trueSym      . proxyParam





data Inst i = Inst i Int
              deriving (Show,Eq,Ord)




data Function l = Function
  { entry        :: Label l
  , blocks       :: Map (Label l) (Block l)

  , predecessors :: Map (Label l) [Label l]
    -- ^ Can be computed from the rest of the graph.
    -- Store here to make going back-wards easier.
  }

-- | Compute a mapping from blocks to their predecessors.
setPredecessors :: Ord (Label l) => Function l -> Function l
setPredecessors Function { .. } =
  Function { predecessors = Map.insertWith (\_ old -> old) entry []
                         $ foldr addBlock Map.empty (Map.toList blocks)
          , ..
          }
  where
  addBlock (b,Block { .. }) m = foldr (addEdgeTo b) m blockNext
  addEdgeTo fromId toId       = Map.insertWith (++) toId [fromId]




data Block l = Block { blockStmt :: Stmt l, blockNext :: [ Label l ] }



data Expr l = Fun (FunSym l) [Expr l]   | EVar (VarSym l)
data Prop l = Pred (PredSym l) [Expr l] | Conn (ConnSym l) [Prop l]
data Stmt l = VarSym l := Expr l
            | Havoc (VarSym l)
            | Assert (Prop l)
            | Assume (Prop l)
            | Stmt l ::: Stmt l
            | Skip

deriving instance (CtrAll Show l) => Show (Expr l)
deriving instance (CtrAll Show l) => Show (Prop l)
deriving instance (CtrAll Show l) => Show (Stmt l)
deriving instance (CtrAll Show l) => Show (Block l)
deriving instance (CtrAll Show l) => Show (Function l)

type CtrAll (c :: * -> Constraint) l =
  ( c (FunSym l)
  , c (VarSym l)
  , c (ConnSym l)
  , c (PredSym l)
  , c (Label l)
  )



--------------------------------------------------------------------------------
class IsSym c where
  symFixity :: c -> Fixity

data Fixity = Prefix | Infix Assoc Int
data Assoc  = AssocNone | AssocLeft | AssocRight

type PPLang l = ( CtrAll PP l
                , IsSym (PredSym l)
                , IsSym (ConnSym l)
                , IsSym (FunSym l)
                )


class PP a where
  ppPrec :: Int -> a -> Doc

ppIO :: PP a => a -> IO ()
ppIO = print . pp

pp :: PP a => a -> Doc
pp = ppPrec 0

ppFun :: (PP a, PP f, IsSym f) => Int -> f -> [a] -> Doc
ppFun prec f es
  | Infix assoc opPrec <- symFixity f =
    case es of
      [x,y]        -> wrapAt opPrec prec (ppInf assoc opPrec x y)
      x : y : more -> ppPrefix (parens (ppInf assoc opPrec x y)) more
      _            -> ppPrefix (parens (pp f)) es

  | otherwise = ppPrefix (pp f) es
  where
  ppInf opAssoc opPrec x y =
    let (rP,lP) = case opAssoc of
                    AssocNone  -> (opPrec + 1, opPrec + 1)
                    AssocLeft  -> (opPrec, opPrec + 1)
                    AssocRight -> (opPrec + 1, opPrec)

    in ppPrec rP  x <+> pp f <+> ppPrec lP y

  ppPrefix f' []  = f'
  ppPrefix f' es' = wrapAt 10 prec (f' <+> fsep (map (ppPrec 11) es'))


wrapAt :: Int -> Int -> Doc -> Doc
wrapAt goal prec d = if prec > goal then parens d else d


instance (PP k, PP a) => PP (Map k a) where
  ppPrec _ = vcat . intersperse (text " ") . map ppB . Map.toList
    where
    ppB (x,y) = (pp x <> colon) $$ nest 2 (pp y)


instance PP i => PP (Inst i) where
  ppPrec _ (Inst x y) = pp x <> text "_" <> int y

instance PPLang l => PP (Stmt l) where
  ppPrec _ stmt =
    case stmt of
      i := e    -> pp i <+> text "=" <+> pp e
      Havoc i   -> text "havoc" <+> pp i
      Assert e  -> text "assert" <+> pp e
      Assume e  -> text "assume" <+> pp e
      s1 ::: s2 -> pp s1 $$ pp s2
      Skip      -> text "skip"

instance PPLang l => PP (Expr l) where
  ppPrec prec expr =
    case expr of
      EVar i    -> pp i
      Fun f es  -> ppFun prec f es

instance PPLang l => PP (Prop l) where
  ppPrec prec prop =
    case prop of
      Pred f es     -> ppFun prec f es
      Conn f es     -> ppFun prec f es

instance PPLang l => PP (Block l) where
  ppPrec _ Block { .. } =
    pp blockStmt $$ text "goto" <+> hsep (map pp blockNext)

instance PPLang l => PP (Function l) where
  ppPrec _ Function { .. } = text "-- Entry:" <+> pp entry $$ text " " $$
                            pp blocks



--------------------------------------------------------------------------------


dropSkipsInBlock :: Block l -> Block l
dropSkipsInBlock Block { .. } =
  case dropSkips blockStmt of
    Nothing -> Block { blockStmt = Skip, .. }
    Just b  -> Block { blockStmt = b, .. }

dropSkips :: Stmt l -> Maybe (Stmt l)
dropSkips st =
  case st of
    s1 ::: s2 ->
      case (dropSkips s1, dropSkips s2) of
        (Nothing,x) -> x
        (x,Nothing) -> x
        (Just x, Just y) -> Just (x ::: y)
    Skip -> Nothing
    _    -> Just st


--------------------------------------------------------------------------------
progEqns :: Language l => Function l -> Map (Label l) (Prop l)
progEqns Function { .. } = fmap blockEqn blocks

blockEqn :: Language l => Block l -> Prop l
blockEqn Block { .. } = wp blockStmt (conj (map ok blockNext))

wp :: Language l => Stmt l -> Prop l -> Prop l
wp stmt prop =
  case stmt of
    Assert p  -> p /\ prop
    Assume p  -> p ==> prop
    s1 ::: s2 -> wp s1 (wp s2 prop)
    Skip      -> prop
    Havoc _   -> err "Havoc"
    _ := _    -> err ":="

  where
  err msg = error ("Non-passive statement: " ++ msg)

--------------------------------------------------------------------------------
passifyStmt :: Language l => Stmt l -> Stmt l
passifyStmt stmt =
  case stmt of
    i := e    -> Assume (EVar i === e)
    Havoc _   -> Skip
    Assert _  -> stmt
    Assume _  -> stmt
    Skip      -> stmt
    s1 ::: s2 -> passifyStmt s1 ::: passifyStmt s2

passifyBlock :: Language l => Block l -> Block l
passifyBlock Block { .. } = Block { blockStmt = passifyStmt blockStmt, .. }

-- | Convert to sequences of assert and assume.
passifyFunction :: Language l => Function l -> Function l
passifyFunction Function { .. } =
  Function { blocks = fmap passifyBlock blocks, .. }


--------------------------------------------------------------------------------
-- Conversion to DSA


data InstDB l = InstDB
  { nextName   :: Map (VarSym l) Int

  , blockInsts :: Map (Label l) (Map (VarSym l) (Set (Inst (VarSym l))))

  , doneBlocks :: Map (Label l) (Block (DSA l))

  , curBlock   :: Map (VarSym l) (Inst (VarSym l))

  , curPreds   :: [Label l]
  }

blankDB :: InstDB l
blankDB =
  InstDB { nextName   = Map.empty
         , blockInsts = Map.empty
         , doneBlocks = Map.empty
         , curBlock   = Map.empty
         , curPreds   = []
         }


newBlock :: Language l => Function l -> Label l -> InstDB l -> InstDB l
newBlock p b InstDB { .. } =
  InstDB { curBlock = Map.empty
         , curPreds = predecessors p Map.! b
         , ..
         }


finishBlock :: Language l => Label l -> Block (DSA l) -> InstDB l ->
                                                              InstDB l
finishBlock curBlockId bl InstDB { .. } =
  InstDB  { blockInsts = Map.insert curBlockId knownNames blockInsts
          , doneBlocks = Map.insert curBlockId bl doneBlocks
          , curBlock   = Map.empty
          , curPreds   = []
          , ..
          }
  where
  knownNames  = Map.union (fmap Set.singleton curBlock)
                -- for things that were not mentioned in this block,
                -- we compute the intersection of the known names in our
                -- parents.
                $ case [ blockInsts Map.! b | b <- curPreds ] of
                    [] -> Map.empty
                    xs -> foldr1 (Map.intersectionWith Set.intersection) xs


-- | Get the current instance for the given variable.
lookupCur :: Language l => VarSym l -> InstDB l -> (Inst (VarSym l), InstDB l)
lookupCur x idb =
  case Map.lookup x (curBlock idb) of
    Just i  -> (i, idb)
    Nothing -> chooseName x idb


-- | Pick a previously unused instance for some variable.
newInstVar :: Language l => VarSym l -> InstDB l -> (Inst (VarSym l), InstDB l)
newInstVar x InstDB { .. } =
  (v, InstDB { nextName = Map.insert x (i+1) nextName
             , curBlock = Map.insert x v curBlock
             , .. })
  where i = Map.findWithDefault 0 x nextName
        v = Inst x i


-- | Add a renaming to the end of a block, to accomoda DSA representation.
addRename :: Language l => Inst (VarSym l) -> Label l -> InstDB l -> InstDB l
addRename v@(Inst x _) bid InstDB { .. } =
  InstDB { doneBlocks = Map.adjust upd bid doneBlocks
         , blockInsts = Map.adjust (Map.adjust (Set.insert v) x) bid blockInsts
         , .. }
  where
  Just (j,_)        = Set.minView (blockInsts Map.! bid Map.! x)
  upd Block { .. }  = Block { blockStmt = blockStmt ::: (v := EVar j)
                            , .. }

-- | Choose a name to be used in the curren block, based on the instances
-- in our predecessors.
chooseName :: Language l => VarSym l -> InstDB l -> (Inst (VarSym l),InstDB l)
chooseName x idb =
  case bs of
    [] -> newInstVar x idb
    _  -> case Set.minView (foldr1 Set.intersection opts) of
            Nothing -> let (y,idb1) = newInstVar x idb
                       in (y, foldr (addRename y) idb1 bs)
            Just (i,_) -> (i, idb)
  where
  opts = [ Map.findWithDefault Set.empty x (blockInsts idb Map.! b) | b <- bs ]
  bs   = curPreds idb




-- | Topologically sort the blocks of a program with no loops.
topoSort :: Language l => Function l -> [ (Label l, Block l) ]
topoSort Function { .. } = unfoldr step (Set.empty,[entry],[])
  where
  deQ (_,[],[])           = Nothing
  deQ (done,[],qBack)     = deQ (done,reverse qBack,[])
  deQ (done,q : qs,qBack) = Just (q, (done,qs,qBack))

  enQ bid (done,qFront,qBack) =
    let ready = all (`Set.member` done) (predecessors Map.! bid)
    in if ready then (done, qFront, bid : qBack)
                else (done, qFront,       qBack)

  step s = do (bid,(done,qFront,qBack)) <- deQ s
              let s1 = (Set.insert bid done, qFront, qBack)
                  b  = blocks Map.! bid
              return ((bid,b), foldr enQ s1 (blockNext b))



type InstM l = StateT (InstDB l) Id

-- | Instantiate an expression.
instExpr :: Language l => Expr l -> InstM l (Expr (DSA l))
instExpr expr =
  case expr of
    EVar x    -> EVar `fmap` sets (lookupCur x)
    Fun f es  -> Fun f `fmap` mapM instExpr es


-- | Instantiate a proposition.
instProp :: Language l => Prop l -> InstM l (Prop (DSA l))
instProp expr =
  case expr of
    Pred f es -> Pred f `fmap` mapM instExpr es
    Conn f ps -> Conn f `fmap` mapM instProp ps



-- | Instantiate a statement.
instStmt :: Language l => Stmt l -> InstM l (Stmt (DSA l))
instStmt stmt =
  case stmt of
    x := e ->
      do e' <- instExpr e   -- do this first, to use the current value for x!
         x' <- sets (newInstVar x)
         return (x' := e')
    Havoc x   -> Havoc `fmap` sets (newInstVar x)
    Assert e  -> Assert `fmap` instProp e
    Assume e  -> Assume `fmap` instProp e
    s1 ::: s2 -> liftM2 (:::) (instStmt s1) (instStmt s2)
    Skip      -> return Skip


instBlock :: Language l => Function l -> (Label l, Block l) -> InstM l ()
instBlock p (bid,b) =
  do sets_ $ newBlock p bid
     s <- instStmt (blockStmt b)
     sets_ $ finishBlock bid (changeStmt b s)

changeStmt :: Block l -> Stmt (DSA l) -> Block (DSA l)
changeStmt Block { .. } s = Block { blockStmt = s, .. }

-- XXX: This appears to be a bug in GHC
-- changeStmt b s = b { blockStmt = s }

-- | Convert a program into DSA form.
toDSA :: Language l => Function l -> Function (DSA l)
toDSA f@Function { .. } = Function { blocks = doneBlocks s, .. }
  where
  (_,s) = runId $ runStateT blankDB $ mapM_ (instBlock f) $ topoSort f



--------------------------------------------------------------------------------
-- Eliminating loops

data Loop l = Loop
  { loopStart   :: Label l
  , loopEnd     :: Label l
  , loopBlocks  :: Set (Label l)
  }

deriving instance Show (Label l) => Show (Loop l)


-- | Add loop invariants, and remove loops.
removeLoops :: Language l => Function l -> Function l
removeLoops p = apply cutLoop
              $ apply forgetLoopTargets
              $ apply addinvariant p
  where
  loops         = findLoops p
  apply f prog  = foldr f prog loops


-- | Remove the back edges of loops.
cutLoop :: Language l => Loop l -> Function l -> Function l
cutLoop Loop { .. } Function { .. } =
  Function { blocks = Map.adjust cut loopEnd blocks
          , predecessors = Map.adjust (delete loopEnd) loopStart predecessors
          , .. }
  where
  cut Block { .. } = Block { blockNext = filter (/= loopStart) blockNext, .. }


-- | "Havoc" the varialbes that are modified by the loop.
forgetLoopTargets :: Language l => Loop l -> Function l -> Function l
forgetLoopTargets Loop { .. } Function { .. } =
  Function { blocks = Map.adjust havoc loopStart blocks, .. }
  where
  havoc Block { .. } = Block { blockStmt = foldr addH blockStmt vars, .. }
  addH x s = Havoc x ::: s
  vars     = Set.toList $ Set.unions $ map varsOf $ Set.toList loopBlocks
  varsOf b = statementUpdates (blockStmt (blocks Map.! b))


-- | Varaibles updated by this statement
statementUpdates :: Language l => Stmt l -> Set (VarSym l)
statementUpdates stmt =
  case stmt of
    x := _    -> Set.singleton x
    Havoc x   -> Set.singleton x
    Assert _  -> Set.empty
    Assume _  -> Set.empty
    s1 ::: s2 -> Set.union (statementUpdates s1) (statementUpdates s2)
    Skip      -> Set.empty


-- | Add inveariant assertion/assumptions for the given loop
addinvariant :: Language l => Loop l -> Function l -> Function l
addinvariant Loop { .. } p0 =
    updBlock addHead loopStart
  $ foldr (updBlock addPre) p0
  $ predecessors p0 Map.! loopStart
  where
  inv = invariant loopStart loopEnd
  addPre Block { .. } = Block { blockStmt = blockStmt ::: Assert inv, .. }
  addHead Block { .. } = Block { blockStmt = Assume inv ::: blockStmt, .. }
  updBlock f b Function { .. } = Function { blocks = Map.adjust f b blocks, .. }


{- | Identify the loops in a program.  Assumes that the control-flow
graph is reducible (i.e., loops have only one entry point). -}
findLoops :: Language l => Function l -> [Loop l]
findLoops Function { .. } = concatMap blockLoops (Map.toList blocks)
  where
  blockLoops (loopEnd, Block { .. }) =
    [ Loop { loopBlocks = naturalLoop Function { .. } loopEnd loopStart, .. }
        | loopStart <- blockNext, loopStart `dominates` loopEnd ]

  doms              = dominators Function { .. }
  dominates a b     = a `Set.member` (doms Map.! b)


-- | Given a program and a back-edge, reconstruct a loop.
naturalLoop :: Language l => Function l -> Label l -> Label l -> Set (Label l)
naturalLoop p n d = go (insert n (Set.singleton d, []))
  where
  go (loop, [])     = loop
  go (loop, m : ms) = go (foldr insert (loop,ms) (predecessors p Map.! m))

  insert m (loop,todo)
    | m `Set.member` loop = (loop, todo)
    | otherwise           = (Set.insert n loop, m : todo)


-- | Compute the dominators for each block in a program.
dominators :: Language l => Function l -> Map (Label l) (Set (Label l))
dominators Function { .. } = head
                           $ catMaybes
                           $ zipWith done steps (tail steps)
  where
  done x y  = if x == y then Just x else Nothing

  steps     = iterate step start

  start     = Map.insert entry (Set.singleton entry)
            $ fmap (const (Map.keysSet blocks)) blocks

  step doms = foldr stepNode doms (Map.keys blocks)

  stepNode node doms
    | node == entry = doms
    | otherwise     = let s = Set.insert node
                            $ foldr1 Set.intersection
                            $ map (doms Map.!)
                            $ predecessors Map.! node
                      in Map.insert node s doms






