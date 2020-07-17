{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Cps (build, Cps (..), Stack, Code, Data, Builder, simplify, inline, abstract) where

import Common
import Constant (Constant)
import qualified Constant
import Core
import qualified Data.Text as T
import Global
import HasCode
import HasConstants
import HasData
import HasLet
import HasStack
import HasThunk
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import TextShow (TextShow, fromString, fromText, showb, toText)
import Tuple
import Unique
import VarMap (VarMap)
import qualified VarMap
import Variable

data Data a where
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a
  ThunkData :: Label a -> Code -> Data (U a)
  PairData :: Data a -> Data b -> Data (a :*: b)

data Code where
  GlobalCode :: Global a -> Stack a -> Code
  LetLabelCode :: Stack a -> Label a -> Code -> Code
  LetBeCode :: Data a -> Variable a -> Code -> Code
  ForceCode :: Data (U a) -> Stack a -> Code
  ThrowCode :: Stack (F a) -> Data a -> Code
  LambdaCode :: Stack (a :=> b) -> Variable a -> Label b -> Code -> Code

data Stack a where
  LabelStack :: Label a -> Stack a
  ToStack :: Variable a -> Code -> Stack (F a)
  ApplyStack :: Data a -> Stack b -> Stack (a :=> b)

-- |
--
-- I don't understand this but apparently the CPS transform of Call By
-- Push Value is similar to the λμ ̃μ calculus.
--
-- https://www.reddit.com/r/haskell/comments/hp1mao/i_found_a_neat_duality_for_cps_with_call_by_push/fxn046g/?context=3
class (HasConstants t, HasCode t, HasStack t, HasLet t, HasThunk t, Tuple t) => Cps t where
  throw :: StackRep t (F a) -> DataRep t a -> CodeRep t Void

  letTo :: SSet a -> (DataRep t a -> CodeRep t Void) -> StackRep t (F a)

  apply :: DataRep t a -> StackRep t b -> StackRep t (a :=> b)

  nil :: StackRep t Void

data Builder

instance HasData Builder where
  newtype DataRep Builder a = DB (forall s. Unique.Stream s -> (SSet a, Data a))

instance HasCode Builder where
  newtype CodeRep Builder a = CB (forall s. Unique.Stream s -> Code)

instance HasStack Builder where
  newtype StackRep Builder a = SB (forall s. Unique.Stream s -> (SAlgebra a, Stack a))

instance HasLet Builder where
  letBe (DB x) f = CB $ \(Unique.Stream newId xs ys) ->
    let (xt, x') = x xs
        binder = Variable xt newId
     in case f (DB $ \_ -> (xt, VariableData binder)) of
          CB y ->
            let y' = y ys
             in LetBeCode x' binder y'

instance HasConstants Builder where
  constant k = DB $ \_ -> (Constant.typeOf k, ConstantData k)

instance Tuple Builder where
  pair (DB x) (DB y) = DB $ \(Unique.Stream _ ks xs) ->
    let (xt, x') = x xs
        (yt, y') = y xs
     in (SPair xt yt, PairData x' y')

instance HasThunk Builder where
  lambda (SB k) f = CB $ \(Unique.Stream aId (Unique.Stream bId _ ks) ys) ->
    let (a `SFn` b, k') = k ks
        binder = Variable a aId
        label = Label b bId
     in case f (DB $ \_ -> (a, VariableData binder)) (SB $ \_ -> (b, LabelStack label)) of
          CB y ->
            let y' = y ys
             in LambdaCode k' binder label y'

  thunk t f = DB $ \(Unique.Stream newId xs ys) ->
    let binder = Label t newId
     in case f (SB $ \_ -> (t, LabelStack binder)) of
          CB y ->
            let y' = y ys
             in (SU t, ThunkData binder y')
  force (DB k) (SB x) = CB $ \(Unique.Stream _ ks xs) ->
    let (_, k') = k ks
        (_, x') = x xs
     in ForceCode k' x'

  call g (SB k) = CB $ \s ->
    let (_, k') = k s
     in GlobalCode g k'

instance Cps Builder where
  letTo t f = SB $ \(Unique.Stream newId xs ys) ->
    let binder = Variable t newId
     in case f (DB $ \_ -> (t, VariableData binder)) of
          CB y ->
            let y' = y ys
             in (SF t, ToStack binder y')

  throw (SB k) (DB x) = CB $ \(Unique.Stream _ ks xs) ->
    let (_, k') = k ks
        (_, x') = x xs
     in ThrowCode k' x'

  apply (DB x) (SB k) = SB $ \(Unique.Stream _ ks xs) ->
    let (xt, x') = x xs
        (kt, k') = k ks
     in (xt `SFn` kt, ApplyStack x' k')

instance TextShow (Data a) where
  showb (ConstantData k) = showb k
  showb (VariableData v) = showb v
  showb (ThunkData binder@(Label t _) body) =
    fromString "thunk " <> showb binder <> fromString ": " <> showb t <> fromString " " <> fromText (T.replace (T.pack "\n") (T.pack "\n\t") (toText (fromString "\n" <> showb body)))

instance TextShow (Stack a) where
  showb (LabelStack v) = showb v
  showb (ToStack binder@(Variable t _) body) =
    fromString "to " <> showb binder <> fromString ": " <> showb t <> fromString ".\n" <> showb body
  showb (ApplyStack x f) = showb x <> fromString " :: " <> showb f

instance TextShow Code where
  showb c = case c of
    GlobalCode g k -> fromString "call " <> showb g <> fromString " " <> showb k
    LetLabelCode value binder body -> showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
    LetBeCode value binder body -> showb value <> fromString " be " <> showb binder <> fromString ".\n" <> showb body
    ThrowCode k x -> fromString "throw " <> showb k <> fromString " " <> showb x
    ForceCode thnk stk -> fromString "! " <> showb thnk <> fromString " " <> showb stk
    LambdaCode k binder@(Variable t _) label@(Label a _) body ->
      showb k <> fromString " λ " <> showb binder <> fromString ": " <> showb t <> fromString " " <> showb label <> fromString ": " <> showb a <> fromString "\n" <> showb body

build :: DataRep Builder a -> Data a
build (DB s) = snd (Unique.withStream s)

simplify :: Data a -> Data a
simplify (ThunkData binder body) = ThunkData binder (simpCode body)
simplify x = x

simpStack :: Stack a -> Stack a
simpStack (ToStack binder body) = ToStack binder (simpCode body)
simpStack (ApplyStack h t) = ApplyStack (simplify h) (simpStack t)
simpStack x = x

simpCode :: Code -> Code
simpCode code = case code of
  ThrowCode (ToStack binder body) value -> simpCode (LetBeCode value binder body)
  ForceCode (ThunkData label body) k -> simpCode (LetLabelCode k label body)
  ThrowCode k x -> ThrowCode (simpStack k) (simplify x)
  ForceCode f x -> ForceCode (simplify f) (simpStack x)
  LetLabelCode thing binder body -> LetLabelCode (simpStack thing) binder (simpCode body)
  LetBeCode thing binder body -> LetBeCode (simplify thing) binder (simpCode body)
  GlobalCode g k -> GlobalCode g (simpStack k)
  LambdaCode k binder label body -> LambdaCode (simpStack k) binder label (simpCode body)

inline :: Cps t => Data a -> DataRep t a
inline = inlValue LabelMap.empty VarMap.empty

inlValue :: Cps t => LabelMap (StackRep t) -> VarMap (DataRep t) -> Data a -> DataRep t a
inlValue lenv env x = case x of
  VariableData v ->
    let Just x = VarMap.lookup v env
     in x
  ThunkData binder@(Label t _) body -> thunk t $ \k ->
    inlCode (LabelMap.insert binder k lenv) env body
  ConstantData k -> constant k

inlStack :: Cps t => LabelMap (StackRep t) -> VarMap (DataRep t) -> Stack a -> StackRep t a
inlStack lenv env stk = case stk of
  LabelStack v ->
    let Just x = LabelMap.lookup v lenv
     in x
  ApplyStack h t -> Cps.apply (inlValue lenv env h) (inlStack lenv env t)
  ToStack binder@(Variable t _) body -> Cps.letTo t $ \value ->
    let env' = VarMap.insert binder value env
     in inlCode lenv env' body

inlCode :: Cps t => LabelMap (StackRep t) -> VarMap (DataRep t) -> Code -> CodeRep t Void
inlCode lenv env code = case code of
  LambdaCode k binder@(Variable t _) label@(Label a _) body ->
    let k' = inlStack lenv env k
     in lambda k' $ \h k ->
          inlCode (LabelMap.insert label k lenv) (VarMap.insert binder h env) body
  LetLabelCode term binder@(Label t _) body -> result
    where
      term' = inlStack lenv env term
      result
        | countLabel binder body <= 1 || isSimpleStack term =
          inlCode (LabelMap.insert binder term' lenv) env body
        | otherwise =
          force
            ( thunk t $ \x ->
                inlCode (LabelMap.insert binder x lenv) env body
            )
            term'
  LetBeCode term binder@(Variable t _) body -> result
    where
      term' = inlValue lenv env term
      result
        | count binder body <= 1 || isSimple term =
          inlCode lenv (VarMap.insert binder term' env) body
        | otherwise =
          throw
            ( letTo t $ \x ->
                inlCode lenv (VarMap.insert binder x env) body
            )
            term'
  ThrowCode k x -> throw (inlStack lenv env k) (inlValue lenv env x)
  ForceCode k x -> force (inlValue lenv env k) (inlStack lenv env x)
  GlobalCode g k -> call g (inlStack lenv env k)

isSimple :: Data a -> Bool
isSimple (ConstantData _) = True
isSimple (VariableData _) = True
isSimple _ = False

isSimpleStack :: Stack a -> Bool
isSimpleStack (LabelStack _) = True
isSimpleStack _ = False

count :: Variable a -> Code -> Int
count v = code
  where
    value :: Data b -> Int
    value (VariableData binder) = if AnyVariable v == AnyVariable binder then 1 else 0
    value (ThunkData _ body) = code body
    value _ = 0
    stack :: Stack b -> Int
    stack (ApplyStack h t) = value h + stack t
    stack (ToStack binder body) = code body
    stack _ = 0
    code :: Code -> Int
    code c = case c of
      LetLabelCode x binder body -> stack x + code body
      LetBeCode x binder body -> value x + code body
      ThrowCode k x -> stack k + value x
      ForceCode t k -> value t + stack k
      GlobalCode _ k -> stack k
      LambdaCode k _ _ body -> stack k + code body

countLabel :: Label a -> Code -> Int
countLabel v = code
  where
    value :: Data b -> Int
    value (ThunkData _ body) = code body
    value _ = 0
    stack :: Stack b -> Int
    stack stk = case stk of
      LabelStack binder -> if AnyLabel v == AnyLabel binder then 1 else 0
      ToStack binder body -> code body
      ApplyStack h t -> value h + stack t
    code :: Code -> Int
    code c = case c of
      LetLabelCode x binder body -> stack x + code body
      LetBeCode x binder body -> value x + code body
      ThrowCode k x -> stack k + value x
      ForceCode t k -> value t + stack k
      GlobalCode _ k -> stack k
      LambdaCode k _ _ body -> stack k + code body

abstract :: Cps t => Data a -> DataRep t a
abstract x = abstData x LabelMap.empty VarMap.empty

abstData :: Cps t => Data a -> LabelMap (StackRep t) -> VarMap (DataRep t) -> DataRep t a
abstData x = case x of
  ConstantData k -> \_ _ -> constant k
  VariableData v -> \_ env -> case VarMap.lookup v env of
    Just x -> x
    Nothing -> error "variable not found in environment"
  ThunkData label@(Label t _) body ->
    let body' = abstCode body
     in \lenv env ->
          thunk t $ \k ->
            body' (LabelMap.insert label k lenv) env

abstStack :: Cps t => Stack a -> LabelMap (StackRep t) -> VarMap (DataRep t) -> StackRep t a
abstStack stk = case stk of
  LabelStack v -> \lenv _ -> case LabelMap.lookup v lenv of
    Just x -> x
    Nothing -> error "label not found in environment"
  ToStack binder@(Variable t _) body ->
    let body' = abstCode body
     in \lenv env ->
          letTo t $ \value ->
            body' lenv (VarMap.insert binder value env)
  ApplyStack h t ->
    let h' = abstData h
        t' = abstStack t
     in \lenv env -> apply (h' lenv env) (t' lenv env)

abstCode :: Cps t => Code -> LabelMap (StackRep t) -> VarMap (DataRep t) -> CodeRep t Void
abstCode c = case c of
  GlobalCode g k ->
    let k' = abstStack k
     in \lenv env -> call g (k' lenv env)
  ThrowCode k x ->
    let value' = abstData x
        k' = abstStack k
     in \lenv env -> throw (k' lenv env) (value' lenv env)
  ForceCode k x ->
    let value' = abstStack x
        k' = abstData k
     in \lenv env -> force (k' lenv env) (value' lenv env)
  LetBeCode value binder body ->
    let value' = abstData value
        body' = abstCode body
     in \lenv env -> body' lenv (VarMap.insert binder (value' lenv env) env)
  LetLabelCode value binder body ->
    let value' = abstStack value
        body' = abstCode body
     in \lenv env -> body' (LabelMap.insert binder (value' lenv env) lenv) env
  LambdaCode k binder@(Variable t _) label@(Label a _) body ->
    let body' = abstCode body
        k' = abstStack k
     in \lenv env ->
          lambda
            (k' lenv env)
            ( \h n ->
                body' (LabelMap.insert label n lenv) (VarMap.insert binder h env)
            )
