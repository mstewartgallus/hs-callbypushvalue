{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeOperators #-}

module Cps (build, Cps (..), Stack (..), Code (..), Data (..), Builder (..), simplify, inline, abstract) where

import Common
import Constant (Constant)
import qualified Constant
import Core
import qualified Data.Text as T
import Global
import Label
import LabelMap (LabelMap)
import qualified LabelMap
import TextShow (TextShow, fromString, fromText, showb, toText)
import Type
import Unique
import VarMap (VarMap)
import qualified VarMap
import Variable

data Data a where
  ConstantData :: Constant a -> Data a
  VariableData :: Variable a -> Data a
  ThunkData :: Label a -> Code -> Data (U a)

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
class Cps t where
  constant :: Constant a -> t (Data a)
  global :: Global a -> t (Stack a) -> t Code

  throw :: t (Stack (F a)) -> t (Data a) -> t Code
  force :: t (Data (U a)) -> t (Stack a) -> t Code

  thunk :: Action a -> (t (Stack a) -> t Code) -> t (Data (U a))
  letTo :: Type a -> (t (Data a) -> t Code) -> t (Stack (F a))

  lambda :: t (Stack (a :=> b)) -> (t (Data a) -> (t (Stack b) -> t Code)) -> t Code

  head :: t (Data (a :*: b)) -> t (Data a)
  tail :: t (Data (a :*: b)) -> t (Data b)

  pop :: t (Data (a :*: b)) -> (t (Data a) -> t (Data b) -> t Code) -> t Code

  apply :: t (Data a) -> t (Stack b) -> t (Stack (a :=> b))
  push :: t (Data a) -> t (Data b) -> t (Data (a :*: b))

  unit :: t (Data Unit)
  nil :: t (Stack Void)

instance Cps Builder where
  global g (SB k) = CB $ \s ->
    let (_, k') = k s
     in GlobalCode g k'

  constant k = DB $ \_ -> (Constant.typeOf k, ConstantData k)

  letTo t f = SB $ \(Unique.Stream newId xs ys) ->
    let binder = Variable t newId
     in case f (DB $ \_ -> (t, VariableData binder)) of
          CB y ->
            let y' = y ys
             in (F t, ToStack binder y')
  thunk t f = DB $ \(Unique.Stream newId xs ys) ->
    let binder = Label t newId
     in case f (SB $ \_ -> (t, LabelStack binder)) of
          CB y ->
            let y' = y ys
             in (U t, ThunkData binder y')

  throw (SB k) (DB x) = CB $ \(Unique.Stream _ ks xs) ->
    let (_, k') = k ks
        (_, x') = x xs
     in ThrowCode k' x'
  force (DB k) (SB x) = CB $ \(Unique.Stream _ ks xs) ->
    let (_, k') = k ks
        (_, x') = x xs
     in ForceCode k' x'

  lambda (SB k) f = CB $ \(Unique.Stream aId (Unique.Stream bId _ ks) ys) ->
    let (a :=> b, k') = k ks
        binder = Variable a aId
        label = Label b bId
     in case f (DB $ \_ -> (a, VariableData binder)) (SB $ \_ -> (b, LabelStack label)) of
          CB y ->
            let y' = y ys
             in LambdaCode k' binder label y'
  apply (DB x) (SB k) = SB $ \(Unique.Stream _ ks xs) ->
    let (xt, x') = x xs
        (kt, k') = k ks
     in (xt :=> kt, ApplyStack x' k')

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

data Builder a where
  CB :: (forall s. Unique.Stream s -> Code) -> Builder Code
  DB :: (forall s. Unique.Stream s -> (Type a, Data a)) -> Builder (Data a)
  SB :: (forall s. Unique.Stream s -> (Action a, Stack a)) -> Builder (Stack a)

build :: Builder a -> a
build (CB s) = Unique.withStream s
build (DB s) = snd (Unique.withStream s)
build (SB s) = snd (Unique.withStream s)

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

inline :: Cps t => Data a -> t (Data a)
inline = inlValue LabelMap.empty VarMap.empty

newtype X t a = X (t (Data a))

newtype L t a = L (t (Stack a))

inlValue :: Cps t => LabelMap (L t) -> VarMap (X t) -> Data a -> t (Data a)
inlValue lenv env x = case x of
  VariableData v ->
    let Just (X x) = VarMap.lookup v env
     in x
  ThunkData binder@(Label t _) body -> thunk t $ \k ->
    inlCode (LabelMap.insert binder (L k) lenv) env body
  ConstantData k -> Cps.constant k

inlStack :: Cps t => LabelMap (L t) -> VarMap (X t) -> Stack a -> t (Stack a)
inlStack lenv env stk = case stk of
  LabelStack v ->
    let Just (L x) = LabelMap.lookup v lenv
     in x
  ApplyStack h t -> Cps.apply (inlValue lenv env h) (inlStack lenv env t)
  ToStack binder@(Variable t _) body -> Cps.letTo t $ \value ->
    let env' = VarMap.insert binder (X value) env
     in inlCode lenv env' body

inlCode :: Cps t => LabelMap (L t) -> VarMap (X t) -> Code -> t Code
inlCode lenv env code = case code of
  LambdaCode k binder@(Variable t _) label@(Label a _) body ->
    let k' = inlStack lenv env k
     in lambda k' $ \h k ->
          inlCode (LabelMap.insert label (L k) lenv) (VarMap.insert binder (X h) env) body
  LetLabelCode term binder@(Label t _) body -> result
    where
      term' = inlStack lenv env term
      result
        | countLabel binder body <= 1 || isSimpleStack term =
          inlCode (LabelMap.insert binder (L term') lenv) env body
        | otherwise =
          force
            ( thunk t $ \x ->
                inlCode (LabelMap.insert binder (L x) lenv) env body
            )
            term'
  LetBeCode term binder@(Variable t _) body -> result
    where
      term' = inlValue lenv env term
      result
        | count binder body <= 1 || isSimple term =
          inlCode lenv (VarMap.insert binder (X term') env) body
        | otherwise =
          throw
            ( letTo t $ \x ->
                inlCode lenv (VarMap.insert binder (X x) env) body
            )
            term'
  ThrowCode k x -> throw (inlStack lenv env k) (inlValue lenv env x)
  ForceCode k x -> force (inlValue lenv env k) (inlStack lenv env x)
  GlobalCode g k -> global g (inlStack lenv env k)

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

abstract :: Cps t => Data a -> t (Data a)
abstract x = abstData x LabelMap.empty VarMap.empty

abstData :: Cps t => Data a -> LabelMap (L t) -> VarMap (X t) -> t (Data a)
abstData x = case x of
  ConstantData k -> \_ _ -> constant k
  VariableData v -> \_ env -> case VarMap.lookup v env of
    Just (X x) -> x
    Nothing -> error "variable not found in environment"
  ThunkData label@(Label t _) body ->
    let body' = abstCode body
     in \lenv env ->
          thunk t $ \k ->
            body' (LabelMap.insert label (L k) lenv) env

abstStack :: Cps t => Stack a -> LabelMap (L t) -> VarMap (X t) -> t (Stack a)
abstStack stk = case stk of
  LabelStack v -> \lenv _ -> case LabelMap.lookup v lenv of
    Just (L x) -> x
    Nothing -> error "label not found in environment"
  ToStack binder@(Variable t _) body ->
    let body' = abstCode body
     in \lenv env ->
          letTo t $ \value ->
            body' lenv (VarMap.insert binder (X value) env)
  ApplyStack h t ->
    let h' = abstData h
        t' = abstStack t
     in \lenv env -> apply (h' lenv env) (t' lenv env)

abstCode :: Cps t => Code -> LabelMap (L t) -> VarMap (X t) -> t Code
abstCode c = case c of
  GlobalCode g k ->
    let k' = abstStack k
     in \lenv env -> global g (k' lenv env)
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
     in \lenv env -> body' lenv (VarMap.insert binder (X (value' lenv env)) env)
  LetLabelCode value binder body ->
    let value' = abstStack value
        body' = abstCode body
     in \lenv env -> body' (LabelMap.insert binder (L (value' lenv env)) lenv) env
  LambdaCode k binder@(Variable t _) label@(Label a _) body ->
    let body' = abstCode body
        k' = abstStack k
     in \lenv env ->
          lambda
            (k' lenv env)
            ( \h n ->
                body' (LabelMap.insert label (L n) lenv) (VarMap.insert binder (X h) env)
            )
