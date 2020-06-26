module Compiler (Compiler, CompilerState (..), getVariable, getLabel) where
import Control.Monad.State
import Common
import TextShow

data CompilerState = CompilerState Integer Integer
type Compiler = State CompilerState

getVariable :: Type a -> Compiler (Variable a)
getVariable t = do
  CompilerState n m <- get
  put (CompilerState (n + 1) m)
  pure (Variable t (toText (fromString "v_" <> showb n)))

getLabel :: Type a -> Compiler (Label a)
getLabel t = do
  CompilerState n m <- get
  put (CompilerState n (m + 1))
  pure (Label t (toText (fromString "l_" <> showb m)))
