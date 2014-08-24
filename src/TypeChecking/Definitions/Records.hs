module TypeChecking.Definitions.Records
    ( typeCheckRecord
    ) where

import Data.Void

import Syntax
import Semantics
import Semantics.Value
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Context
import TypeChecking.Expressions.Utils
import TypeChecking.Expressions.Telescopes
import Normalization

typeCheckRecord :: Monad m => PName -> [Tele] -> Maybe PName -> [Field] -> [Clause] -> TCM m ()
typeCheckRecord recPName@(recPos, recName) params mcon fields clauses = do
    (SomeEq ctx, recType@(Type recTerm _)) <- typeCheckTelescope Nil params $ universe (Set NoLevel)
    recID <- addDataTypeCheck recPName 1 $ Closed (vacuous recType)
    (_, Type conType conSort) <- typeCheckTelescope ctx (map (\(Field pn e) -> VarsTele Explicit [pn] e) fields) $
        Apply (Semantics (Name Prefix recName) $ DataType recID 1) (ctxToVars ctx)
    case findOccurrence recID (nf WHNF conType) of
        Just n | n > 0 -> throwError [Error Other $ emsgLC recPos "Record types cannot be recursive" enull]
        _ -> return ()
    case mcon of
        Just con -> addConstructorCheck con recID 0 1 (PatEval []) $
            Closed $ Type (vacuous $ abstractTerm ctx conType) conSort
        _ -> return ()
    lift $ replaceDataType recName 1 $ Closed $ Type (vacuous $ replaceSort recTerm conSort) conSort
