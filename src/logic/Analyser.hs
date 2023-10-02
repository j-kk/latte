{-# LANGUAGE LambdaCase #-}

module Analyser where
import AbsLatte
import Control.Monad.Reader (ReaderT (runReaderT), MonadReader (ask, local), asks, runReader)
import Data.Map (Map, insert, size, findMax, member, fromList, (!), elems)
import Control.Monad.Except (ExceptT, runExceptT, foldM, MonadError (throwError), unless, forM_, when, foldM_)
import Control.Monad.State (StateT, execStateT, modify, MonadState (get), evalStateT, gets)
import qualified Data.Map as Map
import qualified Control.Monad
import qualified TypeMatchUtils as TM
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure, exitSuccess)
import Data.Maybe ( isNothing, fromJust )
import Data.Functor ((<&>))
import PrintLatte (Print (prt))
import PrintUtils ( prettyPrt, prettyPrt' )
import TypeMatchUtils (extractIdentStr, HasIdent (hasIdent), MaybeIdent (maybeIdent), isAttr)
import CompilerUtils (builtInFunctions)
import qualified Data.Set as S

type BlockDepth = Int

type Loc = Int

data LocInfo = LocInfo {location :: Loc, depth :: BlockDepth}
        deriving Show

type LocMap = Map Loc Type
type ClassMap = Map Ident ClassInfo
type VarMap = Map Ident LocInfo
type FieldsMap = Map Ident ClMember

data Context = Context {
    position :: BNFC'Position,
    variable_map :: VarMap,
    block_depth :: BlockDepth,
    return_type :: Maybe TM.BaseType,
    is_inside_block :: Bool
}

data AState = AState {
    loc_map :: LocMap,
    class_map :: ClassMap,
    processed_classes :: S.Set Ident
}

data ClassInfo = ClassInfo {
    extends :: Maybe Ident,
    fields :: FieldsMap
} deriving (Show)

type Analyser m = StateT AState (ReaderT Context (ExceptT String IO)) m

replPos :: BNFC'Position -> Analyser Context
replPos new_position = do
    ctx <- ask
    return (ctx {position = new_position})

replIsBlock :: Bool -> Analyser Context
replIsBlock is_block = do
    ctx <- ask
    return (ctx {is_inside_block = is_block})

updatePosition :: BNFC'Position -> Analyser r -> Analyser r
updatePosition position cont = do
    ctx <- replPos position
    local (const ctx) cont

ctxDisableBlock :: Analyser r -> Analyser r
ctxDisableBlock cont = do
    ctx <- replIsBlock False
    local (const ctx) cont

showS :: Show a => a -> ShowS
showS = showString . show

getLoc :: Analyser Loc
getLoc = do
    store <- gets loc_map
    let loc = if size store /= 0 then fst (findMax store) + 1 else 1
    return loc

getVariable :: Ident -> Analyser Type
getVariable ident = do
    var_map <- asks variable_map
    loc_map <- gets loc_map
    unless (member ident var_map) $
        throwLocError (showString "Undefined variable: " $ prettyPrt' ident)
    let loc = location (var_map ! ident)
    return (loc_map ! loc)


throwLocError :: String -> Analyser a
throwLocError err = do
    pos <- asks position
    throwError $ prettyPrt pos err

throwLocError' :: BNFC'Position -> String -> Analyser a
throwLocError' pos err =
    throwError $ prettyPrt pos err

type DefMap = Map Ident TopDef

declTopDef :: DefMap -> TopDef -> Analyser VarMap
declTopDef _ (FnDef declPos returnType ident args block) = do
    loc <- getLoc
    arg_types <- mapM checkDefArg args
    modify(\store -> store {loc_map = insert loc (Fun declPos returnType arg_types) (loc_map store)})
    var_map <- asks variable_map
    block_depth <- asks block_depth
    when (member ident var_map) $ throwLocError $ showString "Redeclaration of function named " $ prettyPrt' ident
    return (insert ident (LocInfo loc block_depth) var_map)

declTopDef def_map (ClDef pos ident extends clmembers) = do
    classes <- gets class_map
    if member ident classes then asks variable_map else (do
      prc_classes <- gets processed_classes
      when (S.member ident prc_classes) $ throwLocError $ showString "Class extension loop " $ prettyPrt' ident
      let empty_class = ClassInfo (maybeIdent extends) Map.empty
      modify(\store -> store {processed_classes = S.insert ident (processed_classes store)})
      base_class <- crawlExtension ident def_map empty_class extends
      class_info <- foldM readClassMembers base_class clmembers
      loc <- getLoc
      modify(\store -> store {class_map = insert ident class_info (class_map store)})
      asks variable_map)

readClassMembers :: ClassInfo -> ClMember -> Analyser ClassInfo
readClassMembers class_info clmember = do
    ident <- case clmember of
        (Attr _ (Void voidpos) _) ->  throwLocError' voidpos "Class cannot take void as an attribute."
        (Attr _ (Fun funpos _ _) _) -> throwLocError' funpos "Function cannot take function as an attribute."
        (Attr pos atype ident) -> return ident
        (Meth pos ret_type ident args block) -> do
            when (TM.isFun ret_type) $ throwLocError' pos "Method cannot return fun"
            mapM_ checkDefArg args
            return ident
    case Map.lookup ident (fields class_info) of
      Nothing -> ok ident
      Just Attr {} -> throwLocError' (hasPosition clmember) $ showString "Cannot overwrite attribute" (show ident)
      Just Meth {} ->
          if TM.isMeth clmember then ok ident else throwLocError' (hasPosition clmember) $ showString "Cannot overwrite method with an attribute" (show ident)

    where
        ok ident = return class_info { fields = Map.insert ident clmember (fields class_info)}



crawlExtension :: Ident -> DefMap -> ClassInfo -> ClassExt -> Analyser ClassInfo
crawlExtension _ _ cl (NoExt _) = return cl
crawlExtension base_ident def_map (ClassInfo extends cl_fields) (Ext pos ident) = do
    classes <- gets class_map
    base_class <- case Map.lookup ident classes of
        Nothing -> do
            case Map.lookup ident def_map of
                Just cls@(ClDef pos ident extends clmembers) -> do
                    declTopDef def_map cls
                    classes <- gets class_map
                    return (classes ! ident)
                Just _ -> throwLocError' pos $ showString "Cannot extend function: " $ prettyPrt' ident
                Nothing -> throwLocError' pos $ showString "Cannot find base class: " $ prettyPrt' ident
        Just c -> return c
    updated_fields <- foldM appendField cl_fields (Map.elems $ fields base_class)
    return $ ClassInfo extends updated_fields
    where
        appendField :: FieldsMap -> ClMember -> Analyser FieldsMap
        appendField actual_fields member =
            case member of
                attr@(Attr _ _ attr_id) -> do
                    case Map.lookup attr_id actual_fields of
                        Nothing -> return $ Map.insert attr_id attr actual_fields
                        Just any -> throwLocError $ showString "Redeclaration of field: " $ prettyPrt' attr_id
                meth@(Meth _ _ meth_id _ _) -> do
                    when (Map.member meth_id actual_fields) $ when (isAttr (actual_fields ! meth_id)) $ throwLocError $ showString "Cannot override attribute with method: " $ prettyPrt' meth_id
                    return $ Map.insert meth_id meth actual_fields



checkDefArg :: Arg -> Analyser Type
checkDefArg (Arg argpos argtype argident) =
    case argtype of
        (Void voidpos) -> updatePosition voidpos $ throwLocError "Function cannot take void as an argument."
        (Fun funpos _ _) -> updatePosition funpos $ throwLocError "Function cannot take function as an argument."
        _ -> return argtype

evalExpr :: Expr -> Analyser (Type, Maybe (Either Bool Integer))
evalExpr expr = case expr of
    EVar pos id -> do
        t <- updatePosition pos $ getVariable id
        return (t, Nothing)
    ELitInt pos n -> do
        unless (-2147483648 <= n && n < 2147483647) $ throwLocError $ showString "Number exceeding int range: " $ prettyPrt' n
        return (Int pos, Just (Right n))
    ELitTrue pos ->
        return (Bool pos, Just (Left True))
    ELitFalse pos ->
        return (Bool pos, Just (Left False))
    EInitArr pos arr_type expr -> do
        arr_size <- evalExpr expr
        updatePosition pos $ case arr_type of
          Void ma -> throwLocError "Cannot initialise an array of voids."
          Fun ma ty tys -> throwLocError "Cannot initialise an array of functions."
          _ -> do
            updatePosition pos $ unless (TM.isInt $ fst arr_size) $ throwLocError $ showString "Array size must be an integer, given: " $ prettyPrt expr $ showString " has type: " $ prettyPrt' arr_type
            return (Array pos arr_type, Nothing)
    ENewCls pos dtype -> do
        cls_map <- gets class_map
        cls_ident <- case dtype of
          Cls ma id -> return id
          _ -> throwLocError' pos $ showString "Expected class identifier, got: " $ prettyPrt' dtype
        unless (member cls_ident cls_map) $ throwLocError' pos $ showString "Unknown type identifier: " $ prettyPrt' cls_ident
        return (dtype, Nothing)

    ECastNull pos dtype -> do
        cls_map <- gets class_map
        cls_ident <- case dtype of
          Cls ma id -> return id
          _ -> throwLocError' pos $ showString "Expected class identifier, got: " $ prettyPrt' dtype
        unless (member cls_ident cls_map) $ throwLocError' pos $ showString "Unknown type identifier: " $ prettyPrt' cls_ident
        return (dtype, Nothing)

    EArrElem pos expr_name expr_i -> do
        dtype <- updatePosition pos $ fst <$> evalExpr expr_name
        itype <- fst <$> evalExpr expr_i
        unless (TM.isInt itype) $
            throwLocError (showString "Array index must be an integer, got: " $ prettyPrt' itype)
        case dtype of
          Array ma elem_type -> return (elem_type, Nothing)
          _ -> throwLocError' pos (showString "Expression does not evaluate to array: " $ prettyPrt' expr_name)
    EApp pos ident exs -> do
        var_map <- asks variable_map
        fun_decl <- getVariable ident
        case fun_decl of
            Fun pos returnType argTypes -> do
                unless (length argTypes == length exs) $ throwLocError $ showString "Cannot evaluate function " $ prettyPrt ident " - wrong number of arguments applied"
                forM_ (zip argTypes exs) checkType
                return (returnType, Nothing)
            _ -> throwLocError $ showString "Cannot apply to " $ prettyPrt ident " is not a function!"
        where
            checkType :: (Type, Expr) -> Analyser ()
            checkType (argtype, expr) = do
                (expr_type, _) <- evalExpr expr
                updatePosition (hasPosition expr_type) $ unless (TM.typeToBase argtype == TM.typeToBase expr_type) $ throwLocError $ showString "Expected type " $ prettyPrt argtype $ showString " got: " $ prettyPrt' expr_type
    EClassVar pos expr field_ident -> do
        (expr_type, _) <- evalExpr expr
        case expr_type of
          Array pos array_type -> do
              case extractIdentStr field_ident of
                  "length" -> return (Int pos, Nothing)
                  s -> throwLocError' pos $ showString "Cannot evaluate attribute " $ prettyPrt field_ident " on array "
          Cls pos cls_ident -> do
              cls_map <- gets class_map
              cls <- case Map.lookup cls_ident cls_map of
                Nothing -> throwLocError' pos $ showString "Unknown type identifier: " $ prettyPrt' cls_ident
                Just cls -> return cls
              cls_field <-case Map.lookup field_ident (fields cls) of
                Nothing -> throwLocError' pos $ showString "Unknown class attribute: " $ prettyPrt' field_ident
                Just cm -> return cm
              case cls_field of
                Attr _ dtype _ -> return (dtype, Nothing)
                Meth {} -> throwLocError $ showString "Tried to access an attribute, however it is a function " $ prettyPrt' cls_ident

          _ -> throwLocError' pos $ showString "Cannot evaluate attribute " $ prettyPrt field_ident $ showString  " on expression of type " $ prettyPrt' expr_type
    EMethCall pos cls_expr meth_ident meth_exprs -> do
        (expr_type, _) <- evalExpr cls_expr
        case expr_type of
          Cls pos cls_ident -> do
              cls_map <- gets class_map
              cls <- case Map.lookup cls_ident cls_map of
                Nothing -> throwLocError' pos $ showString "Unknown type identifier: " $ prettyPrt' cls_ident
                Just cls -> return cls
              cls_field <-case Map.lookup meth_ident (fields cls) of
                Nothing -> throwLocError' pos $ showString "Unknown class method: " $ prettyPrt' meth_ident
                Just cm -> return cm
              case cls_field of
                Attr _ dtype _ -> throwLocError' pos $ showString "Tried to access an attribute, however it is a function " $ prettyPrt' cls_ident
                Meth _ ret_type _ args _ -> do
                    argTypes <- mapM checkDefArg args
                    unless (length argTypes == length meth_exprs) $ throwLocError $ showString "Cannot evaluate method " $ prettyPrt meth_ident " - wrong number of arguments applied"
                    forM_ (zip argTypes meth_exprs) checkType
                    return (ret_type, Nothing)

          _ -> throwLocError' pos $ showString "Cannot evaluate method " $ prettyPrt meth_ident $ showString  " on expression of type " $ prettyPrt' expr_type
        where
            checkType :: (Type, Expr) -> Analyser ()
            checkType (argtype, expr) = do
                (expr_type, _) <- evalExpr expr
                updatePosition (hasPosition expr_type) $ unless (TM.typeToBase argtype == TM.typeToBase expr_type) $ throwLocError $ showString "Expected type " $ prettyPrt argtype $ showString " got: " $ prettyPrt' expr_type
    EString pos s -> return (Str pos, Nothing)
    Neg pos ex -> do
        (ex_type, val) <- evalExpr ex
        updatePosition pos $ unless (TM.isInt ex_type) $ throwLocError $ showString "Cannot perform arithmetic negation value of " (prettyPrt' ex)
        return (ex_type, either (const Nothing) (\x -> return (Right (-x))) =<< val)
    Not pos ex -> do
        (ex_type, val) <- evalExpr ex
        updatePosition pos $ unless (TM.isBool ex_type) $ throwLocError $ showString "Cannot perform logic negation value of " (prettyPrt' ex)
        return (ex_type, either (Just . Left . not) (const Nothing) =<< val)
    EMul pos ex mo ex' -> do
        (ex_type, val) <- evalExpr ex
        (ex_type', val') <- evalExpr ex'
        updatePosition pos $ unless (TM.isInt ex_type && TM.isInt ex_type') $ throwLocError $ showString "Cannot perform arithmetic operation: " $ prettyPrt' expr
        return (Int pos, Just . Right =<< calcMulOp mo val val')
    EAdd pos ex (Plus _) ex' -> do
        (ex_type, val) <- evalExpr ex
        (ex_type', val') <- evalExpr ex'
        updatePosition pos $ unless (TM.isInt ex_type && TM.isInt ex_type' || TM.isStr ex_type && TM.isStr ex_type') $ throwLocError $ showString "Cannot perform arithmetic operation: " $ prettyPrt' expr
        return (ex_type, Just . Right =<< calcAddOp (+) val val')
    EAdd pos ex (Minus _) ex' -> do
        (ex_type, val) <- evalExpr ex
        (ex_type', val') <- evalExpr ex'
        updatePosition pos $ unless (TM.isInt ex_type && TM.isInt ex_type') $ throwLocError $ showString "Cannot perform arithmetic operation: " $ prettyPrt' expr
        return (Int pos, Just . Right =<< calcAddOp (-) val val')
    ERel pos (ECastNull _ (Cls _ cls_ident)) ro (ECastNull _ (Cls _ cls_ident')) -> do
        unless (TM.isEq ro || TM.isNEq ro) $ throwLocError' pos "Cannot use other relation operators than == and !="
        if cls_ident == cls_ident'
            then return (Bool pos, Just $ Left (TM.isEq ro))
            else throwLocError' pos "Wrong class type cast"
    ERel pos ex ro (ECastNull _ (Cls pos' cls_ident')) -> do
        unless (TM.isEq ro || TM.isNEq ro) $ throwLocError' pos "Cannot use other relation operators than == and !="
        (ex_type, val) <- evalExpr ex
        case ex_type of
          Cls _ cls_ident -> do
              if cls_ident == cls_ident'
                  then return (Bool pos, Nothing)
                  else throwLocError' pos' "Wrong class type cast"
          _ -> throwLocError' pos "Only class can be compared to null"
    ERel pos (ECastNull _ (Cls pos' cls_ident)) ro ex' -> do
        unless (TM.isEq ro || TM.isNEq ro) $ throwLocError' pos "Cannot use other relation operators than == and !="
        (ex_type, val) <- evalExpr ex'
        case ex_type of
          Cls _ cls_ident -> do
              if cls_ident == cls_ident
                  then return (Bool pos, Nothing)
                  else throwLocError' pos' "Wrong class type cast"
          _ -> throwLocError' pos "Only class can be compared to null"
    ERel pos ex ro ex' -> do
        (ex_type, val) <- evalExpr ex
        (ex_type', val') <- evalExpr ex'
        updatePosition pos $ unless (TM.isInt ex_type && TM.isInt ex_type' || TM.isBool ex_type && TM.isBool ex_type') $ throwLocError $ showString "Cannot compare (different types): " $ prettyPrt' expr
        return (Bool pos, Just . Left =<< calcRelOp ro val val')
    EAnd pos ex ex' -> do
        (ex_type, val) <- evalExpr ex
        (ex_type', val') <- evalExpr ex'
        updatePosition pos $ unless (TM.isBool ex_type && TM.isBool ex_type') $ throwLocError $ showString "Cannot perform conjunction: " $ prettyPrt' expr
        return (Bool pos, Just . Left =<< calcBinOp (&&) val val')
    EOr pos ex ex' -> do
        (ex_type, val) <- evalExpr ex
        (ex_type', val') <- evalExpr ex'
        updatePosition pos $ unless (TM.isBool ex_type && TM.isBool ex_type') $ throwLocError $ showString "Cannot perform disjunction: " $ prettyPrt' expr
        return (Bool pos, Just . Left =<< calcBinOp (||) val val')

    where
        calcMulOp :: MulOp -> Maybe (Either Bool Integer) -> Maybe (Either Bool Integer) -> Maybe Integer
        calcMulOp op a b = do
            pure_a <- a >>= extractInt
            pure_b <- b >>= extractInt
            case op of
                Times _ -> return (pure_a * pure_b)
                Div ma -> do
                    dividor <- checkDividor pure_b
                    return (div pure_a dividor)
                Mod ma -> do
                    dividor <- checkDividor pure_b
                    return (mod pure_a dividor)

        calcAddOp :: (Integer -> Integer -> Integer) -> Maybe (Either Bool Integer) -> Maybe (Either Bool Integer) -> Maybe Integer
        calcAddOp op a b = do
            pure_a <- a >>= extractInt
            pure_b <- b >>= extractInt
            return (op pure_a pure_b)

        calcRelOp :: (Ord a, Ord b) => RelOp -> Maybe (Either a b) -> Maybe (Either a b) -> Maybe Bool
        calcRelOp rel a b = do
            pure_a <- a
            pure_b <- b
            case (pure_a, pure_b) of
                (Left b1, Left b2) -> return (fun rel b1 b2)
                (Right i1, Right i2) -> return (fun rel i1 i2)
                _ -> Nothing
            where
                fun rel a b = case rel of
                    LTH _ -> a < b
                    LE _ -> a <= b
                    GTH _ -> a > b
                    GE _ -> a >= b
                    EQU _ -> a == b
                    NE _ -> a /= b

        checkDividor :: Integer -> Maybe Integer
        checkDividor x = if x == 0 then Nothing else return x

        calcBinOp :: (Bool -> Bool -> Bool) -> Maybe (Either Bool Integer) -> Maybe (Either Bool Integer) -> Maybe Bool
        calcBinOp fun a b = do
            pure_a <- a >>= extractBool
            pure_b <- b >>= extractBool
            return (fun pure_a pure_b)

        extractInt :: Either Bool Integer -> Maybe Integer
        extractInt = \case
            Left _ -> Nothing
            Right x -> return x

        extractBool :: Either Bool Integer -> Maybe Bool
        extractBool = \case
            Left x -> return x
            Right _ -> Nothing

matchType :: Type -> Type -> Analyser ()
matchType t1 t2 = do
    case b2 of
      TM.Cls id -> case b1 of
        TM.Cls id' -> do
            compatible <- getChildren id'
            if id' `elem` compatible
                then return ()
                else throwLocError $ showString "Mismatching class types: " $ prettyPrt b1 $ showString " and " $ prettyPrt' b2
        __ -> throwLocError $ showString "Mismatching types: " $ prettyPrt b1 $ showString " and " $ prettyPrt' b2
      _ -> unless (b1 == b2) $ throwLocError $ showString "Mismatching types: " $ prettyPrt b1 $ showString " and " $ prettyPrt' b2

    return ()
    where
        b1 = TM.typeToBase t1
        b2 = TM.typeToBase t2
        getChildren :: Ident -> Analyser [Ident]
        getChildren cls_ident = do
            classes <- gets class_map
            case Map.lookup cls_ident classes of
              Nothing -> throwLocError $ showString "Class not found: " $ prettyPrt' cls_ident
              Just class_info -> do
                  case extends class_info of
                    Nothing -> return [cls_ident]
                    Just parent_id -> do
                        parents <- getChildren parent_id
                        return (cls_ident : parents)

declItem :: Type -> Item -> Analyser VarMap
declItem item_type (NoInit pos ident) = do
    var_map <- asks variable_map
    init_depth <- asks block_depth
    loc <- getLoc
    when (TM.isVoid item_type) $ throwLocError' pos "Cannot declare variable of type void."
    when (member ident var_map) $ do
        when (init_depth <= depth (var_map ! ident)) $ throwLocError' pos $ showString "Cannot initialise value with name: " $ prettyPrt ident " in the same block."
        var <- getVariable ident
        when (TM.isFun var) $ throwLocError' pos $ showString "Cannot initialise value with name: " $ prettyPrt ident ". There is already a function with the same name"
    modify (\s -> s {loc_map = insert loc item_type (loc_map s)})
    return (insert ident (LocInfo loc init_depth) var_map)

declItem item_type (Init pos ident expr) = do
    (init_type, _) <- evalExpr expr
    matchType item_type init_type
    declItem item_type (NoInit pos ident)

checkStmt :: Stmt -> Analyser (VarMap, Bool)
checkStmt stmt = case stmt of
    Empty _ -> unchanged
    BStmt pos block -> updatePosition pos $ checkBlock block >>= update_ret_only
    Decl pos itemType items -> do
        ctx <- ask
        let depth = block_depth ctx
        let is_block' = is_inside_block ctx
        let ret_type' = return_type ctx
        unless is_block' $ throwLocError "Cannot declare variable outside block!"
        new_varmap <- foldM (\var_map itemdecl -> local (const (Context pos var_map depth ret_type' is_block')) (declItem itemType itemdecl)) (variable_map ctx) items
        return (new_varmap, False)
    Ass pos lvalue expr -> do
        vartype <- fst <$> evalExpr lvalue
        (expr_type, _) <- evalExpr expr
        matchType vartype expr_type
        unchanged
    Incr pos expr -> do
        vartype <- fst <$> evalExpr expr
        updatePosition pos $ unless (TM.isInt vartype) $ throwLocError $ showString "Cannot increase value of non int, variable: " $ prettyPrt expr $ showString " has type: " $ prettyPrt' vartype
        unchanged
    Decr pos expr -> do
        vartype <- fst <$> evalExpr expr
        updatePosition pos $ unless (TM.isInt vartype) $ throwLocError $ showString "Cannot decrease value of non int, variable: " $ prettyPrt expr $ showString " has type: " $ prettyPrt' vartype
        unchanged
    Ret pos expr -> do
        (expr_type, _) <- evalExpr expr
        mret_type <- asks return_type
        updatePosition pos $ case mret_type of
          Nothing -> throwLocError $ showString "Function tried to return: " $ prettyPrt expr_type  " when a value was already returned."
          Just ret_type -> do
              when (ret_type == TM.Void) $ throwLocError "Void function cannot return value"
              unless (ret_type == TM.typeToBase expr_type) $ throwLocError $ showString "Found return with type: " $ prettyPrt expr_type $ showString ", expected return type:" $ prettyPrt' ret_type
        update_ret_only True
    VRet pos -> do
        mret_type <- asks return_type
        updatePosition pos $ unless (maybe True (== TM.Void) mret_type) $ throwLocError $ showString "Found return without value, expected return type:" $ prettyPrt' (fromJust mret_type)
        update_ret_only True
    Cond pos expr stmt -> do
        (expr_type, static_value) <- evalExpr expr
        updatePosition pos $ unless (TM.isBool expr_type) $ throwLocError $ showString "If condition must evaluate to bool, got: " $ prettyPrt expr $ showString " which evaluates to " $ prettyPrt' expr_type
        (_, did_return) <- ctxDisableBlock $ checkStmt stmt
        case static_value of
            Just (Left True) -> update_ret_only did_return
            _ -> unchanged
    CondElse pos expr stmt stmt' -> do
        (expr_type, static_value) <- evalExpr expr
        updatePosition pos $ unless (TM.isBool expr_type) $ throwLocError $ showString "If condition must evaluate to bool, got: " $ prettyPrt expr $ showString " which evaluates to " $ prettyPrt' expr_type
        (_, did_return) <- ctxDisableBlock $ checkStmt stmt
        (_, did_return') <- ctxDisableBlock $ checkStmt stmt'
        case static_value of
            Just (Left value) -> if value then update_ret_only did_return else update_ret_only did_return'
            _ -> update_ret_only (did_return && did_return')
    While pos expr stmt -> do
        (expr_type, static_value) <- evalExpr expr
        updatePosition pos $ unless (TM.isBool expr_type) $ throwLocError $ showString "If condition must evaluate to bool, got: " $ prettyPrt expr $ showString " which evaluates to " $ prettyPrt' expr_type
        checkStmt stmt
        case static_value of
            Just (Left True) -> update_ret_only True
            _ -> unchanged
    For pos dtype ident expr stmt -> do
        range_type <- fst <$> evalExpr expr
        unless (TM.isArray range_type) $ throwLocError' pos $ showString "For loops can iterate only over array, got: " $ prettyPrt' range_type
        unless (fromJust (TM.getArrayItemType (TM.typeToBase range_type)) == TM.typeToBase dtype) $ throwLocError' pos $ showString "For loops can iterate only over array, got: " $ prettyPrt' dtype
        act_ctx@(Context _ var_map depth did_return _) <- ask
        did_return <- snd <$> local (const (Context pos var_map (depth + 1) did_return False)) loop_ctx
        return (var_map, did_return)
        where
            loop_ctx = do
                var_map <- declItem dtype (TM.noInitNP ident)
                act_ctx@(Context _ _ depth did_return _) <- ask
                local (const (Context pos var_map (depth + 1) did_return True)) (checkStmt stmt)

    SExp pos expr -> do
        updatePosition pos $ evalExpr expr
        unchanged
    where
        unchanged :: Analyser (VarMap, Bool)
        unchanged = update_ret_only False

        update_ret_only :: Bool -> Analyser (VarMap, Bool)
        update_ret_only did_return = do
            var_map <- asks variable_map
            return (var_map, did_return)

checkBlock :: Block -> Analyser Bool
checkBlock (Block pos stmts) = do
    ctx <- ask
    updatePosition pos $ foldM foldFun (variable_map ctx , False) stmts <&> snd
    where
        foldFun :: (VarMap, Bool) -> Stmt -> Analyser (VarMap, Bool)
        foldFun (var_map, did_return) stmt = do
            act_ctx <- ask
            let ret_type = if did_return then Nothing else return_type act_ctx
            local (const (Context pos var_map (block_depth act_ctx + 1) (if did_return then Nothing else ret_type) True)) (checkStmt stmt)


analyseMain :: Analyser ()
analyseMain = do
    var_map <- asks variable_map
    unless (member (Ident "main") var_map) $
        throwError "No main function found in program!"
    main_function <- getVariable (Ident "main")
    case main_function of
      Fun pos returnType argTypes -> do
          updatePosition pos $ unless (TM.isInt returnType) $
            throwLocError "Expected main to return int."
          updatePosition pos $ unless (null argTypes) $
            throwLocError "Expected main accept no arguments"
      _ -> throwLocError "Expected main to be a function"

runAnalysis :: Program -> Analyser ()
runAnalysis (Program pos defs) = do
    ctx <- ask
    let init_varmap = variable_map ctx
    let block_depth' = block_depth ctx

    let def_map = fromList (zip (map hasIdent defs) defs)
    unless (length def_map == length defs) $ throwLocError "TopDef redeclaration"
    -- Declare built in functions
    predefined_varmap <- foldM (\var_map funcdecl -> local (const (Context BNFC'NoPosition var_map block_depth' Nothing False)) (declTopDef def_map funcdecl)) init_varmap builtInFunctions
    -- Declare functions & classes
    final_varmap <- foldM (\var_map decl -> local (const (Context (hasPosition decl) var_map block_depth' Nothing False)) (declTopDef def_map decl)) predefined_varmap defs
    -- Analyse Main
    local (const (Context BNFC'NoPosition final_varmap block_depth' (Just TM.Int) False)) analyseMain
    classes <- gets class_map
    -- Analyse other functions
    local (const (Context BNFC'NoPosition final_varmap block_depth' Nothing False)) (mapM_ analyseFunction defs)
    -- Analyse methods
    local (const (Context BNFC'NoPosition final_varmap block_depth' Nothing False)) (mapM_ (\(ident, class_info) -> analyseClsMethods (Cls BNFC'NoPosition ident) class_info) (Map.toList classes))

    where
        declArg ::  Arg -> Analyser VarMap
        declArg (Arg pos arg_type ident) = updatePosition pos $ declItem arg_type (TM.noInitNP ident)

        analyseFunction :: TopDef -> Analyser ()
        analyseFunction (FnDef pos ret_type fun_ident fun_args fun_block) = do
            ctx <- ask
            let outer_varmap = variable_map ctx
            let outer_block_depth = block_depth ctx
            fun_varmap <- foldM (\var_map arg -> local (const (Context BNFC'NoPosition var_map (outer_block_depth + 1) Nothing False)) (declArg arg)) outer_varmap fun_args
            did_return <- local (const (Context BNFC'NoPosition fun_varmap (outer_block_depth + 1) (Just (TM.typeToBase ret_type)) False)) (checkBlock fun_block)
            when (not (TM.isVoid ret_type) && not did_return) $ throwLocError $ showString "Function " $ prettyPrt fun_ident $ showString " did not return anything, when it was expected to return " $ prettyPrt' ret_type

        analyseFunction ClDef {} = return ()

        analyseClsMethods :: Type -> ClassInfo -> Analyser ()
        analyseClsMethods self (ClassInfo _ fields) = do
            let cls_attrs = map (\case
                    Attr _ argtype ident -> (argtype, TM.noInitNP ident)
                    _ -> undefined) (filter TM.isAttr (elems fields))
            ctx <- ask
            let outer_varmap = variable_map ctx
            let outer_block_depth = block_depth ctx
            cls_env <- foldM (\var_map (argtype, item) -> local (const (Context BNFC'NoPosition var_map (outer_block_depth + 1) Nothing False)) (declItem argtype item)) outer_varmap cls_attrs
            cls_env' <- local (const (Context BNFC'NoPosition cls_env (outer_block_depth + 1) Nothing False)) $ declItem self (TM.noInitNP (Ident "self"))
            let cls_methods = map (\case
                    Meth pos ret_type ident args block -> FnDef pos ret_type ident args block
                    _ -> undefined) (filter TM.isMeth (elems fields))
            local (const (Context BNFC'NoPosition cls_env' (outer_block_depth + 1) Nothing True)) (mapM_ analyseFunction cls_methods)


analyse :: Program -> IO ()
analyse program = do
    let starting_state = AState Map.empty Map.empty S.empty
    analysis_result <- runExceptT $ runReaderT (evalStateT (runAnalysis program) starting_state) (Context BNFC'NoPosition Map.empty 0 Nothing False)
    case analysis_result of
      Left s -> do
          hPutStrLn stderr $ showString "ERROR\n" s
          exitFailure
      _ -> return ()

    return ()
    