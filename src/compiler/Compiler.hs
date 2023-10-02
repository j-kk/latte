{-# LANGUAGE LambdaCase #-}
module Compiler (runCompilator) where
import AbsLatte (Expr, Ident (Ident), Expr' (..), MulOp' (..), AddOp' (..), RelOp, Stmt, Stmt' (..), Item, Type, Item' (..), Block' (Block), TopDef' (FnDef, ClDef), TopDef, Arg' (Arg), Program, Program' (Program), ClMember, ClMember' (Attr, Meth))
import CompilerUtils (CM, InstrS, Memory (Local, Param, Attribute), CompilerEnv (variableMem, CompilerEnv, inClassMethod), throwImpossible, instrSS, instrS, Register (EAX, ECX, ESP, EDX), Instr (..), Operand (Reg, LitNumber, Mem, LitString, ArrElem, Addr, AttrAddr, MethAddr, VTMLit), litTrue, litFalse, CompilerState (strings, funTypes, variables, CompilerState, classDefs, vms), Label (StringLabel, JumpLabel, FuncLabel), SingleOp (NEG, INC, DEC), BinOp (..), ZeroOp (CDQ), getNewLabel, matchJumpOp, JumpOp (JMP, JE), dword, builtInFunctions, ClassDef (meths, attrs, extends, ClassDef), VMS (vattr, vmeth, VMS), vmtLabel, litNull, methodLabel)
import TypeMatchUtils as TM ( typeToBase, BaseType(..), extractIdentStr, noPosition, getArrayItemType, MaybeIdent (maybeIdent), baseToType, isFnDef )
import Control.Monad.Reader (MonadReader(ask, local), asks, ReaderT (runReaderT))
import Data.Map as M ( insert, lookup, size, fromList, empty, elems, Map, union, toList )
import Control.Monad.State (gets, modify, MonadState (get), evalStateT)
import Control.Monad (foldM)
import PrintUtils (prettyPrt, prettyPrt')
import qualified AbsLatte as Abs;
import Control.Lens (Field14(_14))
import Data.List (nubBy)
import Control.Monad.Except ( foldM, ExceptT )

getVar :: Ident -> CM (Memory, BaseType)
getVar ident = do
  env <- ask
  case M.lookup ident (variableMem env) of
    Nothing -> throwImpossible "Uninitialized variable"
    Just res -> return res

getFunRet :: Ident -> CM BaseType
getFunRet ident = do
  functions <- gets funTypes
  case M.lookup ident functions of
    Nothing -> throwImpossible $ "Unknown function identifier " ++ show ident
    Just bt -> return bt

defaultValue :: BaseType -> CM Operand
defaultValue dtype =
  case dtype of
    Int -> return $ LitNumber 0
    Bool -> return litFalse
    Str -> do
      strings <- gets strings
      empty_str <- case M.lookup "" strings of
        Nothing -> do
            let i = fromIntegral $ M.size strings
            modify (\st -> st {strings = M.insert "" (StringLabel i "") strings})
            return i
        Just (StringLabel i _) -> return i
        _ -> throwImpossible "Non string label in strings storage"
      return $ LitString empty_str
    Cls _ -> return litNull
    _ -> throwImpossible $ "Type " ++ show dtype ++ " has no default value"

getVMSMethod :: Ident -> Ident -> CM (TM.BaseType, Integer, Ident)
getVMSMethod cls_ident meth_ident = do
    clss_vms <- gets vms
    case M.lookup cls_ident clss_vms of
      Nothing -> throwImpossible "Class vms not found"
      Just vms -> case M.lookup meth_ident (M.fromList (vmeth vms)) of
        Nothing -> throwImpossible "Method not found"
        Just bt -> return bt


getExprType :: Expr -> CM TM.BaseType
getExprType = \case
  EVar _ ident -> snd <$> getVar ident
  ELitInt _ _ -> return Int
  ELitTrue _ -> return Bool
  ELitFalse _ -> return Bool
  EApp _ ident _ -> getFunRet ident
  EString _ _ -> return Str
  Neg _ _ -> return Int
  Not _ _ -> return Bool
  EMul {} -> return Int
  EAdd _ ex (Plus _) _ -> getExprType ex
  EAdd _ ex (Minus _) _ -> return Int
  ERel _ ex ro ex' -> return Bool
  EAnd _ ex ex' -> return Bool
  EOr _ ex ex' -> return Bool
  EArrElem _ ex _ -> do
    inner_type <- getExprType ex
    return $ Array inner_type
  EInitArr _ arr_type _ -> return $ Array (typeToBase arr_type)
  EClassVar _ class_expr var_ident -> do
    expr_type <- getExprType class_expr
    case expr_type of
        Cls class_ident -> do
          class_defs <- gets classDefs
          case M.lookup class_ident class_defs of
            Just class_def -> case M.lookup var_ident (attrs class_def) of
              Nothing -> throwImpossible "Attribute not found!"
              Just ret_type -> return ret_type
            Nothing -> throwImpossible "Class not found"
        Array arr_type -> return (Array arr_type)
        _ -> throwImpossible $ showString "Not a class! " $ show class_expr
  EMethCall _ class_expr meth_ident _ -> do
    expr_type <- getExprType class_expr
    class_ident <- case expr_type of
          Cls ident -> return ident
          _ -> throwImpossible "Not a class!"
    class_defs <- gets classDefs
    (Fun ret_type _, _, _) <- getVMSMethod class_ident meth_ident
    return ret_type

  ENewCls _ (Abs.Cls _ ident) -> return $ Cls ident
  ENewCls _ _ -> throwImpossible "Expected class identifier!"
  ECastNull _ (Abs.Cls _ ident) -> return $ Cls ident
  ECastNull _ _ -> throwImpossible "Expected class identifier!"

getVMS :: Expr -> CM VMS
getVMS expr = do
  Cls cls_ident <- getExprType expr
  vms <- gets vms
  case M.lookup cls_ident vms of
    Just vms -> return vms
    Nothing -> throwImpossible "No VMS defined!"

getVMAttr :: Expr -> Ident -> CM (Memory, BaseType)
getVMAttr expr ident = do
  vms <- getVMS expr
  case M.lookup ident (vattr vms) of
    Nothing -> throwImpossible "No attribute found in VMS."
    Just attr -> return attr


getVMMeth :: Expr -> Ident -> CM (BaseType, Integer, Ident)
getVMMeth expr ident = do
  vms <- getVMS expr
  case M.lookup ident (M.fromList (vmeth vms)) of
    Nothing -> throwImpossible "No method found in VMS."
    Just attr -> return attr

transExpr :: Expr -> CM InstrS
transExpr expr = case expr of
  EVar _ ident -> transEVar ident instr_attr instr_loc
    where
      instr_attr loc =
          [ MOV (Reg EAX) (Mem $ Param 1)
          , MOV (Reg EAX) (Mem loc)
          ]
      instr_loc loc = [MOV (Reg EAX) (Mem loc)]
  ELitInt _ n ->
    return $ instrS (MOV (Reg EAX) (LitNumber n))
  ELitTrue _ ->
    return $ instrS (MOV (Reg EAX) litTrue)
  ELitFalse _ ->
    return $ instrS (MOV (Reg EAX) litFalse)
  EApp _ ident@(Ident funName) exs -> transLValue expr
  EArrElem {} -> do
    instr_acc <- transLValue expr
    return $ instr_acc . instrSS [MOV (Reg EAX) (Addr 0 EAX)]
  EClassVar _ cls_expr var_ident -> do
    type_ <- getExprType expr
    case type_ of
        (Array _) -> transExpr (EArrElem Abs.BNFC'NoPosition cls_expr (ELitInt Abs.BNFC'NoPosition (-1)))
        _       -> do
            instr_acc <- transLValue expr
            return $ instr_acc . instrSS [MOV (Reg EAX) (Addr 0 EAX)]
  ECastNull _ _ -> return $ instrS $ MOV (Reg EAX) litNull
  EMethCall {} -> transLValue expr
  EInitArr {} -> transLValue expr
  ENewCls {} -> transLValue expr

  EString _ s -> do
    str_id <- getStrLabel s
    return $ instrS (LEA (Reg EAX) (LitString str_id))
    where
      getStrLabel :: String -> CM Integer
      getStrLabel str = do
        ctx_strings <- gets strings
        case M.lookup str ctx_strings of
          Nothing -> do
            let i = fromIntegral $ M.size ctx_strings
            modify (\st -> st {strings = M.insert str (StringLabel i str) ctx_strings})
            return i
          Just lbl@(StringLabel i _) -> return i
          Just x -> throwImpossible $ "String map contains non-string label: " ++ show x
  Neg _ ex -> do
    expr_instrs <- transExpr ex
    return $ expr_instrs . instrS (SingleInstr NEG (Reg EAX))
  Not _ ex -> do
    expr_instrs <- transExpr ex
    return $ expr_instrs . instrS (BinInstr XOR (Reg EAX) litTrue)
  EMul _ e1 (Times _) e2 -> do
      instr_e1 <- transExpr e1
      instr_e2 <- transExpr e2
      return $
        instr_e1 .
        instrS (PUSH (Reg EAX)) .
        instr_e2 .
        instrS (POP (Reg ECX)) .
        instrS (BinInstr MUL (Reg EAX) (Reg ECX))
  EMul _ e1 mo e2 -> do
      let ret = case mo of
                Mod _ -> instrS (MOV (Reg EAX) (Reg EDX))
                _ -> id
      instr_e1 <- transExpr e1
      instr_e2 <- transExpr e2
      return $
        instr_e1 .
        instrS (PUSH (Reg EAX)) .
        instr_e2 .
        instrS (MOV (Reg ECX) (Reg EAX)) .
        instrS (POP (Reg EAX)) .
        instrS (ZeroInstr CDQ) .
        instrS (BinInstr DIV (Reg EAX) (Reg ECX)) .
        ret
  EAdd loc e1 ao e2 -> do
    add_type <- getExprType e1
    case add_type of
      Str -> transExpr (EApp noPosition (Ident "____concatStr") [e1, e2])
      _   -> do
        let op = case ao of
                Plus _   -> ADD
                Minus _ -> SUB
        instr_e1 <- transExpr e1
        instr_e2 <- transExpr e2
        return $
          instr_e2 .
          instrS (PUSH (Reg EAX)) .
          instr_e1 .
          instrS (POP (Reg ECX)) .
          instrS (BinInstr op (Reg EAX) (Reg ECX))
  ERel {} -> bin_op_handle
  EAnd {} -> bin_op_handle
  EOr {} -> bin_op_handle

  where
    bin_op_handle = do
      falseLabel <- getNewLabel
      trueLabel <- getNewLabel
      afterLabel <- getNewLabel
      cmp_instr <- transComp expr trueLabel falseLabel
      return $ cmp_instr . cmp_epilog trueLabel falseLabel afterLabel
    cmp_epilog trueLabel falseLabel afterLabel =
        instrSS
        [ Lab $ JumpLabel falseLabel
        , MOV (Reg EAX) litFalse
        , JUMP JMP afterLabel
        , Lab $ JumpLabel trueLabel
        , MOV (Reg EAX) litTrue
        , Lab (JumpLabel afterLabel)
        ]


transComp :: Expr -> Integer -> Integer -> CM InstrS
transComp expr trueLabel falseLabel = case expr of
  ELitTrue _ -> return $ instrS $ JUMP JMP trueLabel
  ELitFalse _ -> return $ instrS $ JUMP JMP falseLabel
  Not _ ex -> transComp ex falseLabel trueLabel
  ERel _ e1 ro e2 -> do
    expr_type <- getExprType e1
    case expr_type of
      Str -> do
        cmpCall <- transExpr (EApp noPosition (Ident "____compareStr") [e1, e2])
        instr_cmp <- transComp expr trueLabel falseLabel
        return $ cmpCall . instrSS
          [ BinInstr CMP (Reg EAX) litFalse
          , JUMP (matchJumpOp ro) trueLabel
          , JUMP JMP falseLabel
          ]
      _ -> do
        instr_e1 <- transExpr e1
        instr_e2 <- transExpr e2
        return $
          instr_e1 .
          instrS (PUSH (Reg EAX)) .
          instr_e2 .
          instrSS
          [ POP (Reg ECX)
          , BinInstr CMP (Reg ECX) (Reg EAX)
          , JUMP (matchJumpOp ro) trueLabel
          , JUMP JMP falseLabel
          ]
  EAnd _ e1 e2 -> do
    midLabel <- getNewLabel
    instr_e1 <- transComp e1 midLabel falseLabel
    instr_e2 <- transComp e2 trueLabel falseLabel
    return $
      instr_e1 .
      instrS (Lab $ JumpLabel midLabel) .
      instr_e2
  EOr _ e1 e2 -> do
    midLabel <- getNewLabel
    instr_e1 <- transComp e1 trueLabel midLabel
    instr_e2 <- transComp e2 trueLabel falseLabel
    return $
      instr_e1 .
      instrS (Lab $ JumpLabel midLabel) .
      instr_e2
  _ -> do
    instr <- transExpr expr
    return $
      instr .
      instrSS
        [ BinInstr CMP (Reg EAX) litTrue
        , JUMP JE trueLabel
        , JUMP JMP falseLabel
        ]

transEVar :: Ident -> (Memory -> [Instr]) -> (Memory -> [Instr]) -> CM InstrS
transEVar ident instr_attr instr_loc = do
    env <- ask
    var_map <- asks variableMem
    loc <- case M.lookup ident var_map of
      Nothing -> throwImpossible "Undeclared variable"
      Just var -> return (fst var)
    env <- ask
    case loc of
        Attribute _ -> return $ instrSS $ instr_attr loc
        _           -> return $ instrSS $ instr_loc loc


transLValue :: Expr -> CM InstrS
transLValue e = case e of
  EVar _ ident -> transEVar ident instr_attr instr_loc
    where
      instr_attr loc =
          [ MOV (Reg EAX) (Mem $ Param 1)
          , LEA (Reg EDX) (Mem loc)
          , MOV (Reg EAX) (Reg EDX)
          ]
      instr_loc loc = [LEA (Reg EAX) (Mem loc)]
  EArrElem _ arr_expr pos_expr -> do
    instr_pos <- transExpr pos_expr
    instr_acc <- transLValue arr_expr

    return $
      instr_pos .
      instrS (PUSH (Reg EAX)) .
      instr_acc .
      instr_retr

    where
      instr_retr = case arr_expr of
        EMethCall{} -> instr_access
        EApp{}      -> instr_access
        ENewCls{}   -> instr_access
        _           -> instr_assign

      instr_assign = instrSS [
        POP (Reg EDX),
        SingleInstr INC (Reg EDX),
        MOV (Reg EAX) (Addr 0 EAX),
        LEA (Reg EAX) (ArrElem EAX EDX dword)
        ]

      instr_access = instrSS [
        POP (Reg EDX),
        SingleInstr INC (Reg EDX),
        LEA (Reg EAX) (ArrElem EAX EDX dword)
        ]

  EClassVar _ class_expr attr -> do
    instr_acc <- transLValue class_expr
    (Attribute aloc, _) <- getVMAttr class_expr attr
    return $ instr_acc . code aloc
    where
      code aloc = case class_expr of
        EApp{}      -> instr_access aloc
        EMethCall{} -> instr_access aloc
        ENewCls{}      -> instr_access aloc
        _           -> instr_assign aloc
      instr_access i = instrSS [LEA (Reg EAX) (AttrAddr i EAX)]
      instr_assign i =
            instrSS [MOV (Reg EDX) (Addr 0 EAX), LEA (Reg EAX) (AttrAddr i EDX)]


  EMethCall _ class_expr meth_ident args_exprs -> do
    (Fun ret_type _, offset, _) <- getVMMeth class_expr meth_ident
    instr_acc <- transExpr class_expr
    instrs_args <- mapM transExpr args_exprs
    let instr_args = foldr (\instr acc -> instr . instrS (PUSH (Reg EAX)) . acc ) id (reverse instrs_args)

    return $
      instr_args .
      instr_acc .
      instrSS [
        PUSH (Reg EAX),
        MOV (Reg EAX) (Addr 0 EAX),
        CALLM (MethAddr offset EAX),
        BinInstr ADD (Reg ESP) (LitNumber (dword * (1 + fromIntegral (length instrs_args))))
      ]

  EApp pos fun_ident args_exprs -> do
    inClassMethod <- asks inClassMethod
    case inClassMethod of
      Nothing -> handleEApp
      Just cls_ident -> do
        vms <- gets vms
        case M.lookup cls_ident vms of
          Nothing -> throwImpossible "Undefined class!"
          Just cls_vms -> case M.lookup fun_ident (M.fromList (vmeth cls_vms)) of
            Nothing -> handleEApp
            Just _ -> transLValue (EMethCall pos (EVar Abs.BNFC'NoPosition (Ident "self")) fun_ident args_exprs) 

      where
        handleEApp = do
          instrs_args <- mapM transExpr args_exprs
          let instr_args = foldr (\instr acc -> instr . instrS (PUSH (Reg EAX)) . acc ) id (reverse instrs_args)
          ret_type <- getFunRet fun_ident
          return $
            instr_args .
            instrSS [
              CALL (extractIdentStr fun_ident),
              BinInstr ADD (Reg ESP) (LitNumber (dword * fromIntegral (length args_exprs)))
            ]

  ENewCls _ (Abs.Cls _ cls_ident) -> do
    vms <- getVMS e
    let numMem = (1 +) $ fromIntegral $ M.size $ vattr vms
    let vtable = if vmeth vms /= []
            then instrSS [
              LEA (Reg ECX) (VTMLit $ vmtLabel cls_ident),
              MOV (Addr 0 EAX) (Reg ECX)
              ]
            else id
    return
        $ instrSS
              [ PUSH $ LitNumber (numMem * dword)
              , CALL "malloc"
              , BinInstr ADD (Reg ESP) (LitNumber dword)
              ]
        . vtable

  EInitArr _ arr_type arr_size -> do
    instr_size <- transExpr arr_size
    return $ instr_size . instrSS
        [ PUSH $ Reg EAX
        , SingleInstr INC (Reg EAX)
        , PUSH $ LitNumber dword
        , PUSH $ Reg EAX
        , CALL "calloc"
        , BinInstr ADD (Reg ESP) (LitNumber $ dword * 2)
        , POP (Reg EDX)
        , MOV (Addr 0 EAX) (Reg EDX)
        ]

  _ -> throwImpossible "Cannot calculate lvalue"


transStmt :: Stmt -> CM (CompilerEnv, InstrS)
transStmt stmt = case stmt of
  Empty _ -> do
    env <- ask
    return (env, id)
  BStmt _ (Block _ stmts) -> do
    env <- ask
    instrBlock <- snd <$> foldM fun (env, id) stmts
    return (env, instrBlock)
    where
      fun (env, instr) stmt = do
        (env', instr') <- local (const env) (transStmt stmt)
        return (env', instr . instr')

  Decl _ itemsType items -> do
    env <- ask
    foldM (\(env', instrs) item -> local (const env') (declare itemsType instrs item)) (env, id) items
    where
      declare :: Type -> InstrS -> Item -> CM (CompilerEnv, InstrS)
      declare dtype instr_prev item = do
        let base_type = typeToBase dtype
        state <- get
        let loc = Local (variables state + 1)
        modify (\st -> st { variables  = variables state + 1})
        (ident, instr_decl) <- case item of
          NoInit _ ident -> do
            value <- defaultValue base_type
            case base_type of
              Str -> return (ident, instrSS [MOV (Reg EAX) value, MOV (Mem loc) (Reg EAX)])
              _ -> return (ident, instrS (MOV (Mem loc) value))
          Init _ ident ex -> do
            instrValue <- transExpr ex
            return (ident, instrValue . instrS (MOV (Mem loc) (Reg EAX)))
        env <- ask
        return (env {variableMem = M.insert ident (loc, base_type) (variableMem env)}, instr_prev . instr_decl)

  Ass _ lvalue ex -> do
    instr_acc <- transLValue lvalue
    instr_ex <- transExpr ex
    env <- ask
    return
      ( env
      , instr_acc .
        instrS (PUSH (Reg EAX)) .
        instr_ex .
        instrSS [
          POP (Reg EDX),
          MOV (Addr 0 EDX) (Reg EAX)
          ]
      )
  Incr _ expr -> do
    instr_acc <- transLValue expr
    env     <- ask
    return (env, instr_acc . instrSS [SingleInstr INC $ Addr 0 EAX])
  Decr _ expr -> do
    instr_acc <- transLValue expr
    env     <- ask
    return (env, instr_acc . instrSS [SingleInstr DEC $ Addr 0 EAX])
  Ret _ ex -> do
    instr_ex <- transExpr ex
    env <- ask
    return (env, instr_ex . instrS FunEpilog)
  VRet _ -> do
    env <- ask
    return (env, instrS FunEpilog)
  Cond _ ex st -> do
    trueLabel <- getNewLabel
    afterLabel <- getNewLabel

    instr_cmp <- transComp ex trueLabel afterLabel
    instr_true <- snd <$> transStmt (BStmt noPosition (Block noPosition [st]))
    let instr = instr_cmp .
                instrS (Lab $ JumpLabel trueLabel) .
                instr_true .
                instrS (Lab $ JumpLabel afterLabel)
    env <- ask
    return (env, instr)

  CondElse _ ex st_true st_false -> do
    trueLabel <- getNewLabel
    falseLabel <- getNewLabel
    afterLabel <- getNewLabel

    instr_cmp <- transComp ex trueLabel falseLabel
    instr_true <- snd <$> transStmt (BStmt noPosition (Block noPosition [st_true]))
    instr_false <- snd <$> transStmt (BStmt noPosition (Block noPosition [st_false]))
    let instr = instr_cmp .
                instrS (Lab $ JumpLabel trueLabel) .
                instr_true .
                instrS (JUMP JMP afterLabel) .
                instrS (Lab $ JumpLabel falseLabel) .
                instr_false .
                instrS (Lab $ JumpLabel afterLabel)
    env <- ask
    return (env, instr)
  While _ ex st -> do
    env <- ask

    loopLabel <- getNewLabel
    condLabel <- getNewLabel
    afterLabel <- getNewLabel

    instrComp <- transComp ex loopLabel afterLabel
    instrLoop <- snd <$> transStmt (BStmt noPosition (Block noPosition [st]))

    let instr =
          instrSS [
            JUMP JMP condLabel
          , Lab $ JumpLabel loopLabel
          ]
          . instrLoop
          . instrS (Lab $ JumpLabel condLabel)
          . instrComp
          . instrS (Lab $ JumpLabel afterLabel)

    return (env, instr)

  For _ iter_type iter_init array stmt -> do
    arr_type <- getExprType array
    let iterator  = Ident "____for_iter"
    let array_ptr = Ident "____arr_ptr"
    let block = BStmt Abs.BNFC'NoPosition $ Block Abs.BNFC'NoPosition [
          Decl Abs.BNFC'NoPosition (Abs.Int Abs.BNFC'NoPosition) [NoInit Abs.BNFC'NoPosition iterator],
          Decl Abs.BNFC'NoPosition (baseToType arr_type) [Init Abs.BNFC'NoPosition array_ptr array],
          While Abs.BNFC'NoPosition
                (ERel Abs.BNFC'NoPosition (EVar Abs.BNFC'NoPosition iterator) (Abs.LTH Abs.BNFC'NoPosition) (Abs.EClassVar Abs.BNFC'NoPosition (EVar Abs.BNFC'NoPosition array_ptr) (Ident "length")))
                (BStmt Abs.BNFC'NoPosition $ Block Abs.BNFC'NoPosition
                    [ Decl Abs.BNFC'NoPosition iter_type [Init Abs.BNFC'NoPosition iter_init (EArrElem Abs.BNFC'NoPosition (EVar Abs.BNFC'NoPosition array_ptr) (EVar Abs.BNFC'NoPosition iterator))]
                    , stmt
                    , Incr Abs.BNFC'NoPosition (EVar Abs.BNFC'NoPosition iterator)
                    ]
                )
          ]

    transStmt block

  SExp loc ex -> do
    expr_type <- getExprType ex
    env <- ask
    case expr_type of
      Fun bt bts ->
        throwImpossible $ showString "Cannot print fun " $ show ex
      _ -> do
          instr <- transExpr ex
          return (env, instr)



transMethods :: Ident -> ClMember -> CM InstrS
transMethods _ Attr{} = return id
transMethods cls_ident (Meth pos ret_type method_ident args block) = do
  modify (\state -> state {
          variables = 0
        })
  vms <- gets vms
  case M.lookup cls_ident vms of
    Nothing -> throwImpossible "Class not found in transMethod"
    Just vms -> do
          let args' = M.fromList $ zipWith
                        (\(Arg _ t ident) i -> (ident, (Param i, typeToBase t)))
                        args
                        [2 ..]
          let args'' = M.insert (Ident "self") (Param 1, Cls cls_ident) args'
          instr_meth <- snd <$> local
                    (\env -> env { variableMem = M.union (vattr vms) args'', inClassMethod = Just cls_ident })
                    (transStmt (BStmt pos block))
          stack_size <- gets variables
          return
                $ instrSS [
                        Lab $ FuncLabel $ methodLabel cls_ident method_ident,
                        FunProlog stack_size
                      ]
                . instr_meth
                . instrS FunEpilog

transTopDef :: TopDef -> CM InstrS
transTopDef (FnDef _ fun_type ident args block) = do
  modify (\st -> st { variables = 0 })
  let args' = M.fromList $ zipWith
          (\(Arg _ dtype argident) it -> (argident, (Param it, typeToBase dtype)))
          args
          [1..]
  instr <- snd <$> local (\env -> env {variableMem = args' }) (transStmt (BStmt noPosition block))
  state <- get
  return $
    instrSS [
      Lab (FuncLabel (extractIdentStr ident)),
      FunProlog (variables state) ] .
    instr .
    instrS FunEpilog 

transTopDef (ClDef _ ident extends class_members) = do
  instr_members <- mapM (transMethods ident) class_members
  return $ foldr (.) id instr_members

saveClsMembers :: [TopDef] -> CM ()
saveClsMembers = mapM_ crawl
  where
    crawl :: TopDef -> CM ()
    crawl (FnDef _ ret_type ident _ _) =
      modify (\st -> st {funTypes = M.insert ident (typeToBase ret_type) (funTypes st)})
    crawl (ClDef _ ident extends members) = do
      classes <- gets classDefs
      let (attrs, methods) = foldl saveClsMember ([], []) members
      let cdef = ClassDef {
              extends = maybeIdent extends,
              meths = M.fromList methods,
              attrs = M.fromList attrs
            }
      modify (\st -> st {classDefs = M.insert ident cdef classes })
      where
        saveClsMember :: ([(Ident, BaseType)], [(Ident, BaseType)]) -> ClMember ->  ([(Ident, BaseType)], [(Ident, BaseType)])
        saveClsMember (attrs, meths) member = case member of
          Attr _ attr_type ident -> ((ident, typeToBase attr_type) : attrs, meths)
          Meth _ meth_type ident args _ ->
                (attrs, (ident, Fun (typeToBase meth_type) (map (\(Arg _ arg_type _) -> typeToBase arg_type) args)) : meths)

createVMS :: CM InstrS
createVMS = do
    cDefs <- gets classDefs
    mapM_ (createVM . fst) $ M.toList cDefs
    vmts <- gets vms
    let clsVirtMethods = map (\(v, vmt) -> (v, map vmtToLabel (vmeth vmt)))
            $ M.toList vmts
    let notStructs = filter (\(_, meths) -> meths /= []) clsVirtMethods
    let instrs     = map (uncurry vmtInstr) notStructs
    return $ foldr (.) id instrs
  where
    vmtInstr cls meths =
        instrSS [Lab $ FuncLabel (vmtLabel cls), VMTable meths]
    vmtToLabel (meth, (_, _, methOwner)) = methodLabel methOwner meth

getParentMembers :: Maybe Ident -> CM [([(Ident, BaseType)], [(Ident, (BaseType, Ident))])]
getParentMembers Nothing    = return [([], [])]
getParentMembers (Just cls) = do
    cDefs <- gets classDefs
    case M.lookup cls cDefs of
        Nothing   -> throwImpossible "Impossible, parent must exist"
        Just cDef -> do
            asms <- getParentMembers $ extends cDef
            return
                $ ( M.toList $ attrs cDef
                  , map (\(v, t) -> (v, (t, cls))) (M.toList $ meths cDef)
                  )
                : asms

createVM :: Ident -> CM ()
createVM cls = do
    asms <- getParentMembers (Just cls)
    let (as, ms) = unzip asms
    let as' = zipWith (\(k, t) i -> (k, (Attribute i, t)))
                      (concat $ reverse as)
                      [1 ..]
    let ms'       = concat $ reverse ms
    let orderedMs = map fst $ nubBy (\(m1, _) (m2, _) -> m1 == m2) ms'
    let goodClsMs = M.fromList ms'
    let goodMs = zipWith (\(k, (t, v)) i -> (k, (t, i, v)))
                        (map (`lookup'` goodClsMs) orderedMs)
                        [0 ..]
    let vmt = VMS { vattr = M.fromList as', vmeth = goodMs }

    modify (\st -> st { vms = M.insert cls vmt (vms st) })
  where
    lookup' :: Ident -> M.Map Ident (BaseType, Ident) -> (Ident, (BaseType, Ident))
    lookup' k m = case M.lookup k m of
        Nothing     -> error "createVM not found"
        Just (t, v) -> (k, (t, v))


compile :: Program -> CM InstrS
compile (Program _ top_defs) = do
  saveClsMembers top_defs
  instr_vms <- createVMS

  instr <- foldM fun id top_defs
  strs <- gets strings
  let strLabels = map Lab (M.elems strs)
  return $
    instrSS [
      Intro,
      DataSection] .
    instrSS strLabels .
    instr_vms .
    instrS TextSection .
    instr
  where
    fun :: InstrS -> TopDef -> CM InstrS
    fun instrPrev top_def = do
      instrNew <- transTopDef top_def
      return (instrPrev . instrNew)

runCompilator :: Program -> ExceptT String IO InstrS
runCompilator program@(Program _ topdefs) = evalStateT
  (runReaderT (compile program) (CompilerEnv M.empty Nothing))
  (CompilerState 0 0 M.empty predefinedFunctions M.empty M.empty)
  where
    predefinedFunctions :: Map Ident BaseType
    predefinedFunctions = M.fromList $ map (\(FnDef _ dtype ident _ _) -> (ident, typeToBase dtype)) (filter TM.isFnDef (builtInFunctions ++ topdefs))

