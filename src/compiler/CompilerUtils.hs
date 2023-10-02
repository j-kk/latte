{-# LANGUAGE LambdaCase #-}
module CompilerUtils where
import Prelude as C
import Data.Map (Map)
import TypeMatchUtils as TM
    ( argNP, blockNP, fnDefNP, intNP, strNP, voidNP, BaseType, boolNP, extractIdentStr )
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (StateT, gets, modify)
import Control.Monad.Except (ExceptT, MonadError (throwError))
import AbsLatte (Ident (Ident), RelOp, RelOp' (LTH, LE, GTH, GE, EQU, NE), TopDef)
import Data.List (intercalate)

litTrue, litFalse, litNull :: Operand
litTrue = LitNumber 1
litFalse = LitNumber 0
litNull = LitNumber 0

byte, word, dword, qword :: Integer
byte = 1
word = 2
dword = 4
qword = 8

throwImpossible :: String -> CM a
throwImpossible s =
    throwError $ showString "Impossible after code analysis: " s

data Label = 
    FuncLabel String | 
    JumpLabel Integer | 
    StringLabel Integer String

instance Show Label where
    show = \case
      FuncLabel s -> s ++ ":"
      JumpLabel n -> ".L" ++ show n ++ ":"
      StringLabel n s -> ".LC" ++ show n ++ ":\n\t.string " ++ show s

data Register = EAX | EBX | ECX | EDX | ESI | EDI | ESP | EBP
instance Show Register where
    show = \case
      EAX -> "eax"
      EBX -> "ebp"
      ECX -> "ecx"
      EDX -> "edx"
      ESI -> "esi"
      EDI -> "edi"
      ESP -> "esp"
      EBP -> "ebp"

data Memory = Local Integer | Param Integer | Attribute Integer
instance Show Memory where
    show (Param     n) = "[" ++ show EBP ++ " + 4 * " ++ show (n + 1) ++ "]"
    show (Local     n) = "[" ++ show EBP ++ " - 4 * " ++ show n ++ "]"
    show (Attribute n) = "[" ++ show EAX ++ " + 4 * " ++ show n ++ "]"

data CompilerEnv = CompilerEnv {
    variableMem :: Map Ident (Memory, BaseType) ,
    inClassMethod :: Maybe Ident
}

data CompilerState = CompilerState {
    freeLabel :: Integer,
    variables :: Integer,
    strings :: Map String Label,
    funTypes :: Map Ident BaseType,
    classDefs :: Map Ident ClassDef,
    vms :: Map Ident VMS
}

type CM = ReaderT CompilerEnv (StateT CompilerState (ExceptT String IO))

data ClassDef = ClassDef {
    attrs :: Map Ident BaseType,
    meths :: Map Ident BaseType,
    extends :: Maybe Ident
}

data VMS = VMS {
    vmeth :: [ (Ident, (BaseType, Integer, Ident)) ],
    vattr :: Map Ident (Memory, BaseType)
} deriving Show

data Operand = Reg Register
    | AttrAddr Integer Register
    | ArrElem Register Register Integer
    | Addr Integer Register
    | MethAddr Integer Register
    | Mem Memory
    | LitNumber Integer
    | LitString Integer
    | VTMLit String
    
instance Show Operand where
    show = \case
      Reg reg -> show reg
      AttrAddr 0 reg -> "[" ++ show reg ++ "]"
      AttrAddr n reg -> "[" ++ show reg ++ " + 4 * " ++ show n ++ "]"
      ArrElem base move size ->  "[" ++ show base ++ " + " ++ show size ++ " * " ++ show move ++ "]"
      Addr 0 reg -> "DWORD PTR [" ++ show reg ++ "]"
      Addr n reg -> "DWORD PTR [" ++ show reg ++ " - 4 * " ++ show n ++ "]"
      MethAddr 0 reg -> "[" ++ show reg ++ "]"
      MethAddr n reg -> "[" ++ show reg ++ " + 4 * " ++ show n ++ "]"
      Mem mem -> show mem
      LitNumber n -> show n
      LitString n -> ".LC" ++ show n
      VTMLit l -> l 

vmtLabel :: Ident -> String
vmtLabel cls = methodLabel cls (Ident "VMT")

methodLabel :: Ident -> Ident -> String
methodLabel cls method = extractIdentStr cls ++ "." ++ extractIdentStr method

isMemory :: Operand -> Bool
isMemory (Mem _) = True
isMemory _ = False

isLit :: Operand -> Bool
isLit (LitNumber _) = True
isLit _ = False

matchJumpOp :: RelOp -> JumpOp
matchJumpOp = \case
  LTH _ -> JL
  LE _ -> JLE
  GTH _ -> JG
  GE _ -> JGE
  EQU _ -> JE
  NE _ -> JNE

data JumpOp = JL | JLE | JG | JGE | JE | JNE | JMP
instance Show JumpOp where
    show JL  = "jl"
    show JLE = "jle"
    show JG  = "jg"
    show JGE = "jge"
    show JE  = "je"
    show JNE = "jne"
    show JMP = "jmp"

data BinOp = ADD | SUB | MUL | DIV | XOR | CMP
instance Show BinOp where
    show ADD = "add"
    show SUB = "sub"
    show DIV = "idiv"
    show MUL = "imul"
    show XOR = "xor"
    show CMP = "cmp"

data SingleOp = NEG | INC | DEC
instance Show SingleOp where
    show NEG = "neg"
    show INC = "inc"
    show DEC = "dec"

data ZeroOp = RET | CDQ | LEAVE
instance Show ZeroOp where
    show RET = "ret\n"
    show CDQ = "cdq"
    show LEAVE = "leave"

data Instr =
    Intro
    | DataSection
    | TextSection
    | FunProlog Integer
    | FunEpilog
    | CALL String
    | CALLM Operand
    | MOV Operand Operand
    | LEA Operand Operand
    | PUSH Operand
    | POP Operand
    | JUMP JumpOp Integer
    | ZeroInstr ZeroOp
    | SingleInstr SingleOp Operand
    | BinInstr BinOp Operand Operand
    | Lab Label
    | VMTable [String]

instance Show Instr where
  show = \case
    Intro -> ".global main\n.intel_syntax noprefix"
    DataSection -> ".data"
    TextSection -> ".text"
    FunProlog 0 ->
        show (PUSH (Reg EBP)) ++
        "\n\t" ++
        show (MOV (Reg EBP) (Reg ESP)) -- sub space for locals
    FunProlog n ->
        show (PUSH (Reg EBP)) ++
        "\n\t" ++
        show (MOV (Reg EBP) (Reg ESP)) ++ -- sub space for locals
        "\n\t" ++
        show (BinInstr SUB (Reg ESP) (LitNumber (dword * n)))
    FunEpilog ->
        show LEAVE ++
        "\n\t" ++
        show RET
    CALL label -> "call " ++ label
    CALLM label -> "call " ++ show label
    MOV dst src -> "mov " ++ show dst ++ ", " ++ inword_lit dst src ++ show src
    LEA dst src -> "lea " ++ show dst ++ ", " ++ show src
    PUSH op -> "push " ++ show op
    POP op -> "pop " ++ show op
    JUMP jo jmp_label -> show jo ++ " .L" ++ show jmp_label
    ZeroInstr zo -> show zo
    SingleInstr so op -> show so ++ " " ++ inword op ++ show op
    BinInstr bin_op op1 op2 -> show bin_op ++ " " ++ show op1 ++ ", " ++ show op2
    Lab l -> show l
    VMTable ms -> ".int " ++ intercalate ", " ms

    where 
        inword op = if isMemory op then "DWORD PTR " else ""
        inword_lit op lit = if isMemory op && isLit lit then "DWORD PTR " else ""


indent :: Instr -> String
indent Intro       = ""
indent DataSection = ""
indent TextSection = ""
indent (Lab     _) = ""
indent (VMTable _) = ""
indent _           = "\t"

type InstrS = [Instr] -> [Instr]
instrS :: Instr -> InstrS
instrS = (:)
instrSS :: [Instr] -> InstrS
instrSS = (++)

getNewLabel :: CM Integer
getNewLabel = do
    label <- gets freeLabel
    modify (\st -> st { freeLabel = label + 1}) -- id?
    return label

builtInFunctions :: [TopDef]
builtInFunctions = [
    TM.fnDefNP TM.voidNP (Ident "printInt") [TM.argNP TM.intNP (Ident "x")] (TM.blockNP []),
    TM.fnDefNP TM.voidNP (Ident "printString") [TM.argNP TM.strNP (Ident "x")] (TM.blockNP []),
    TM.fnDefNP TM.voidNP (Ident "error") [] (TM.blockNP []),
    TM.fnDefNP TM.intNP (Ident "readInt") [] (TM.blockNP []),
    TM.fnDefNP TM.strNP (Ident "readString") [] (TM.blockNP []),
    TM.fnDefNP TM.strNP (Ident "____concatStr") [TM.argNP TM.strNP (Ident "x"), TM.argNP TM.strNP (Ident "y")] (TM.blockNP []),
    TM.fnDefNP TM.boolNP (Ident "____compareStr") [TM.argNP TM.strNP (Ident "x"), TM.argNP TM.strNP (Ident "y")] (TM.blockNP [])
    ]

methodIdent :: Ident -> Ident -> Ident 
methodIdent (Ident cls_ident) (Ident meth_ident) = Ident (cls_ident ++ "." ++ meth_ident) 