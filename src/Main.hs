{-# LANGUAGE OverloadedStrings #-}
module Main where

import AbsLatte ( Program )
import Control.Monad.Except (ExceptT, runExceptT, MonadError (throwError), when)
import ParLatte (pProgram, myLexer)
import LexLatte (mkPosToken)
import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr, hPutStr)
import System.FilePath (replaceExtension, dropFileName, combine)
import System.Environment (getArgs, getExecutablePath)
import Data.List (delete)
import Analyser (analyse)
import Control.Exception (catch, IOException)
import Text.Read (Lexeme(String))
import Compiler ( runCompilator )
import CompilerUtils (indent)
import PrintLatte
import Shelly


usage :: IO ()
usage = do
  putStrLn $ unlines [
        "Compiler for Latte language to x86.",
        "Usage:  Call with one of the following argument combinations:"
        , "  --help          Display this help message."
        , "  file            Compile content of the file."
        , " -c               Run only static analysis."
        , " -a               Generate only ASM code."
        ]
  exitFailure

errorMsg :: String
errorMsg = foldl foldFun (showString "") msg ""
  where
    foldFun :: ShowS -> String -> ShowS
    foldFun = \acc line -> acc . showString line . showString "\n"
    msg :: [String]
    msg = [
        "ERROR"
      , "Parse error"
      ]

parse :: String -> IO Program
parse s = do
  case pProgram (myLexer s) of
    Left err -> do
      hPutStr stderr errorMsg
      putStrLn err
      exitFailure
    Right tree -> do
      return tree

compile :: FilePath -> IO ()
compile filepath = do
  s <- readFile filepath
  parsed_program <- parse s
  compilationResult <- runExceptT (runCompilator parsed_program)

  case compilationResult of
    Left e -> do
      hPutStrLn stderr $ "ERROR\n[Compilation error] " ++ e
      exitFailure
    Right instructions -> do
      let compiledFilepath = replaceExtension filepath ".s"
      let compiledProgram = (unlines . map (\x -> indent x ++ show x)) (instructions [])
      writeFile compiledFilepath compiledProgram
      putStrLn (showString "Generated: " compiledFilepath)

genBinCode :: FilePath -> FilePath -> Sh Bool 
genBinCode asm_file self_path = do
  let compiler = "i686-linux-gnu-gcc"
  let lib_path = toTextIgnore $ combine (dropFileName  self_path) "lib/liblatte.o"
  let output_file = replaceExtension asm_file ""
  errExit False (run compiler [lib_path, "-m32", "-o", toTextIgnore output_file, toTextIgnore asm_file])
  exit_code <- lastExitCode
  return $ exit_code == 0

main :: IO ()
main = do
  args <- getArgs
  let noPostCompile = "-c" `elem` args
  let noBinCode = "-a" `elem` args
  let args_no_flags = foldr delete args ["-c", "-a"]
  case args_no_flags of
    ["--help"] -> usage
    [filepath] -> do
      s <- catch (readFile filepath)
        (\e -> do let err = show (e :: IOException)
                  hPutStrLn stderr ("ERROR\nWarning: Couldn't open " ++ filepath ++ ": " ++ err)
                  exitFailure)
      parsed_program <- parse s
      analyse parsed_program
      putStrLn "OK"
      putStrLn "Analysis successful."
      unless noPostCompile $ compile filepath
      self_path <- getExecutablePath 
      unless (noBinCode || noPostCompile) $ bincode_generation filepath self_path
      exitSuccess
    _ -> usage
  where
    bincode_generation filepath self_path= do
      compiler_result <- shelly $ silently $ genBinCode (replaceExtension filepath "s") self_path
      unless compiler_result (hPutStrLn stderr "ASM Compiler error" >> exitFailure)
      putStrLn (showString "Generated: " (replaceExtension filepath ""))
