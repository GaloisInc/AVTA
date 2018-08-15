{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Main (main) where

import           Control.Lens
import           Control.Monad
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import           Data.ElfEdit
import           Data.Macaw.Discovery
import           Data.Macaw.Memory.ElfLoader
import           Data.Macaw.X86
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Some
import qualified Data.Vector as V
import           System.Environment
import           System.Exit
import           System.IO
import           Data.Macaw.CFG.Core 
--import           Data.Macaw.SCFG


warning :: String -> IO ()
warning msg = do
  hPutStrLn stderr msg

fatalError :: String -> IO a
fatalError msg = do
  hPutStrLn stderr msg
  exitFailure

-- | Get the path of the program to analyze.
parseProgPath :: IO FilePath
parseProgPath = do
  args <- getArgs
  case args of
    [] -> fatalError "Please specify path of program to analyze."
    [nm] -> pure nm
    _ -> fatalError "Please specify *only* path of program to analyze."


-- | Read an elf from a binary
readElf :: FilePath -> IO (Elf 64)
readElf path = do
  contents <- BS.readFile path
  case parseElf contents of
    ElfHeaderError _ msg ->
      fatalError msg
    Elf32Res{} -> do
      fatalError "Expected 64-bit elf file."
    Elf64Res errs e -> do
      mapM_ (warning . show) errs
      unless (elfMachine e == EM_X86_64) $ do
        fatalError "Expected a x86-64 binary"
      unless (elfOSABI e `elem` [ELFOSABI_LINUX, ELFOSABI_SYSV]) $ do
        warning "Expected Linux binary"
      pure e


show_rhs (EvalApp app) = "EvalApp"
show_rhs (SetUndefined tr) = "SetUndefined"
show_rhs (ReadMem f mrep) =  "ReadMem"
show_rhs (CondReadMem mrep fb f fty) =  "CondReadMem"
show_rhs (EvalArchFn af trep) =  "EvalArchFn"


show_asgn asgn = show_rhs (assignRhs asgn)

visitTerminals :: StatementList X86_64 ids -> DiscoveryState X86_64 -> IO ()
visitTerminals sl discInfo = do
  case stmtsTerm sl of
    ParsedCall _ Nothing -> do
      putStrLn $ "Tail call"
      
    ParsedCall s ret -> do
      case s^.curIP of
          BVValue _ a ->
             putStrLn $ "Current IP " ++ show a
          RelocatableValue repr addr -> do
            let mem = memory discInfo
            let name_map = symbolNames discInfo
            case (asSegmentOff mem addr) of
                Just seg -> putStrLn $ "Found a call to : (relocatablevalue) " ++ show (Map.lookup seg name_map) ++ " at addr " ++ (show seg)
                Nothing -> putStrLn $ "Found a call to : (relocatablevalue) with undef addr"
          SymbolValue _ _ ->
             putStrLn $ "Found a call to: (symbolvalue) "
          AssignedValue asgn  ->
             putStrLn $ "Found a call to: (assignedvalue) " ++ (show_asgn asgn)
          _ ->
             putStrLn $ "Current IP unknown"

    ParsedCall _ (Just retAddr) -> do
      putStrLn $ "Call returns to " ++ show retAddr
    ParsedJump _ addr -> do
      putStrLn $ "Jump to " ++ show addr
    ParsedLookupTable _ _ addrs -> do
      putStrLn $ "Table to " ++ show (V.toList addrs)
    ParsedReturn{} -> do
      putStrLn $ "Return"
    ParsedIte _ x y -> do
      putStrLn $ "Ite"
      visitTerminals x discInfo
      visitTerminals y discInfo
    ParsedArchTermStmt{} -> do
      putStrLn $ "ArchTermStmt"
    ParsedTranslateError{} -> do
      putStrLn $ "Translate error"
    ClassifyFailure{} -> do
      putStrLn $ "Classify failure"

main :: IO ()
main = do
  args <- getArgs
  putStrLn $ show args

  progPath <- parseProgPath
  e <- readElf progPath

  -- Construct memory representation of Elf file.
  let loadOpts = defaultLoadOptions

  (warnings, mem, entry, symbols) <- either fail pure $
    resolveElfContents loadOpts e
  forM_ warnings $ \w -> do
    hPutStrLn stderr w

  let archInfo = x86_64_linux_info

  -- Default docvery options
  let disOpt = defaultDiscoveryOptions

  -- Create map from symbol addresses to name.
  let addrSymMap = Map.fromList [ (memSymbolStart msym, memSymbolName msym) | msym <- symbols ]
  -- Initial entry point is just entry
  let initEntries = maybeToList entry
  -- Explore all functions
  let fnPred = \_ -> True
  discInfo <- completeDiscoveryState archInfo disOpt mem initEntries addrSymMap fnPred

  -- Walk through functions
  forM_ (exploredFunctions discInfo) $ \(Some f) -> do
    -- Walk through basic blocks within function
    putStrLn $ ""
    putStrLn $ "Function " ++ BSC.unpack (discoveredFunName f)
    forM_ (f^.parsedBlocks) $ \b -> do
      putStrLn $ "Block start: " ++ show (pblockAddr b)
      -- Print out information from list
      visitTerminals (blockStatementList b) discInfo
