{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
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
import           Data.Parameterized.NatRepr
import qualified Data.Parameterized.Map as PMap
import qualified Data.Vector as V
import           System.Environment
import           System.Exit
import           System.IO
import           Data.Macaw.Types
import           Data.Macaw.CFG.Core
import           Data.Macaw.CFG.App
import qualified Data.Macaw.AbsDomain.AbsState as AS
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

showApp ::  StatementList X86_64 ids -> App (Value X86_64 ids) (BVType 64) -> DiscoveryState X86_64 -> String
showApp sl val discInfo =
  case val of
    Mux _ c x y ->  "mux" 
    Trunc x w ->  "trunc" 
    TupleField _ x i ->  "tuple_field" 
    SExt x w ->  "sext" 
    UExt x w ->  "uext"  
    BVAdd _ x y   ->  "bv_add "   ++ showBVValue sl x discInfo ++ " and " ++ showBVValue sl y discInfo
    BVAdc _ x y c ->  "bv_adc" 
    BVSub _ x y ->  "bv_sub"
    BVSbb _ x y b ->  "bv_sbb" 
    BVMul _ x y ->  "bv_mul" 
    BVComplement _ x ->  "bv_complement" 
    BVAnd _ x y ->  "bv_and " ++ showBVValue sl x discInfo ++ " and " ++ showBVValue sl y discInfo
    BVOr  _ x y ->  "bv_or"  
    BVXor _ x y ->  "bv_xor" 
    BVShl _ x y ->  "bv_shl" 
    BVShr _ x y ->  "bv_shr" 
    BVSar _ x y ->  "bv_sar" 
    PopCount _ x ->  "popcount" 
    ReverseBytes _ x ->  "reverse_bytes" 
    Bsf _ x ->  "bsf"
    Bsr _ x ->  "bsr"

showBVValue ::  StatementList X86_64 ids -> Value X86_64 ids (BVType 64) -> DiscoveryState X86_64 -> String
showBVValue sl val discInfo = 
  case val of
          BVValue n a ->
            let mem = memory discInfo in
            let name_map = symbolNames discInfo in
--            let glo_map = _globalDataMap discInfo in
--            let Just addr = (valueAsMemAddr val) in 
--            show (Map.lookup addr glo_map)
--                  Just seg -> show (Map.lookup seg name_map) ++ " at addr " ++ (show seg)
--                  Nothing -> "(bvvalue) undef addr")
             "(BVValue): "++ show (valueAsMemAddr val) -- absoluteAddr (fromInteger a))
          RelocatableValue repr addr -> 
            let mem = memory discInfo in
            let name_map = symbolNames discInfo in
            (case (asSegmentOff mem addr) of
                Just seg -> "(relocatablevalue) " ++ show (Map.lookup seg name_map) ++ " at addr " ++ (show seg)
                Nothing ->  "(relocatablevalue) with undef addr")
          SymbolValue _ _ ->
             "(symbolvalue) "
          AssignedValue asgn  ->
             let absState = stmtsAbsState sl in
             let mAss = view AS.absAssignments absState in
             "(assignedvalue) with AbsValue: " ++
             (show $ PMap.lookup (assignId asgn) mAss)
{-             ++
            (case (assignRhs asgn) of
               EvalApp app -> "EvalApp "++ (showApp sl app discInfo)
               SetUndefined tr -> "SetUndefined"
               ReadMem f mrep -> "ReadMem " ++ (showBVValue sl f discInfo)
               CondReadMem mrep fb f fty -> "CondReadMem"
               EvalArchFn af trep -> "EvalArchFn"
            ) -}
          Initial reg ->
            "Held in register: " ++ (show reg)
          
          _ -> 
             "Unknown BVValue"

visitTerminals :: StatementList X86_64 ids -> DiscoveryState X86_64 -> IO ()
visitTerminals sl discInfo = do
  case stmtsTerm sl of
    ParsedCall _ Nothing -> do
      putStrLn $ "Tail call"
      
    ParsedCall s ret ->
      putStrLn $ "Found a call to: "++(showBVValue sl (s^.curIP) discInfo)
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
