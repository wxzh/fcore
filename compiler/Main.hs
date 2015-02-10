{-# LANGUAGE DeriveDataTypeable
           , FlexibleContexts
           , TemplateHaskell
           , FlexibleInstances
           , MultiParamTypeClasses
           , OverlappingInstances
           , RankNTypes
           , TypeOperators
           , RecordWildCards
           #-}

module Main (main, TransMethod) where

-- import           Assertions () -- Import this just to run static assertions at compile time.

import           JavaUtils
import           MonadLib
import           Translations
import           Link

import qualified Data.ByteString as B
import           Data.FileEmbed (embedFile)
import           Data.List (sort, group)
import           System.Console.CmdArgs -- Neil Mitchell's CmdArgs library
import           System.Directory (getTemporaryDirectory)
import           System.Environment (getArgs, withArgs)
import           System.FilePath (takeBaseName, (</>))
import           System.IO

type CompileOpt = (Int, Compilation)

data Options = Options
    { optCompile       :: Bool
    , optCompileAndRun :: Bool
    , optSourceFiles   :: [String]
    , optModules       :: [String]
    , optDump          :: DumpOption
    , optTransMethod   :: [TransMethod]
    , optVerbose       :: Bool
    } deriving (Eq, Show, Data, Typeable)

data TransMethod = Apply
                 | Naive
                 | Stack
                 | Unbox
                 | StackAU1
                 | StackAU2
                 | BenchN
                 | BenchS
                 | BenchNA
                 | BenchSA
                 | BenchSAI1
                 | BenchSAI2
                 deriving (Eq, Show, Data, Typeable, Ord)

runtimeBytes :: B.ByteString
runtimeBytes = $(embedFile "runtime/runtime.jar")

writeRuntimeToTemp :: IO ()
writeRuntimeToTemp =
  do tempdir <- getTemporaryDirectory
     let tempFile = tempdir </> "runtime.jar"
     B.writeFile tempFile runtimeBytes

optionsSpec :: Options
optionsSpec =
  Options {optCompile =
             False &= explicit &=
             name "c" &=
             name "compile" &=
             help "Compile Java source"
          ,optCompileAndRun =
             False &= explicit &=
             name "r" &=
             name "run" &=
             help "Compile & run Java source"
          ,optDump =
             NoDump &= explicit &=
             name "d" &=
             name "dump" &=
             typ "TYPE" &=
             help ("Dump intermediate representations; " ++
                   "options: `core`, `simplecore`, `closuref`")
          ,optSourceFiles =
             [] &= args &=
             typ "SOURCE FILES"
          ,optModules =
             [] &= explicit &=
             name "l" &=
             name "module" &=
             typ "MODULE" &=
             help "Link modules to the source file"
          ,optTransMethod =
             [] &= explicit &=
             name "m" &=
             name "method" &=
             typ "METHOD" &=
             help ("Translations method." ++ "Can be either 'naive', 'apply', 'stack', and/or 'unbox'" ++
                                             "(use without quotes)." ++
                                             "The default is 'naive'.")
          ,optVerbose =
             False &= explicit &=
             name "v" &=
             name "verbose" &=
             help "Verbose"} &=
  helpArg [explicit,name "help",name "h"] &=
  program "f2j" &=
  summary "SystemF to Java compiler"

getOpts :: IO Options
getOpts = cmdArgs optionsSpec -- cmdArgs :: Data a => a -> IO a

main :: IO ()
main = do
  rawArgs <- getArgs
  -- If the user did not specify any arguments, pretend as "--help" was given
  Options{..} <- (if null rawArgs then withArgs ["--help"] else id) getOpts

  -- Write the bytes of runtime.jar to temp directory
  writeRuntimeToTemp
  forM_ optSourceFiles (\source_path ->
    do let source_path_new = if null optModules then source_path else takeBaseName source_path ++ "c.sf"
       let output_path      = inferOutputPath source_path_new
           translate_method = optTransMethod
           modList          = optModules
           sort_and_rmdups  = map head . group . sort . (++) [Naive]
       (num, opt) <- getOpt (sort_and_rmdups translate_method)
       unless (null optModules) $
         do content <- Link.linkModule modList
            putStrLn "Linking..."
            Link.link source_path content
            putStrLn (source_path_new ++ " generated!")
       putStrLn (takeBaseName source_path_new ++ " using " ++ show (sort_and_rmdups translate_method))
       putStrLn ("Compiling to Java source code ( " ++ output_path ++ " )")
       compilesf2java num optDump opt source_path_new output_path
       when (optCompile || optCompileAndRun) $
         do when optVerbose (putStrLn "  Compiling to Java bytecode")
            compileJava output_path
       when optCompileAndRun $
         do when optVerbose $ do { putStr "  Running Java\n  Output: "; hFlush stdout }
            runJava output_path)

getOpt :: [TransMethod] -> IO CompileOpt
getOpt translate_method = case translate_method of
  [Apply, Naive]               -> return (0, compileAO)
  -- [Apply, Naive, Unbox]        -> return (0, compileAoptUnbox)
  [Apply, Naive, Stack]        -> return (0, compileS)
  -- [Apply, Naive, Stack, Unbox] -> return (0, compileSAU)
  -- [Naive, StackAU1]            -> return (1, compileSAU)
  -- [Naive, StackAU2]            -> return (2, compileSAU)
  [Naive, Stack]               -> return (0, compileSN)
  -- [Naive, Stack, Unbox]        -> return (0, compileSU)
  -- [Naive, Unbox]               -> return (0, compileUnbox)
  -- [BenchS]                     -> return (0, compileBS False)
  -- [BenchNA]                    -> return (0, compileBN True)
  -- [BenchSA]                    -> return (0, compileBS True)
  -- [BenchSAI1]                  -> return (1, compileBS True)
  -- [BenchSAI2]                  -> return (2, compileBS True)
  _                            -> return (0, compileN) -- Naive is the default
