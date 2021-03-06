{-# LANGUAGE TemplateHaskell #-}

{- |
Module      :  FileLoad
Description :  Testing framework for make test 2
Copyright   :  (c) 2014—2015 The F2J Project Developers (given in AUTHORS.txt)
License     :  BSD3

Maintainer  :  Boya Peng <u3502350@connect.hku.hk>
Stability   :  experimental
Portability :  portable

-}

module Main where

import RuntimeProcessManager

import System.IO
import System.Directory     (doesFileExist, getDirectoryContents)
import System.FilePath      (takeFileName, takeExtensions)
import System.Exit

import System.Clock

import BackEnd
import FileIO
import qualified Data.ByteString as B
import Data.FileEmbed       (embedFile)
import System.Directory     (getTemporaryDirectory)
import System.FilePath      ((</>))

runtimeBytes :: B.ByteString
runtimeBytes = $(embedFile "runtime/runtime.jar")

writeRuntimeToTemp :: IO ()
writeRuntimeToTemp =
  do tempdir <- getTemporaryDirectory
     let tempFile = tempdir </> "runtime.jar"
     B.writeFile tempFile runtimeBytes

testCasesPath :: String
testCasesPath = "testsuite/tests/shouldRun/"

initReplEnv :: [TransMethod] -> Compilation -> [String] -> IO Int
initReplEnv method opt xs = withRuntimeProcess "FileServer" NoBuffering ((\(inP,outP) -> loadFile inP outP method opt xs))

loadFile :: Handle -> Handle -> [TransMethod] -> Compilation -> [String] -> IO Int
loadFile inP outP method opt xs = do
    putStrLn "-------------------------------------"
    putStrLn ("Compilation Option: " ++ show (method))
    loadAll inP outP 0 method opt xs

loadAll ::  Handle -> Handle -> Int -> [TransMethod] -> Compilation -> [String] -> IO Int
loadAll _ _ err _ _ [] = return err
loadAll inP outP err method opt (x:xs) = do
    let compileOpt = (0, opt, method)
    let name = takeFileName x
    if ((head name /= '.') && (takeExtensions x == ".sf"))
      then do putStrLn ("Running " ++ name)
              output <- getStandardOutput x
              putStrLn $ "\x1b[32m" ++ "Standard output: " ++ output
              error2 <- wrap (inP, outP) (receiveMsg2 output) compileOpt True False x
              loadAll inP outP (err+error2) method opt xs
      else loadAll inP outP err method opt xs

getStandardOutput :: FilePath -> IO String
getStandardOutput file = do
  content <- readFile file
  let func = unwords . tail . words
  return $ func ((lines content) !! 0)

fileExist :: String -> IO ()
fileExist name = do
        exist <- doesFileExist name
        if (exist)
          then return ()
          else fileExist name

addFilePath :: [FilePath] -> [FilePath]
addFilePath [] = []
addFilePath (x:xs) = (testCasesPath ++ x) : (addFilePath xs)

main :: IO ()
main = do
  writeRuntimeToTemp
  start <- getTime Monotonic
  xs <- getDirectoryContents testCasesPath
  let (_:_:ys) = xs
  let zs = addFilePath ys
  putStrLn ""
  putStrLn $ "Running test from " ++ testCasesPath
  putStrLn "-------------------------------------"
  error5 <- initReplEnv [SNaive] compileN zs
  error1 <- initReplEnv [Naive] compileN zs
  error2 <- initReplEnv [Naive, Apply] compileAO zs
  error3 <- initReplEnv [Naive, Stack] compileSN zs
  error4 <- initReplEnv [Naive, Apply, Stack] compileS zs
  putStrLn "-------------------------------------"
  putStrLn "Finished!"
  end <- getTime Monotonic
  putStrLn $ "Running Time " ++ show (sec end - sec start) ++ "s"
  if (error1 /= 0) || (error2 /= 0) || (error3 /= 0) || (error4 /= 0) || (error5 /= 0)
    then exitFailure
    else return ()
