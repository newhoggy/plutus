{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumericUnderscores    #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Control.Concurrent.STM.ExtraSpec
    ( tests
    ) where

import           Control.Concurrent           (threadDelay)
import           Control.Concurrent.Async     (concurrently)
import           Control.Concurrent.STM       (atomically)
import           Control.Concurrent.STM.Extra
import           Control.Concurrent.STM.TVar  (newTVar, readTVar, writeTVar)
import           Control.Monad                (forM_, void)
import           Control.Monad.IO.Class       (liftIO)
import           Data.Foldable                (fold)
import           Data.Maybe                   (isNothing)
import           GHC.Conc.Sync                (STM)
import           Test.Tasty                   (TestTree, testGroup)
import           Test.Tasty.HUnit             (HasCallStack, assertBool, assertEqual, testCase)

tests :: TestTree
tests =
    testGroup
        "Control.Concurrent.STM.ExtraSpec"
        [ testCase "Can read one and only one" $ do
          let x :: STMStream Integer
              x = pure 5
          next <- readOne x
          assertEqual "Couldn't read one!" 5 (fst next)

          let next' = readOne <$> snd next
          assertBool "Found more than one!" (isNothing next')

        , testCase "Can read many" $ do
          let ns = [1..10]
              x :: STMStream Integer
              x = foldMap pure ns
          items <- readN 10 x
          assertEqual "Couldn't read what we wrote!" ns items

        , testCase "Unfold doesn't yield consecutive duplicates" $ do

            var <- liftIO $ atomically $ newTVar (1 :: Integer)

            -- Two threads:
            -- 1. Constantly write duplicate values
            let t1 = forM_ [1,1,1,3] $ \a -> do
                  atomically $ writeTVar var a
                  threadDelay 1_000
            --
            -- 2. Constantly read; hopefully no dupes.
                t2 = do
                  let s = unfold $ readTVar var
                  as <- readN 2 s
                  assertEqual "Stream didn't remove consecutive duplicates" [1,3] as

            void $ liftIO $ concurrently t1 t2
        ]
