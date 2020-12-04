{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Curve25519
import Data.ByteString (ByteString)
import Data.ByteString.Base16 (decode, encode)


main :: IO ()
main = do
  -- test
  test2


test :: IO ()
test = do
  (pubA,secA) <- generate_keypair
  (pubB,secB) <- generate_keypair

  aToB <- x25519 pubB secA
  bToA <- x25519 pubA secB

  print $ encode aToB
  print $ encode bToA

test2 :: IO ()
test2 = do


  aToB <- x25519 pub_B sec_A
  bToA <- x25519 pub_A sec_B

  print $ encode aToB
  print $ encode bToA
  print $ encode x_S

  pubA <- pubkey sec_A
  pubB <- pubkey sec_B

  aToB' <- x25519 pubB sec_A
  bToA' <- x25519 pubA sec_B

  print $ encode aToB'
  print $ encode bToA'
  print $ encode x_S

  pure ()


sec_A, sec_B, pub_A, pub_B, x_S :: ByteString
Right sec_A = decode "5ac99f33632e5a768de7e81bf854c27c46e3fbf2abbacd29ec4aff517369c660"
Right sec_B = decode "47dc3d214174820e1154b49bc6cdb2abd45ee95817055d255aa35831b70d3260"
Right pub_A = decode "057e23ea9f1cbe8a27168f6e696a791de61dd3af7acd4eeacc6e7ba514fda863"
Right pub_B = decode "6eb89da91989ae37c7eac7618d9e5c4951dba1d73c285ae1cd26a855020eef04"
Right x_S   = decode "61450cd98e36016b58776a897a9f0aef738b99f09468b8d6b8511184d53494ab"