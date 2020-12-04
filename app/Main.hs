{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Curve25519 (testInverseMul, unpack25519)
import Data.ByteString.Base16


main :: IO ()
main = print . ("0x" <>) . encode =<< testInverseMul (unpack25519 "0123456789abcdef0123456789abcdef")
