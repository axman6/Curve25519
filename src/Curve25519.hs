{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}
{- |
Copyright: (c) 2020 Alex Mason
SPDX-License-Identifier: MIT
Maintainer: Alex Mason <github@me.axman6.com>

See README for more infoPure HAskell iomplementation of Curve255 19
-}

module Curve25519 where
    --    ( FieldElem
    --    , FieldElemM
    --    , withFieldElem
    --    , unpack25519
    --    ) where

import Data.Int (Int64)
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Unboxed.Mutable as MV

import Data.Bits

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Unsafe as BSU

import Control.Monad (replicateM_, when, forM_)
import Control.Monad.ST
import Control.Monad.Primitive
import Data.Functor ((<&>))

type I64 = Int64

newtype FieldElem    = FieldElem (V.Vector I64) deriving stock Show
newtype FieldElemM s = FieldElemM (MV.MVector s I64)

withFieldElem :: PrimMonad m => FieldElem -> (FieldElemM (PrimState m) -> m a) -> m FieldElem
withFieldElem (FieldElem inV) f = FieldElem <$> do
    !minV <- V.thaw inV
    !_ <- f (FieldElemM minV)
    V.unsafeFreeze minV

thaw :: PrimMonad m => FieldElem -> m (FieldElemM (PrimState m))
thaw (FieldElem v) = FieldElemM <$> V.thaw v

withFieldElem' :: PrimMonad m => (FieldElemM (PrimState m) -> m a) -> m FieldElem
withFieldElem' f = do
    fe@(FieldElemM v) <- new
    _ <- f fe
    FieldElem <$> V.unsafeFreeze v


new :: PrimMonad m => m (FieldElemM (PrimState m))
new = FieldElemM <$> MV.replicate 16 0

newSized :: PrimMonad m => Int ->  m (FieldElemM (PrimState m))
newSized size = FieldElemM <$> MV.replicate size 0

index :: PrimMonad m =>  FieldElemM (PrimState m) -> Int -> m I64
index (FieldElemM v) !i = MV.read v i

write :: PrimMonad m => FieldElemM (PrimState m) -> Int -> I64 -> m ()
write (FieldElemM v) !i !e = MV.write v i e

modify :: PrimMonad m => FieldElemM (PrimState m) -> Int -> (I64 -> I64) -> m ()
modify (FieldElemM v) !i !f = MV.unsafeModify v f i


for16 :: PrimMonad m => (Int -> m a) -> m ()
for16 f = forM_ [0..15] f

{-
5 static void unpack25519(field_elem out, const u8 *in)
6{
7     int i;
8     for (i = 0; i < 16; ++i) out[i] = in[2*i] + ((i64) in[2*i + 1] << 8);
9     out[15] &= 0x7fff;
10 }
-}
unpack25519 :: ByteString -> Maybe FieldElem
unpack25519 bs
    | BS.length bs /= 32 = Nothing
    | otherwise = Just $! res
    where res = runST $ withFieldElem' $ \fe ->
            for16 $ \i -> do
                let !lo = fromIntegral $ BSU.unsafeIndex bs (i*2)
                    !hi = fromIntegral $ BSU.unsafeIndex bs (i*2 + 1)
                write fe i (lo + (hi `unsafeShiftL` 8))
                modify fe 15 (.&. 0x7fff)


{-
12 static void carry25519(field_elem elem)
13 {
14      int i;
15      i64 carry;
16      for(i=0;i<16;++i){
17          carry = elem[i] >> 16;
18          elem[i] -= carry << 16;
19          if (i < 15) elem[i + 1] += carry; else elem[0] += 38 * carry;
20      }
21 }
-}
carry25519 :: PrimMonad m => FieldElemM (PrimState m) -> m ()
carry25519 fe = do
    for16 $ \i -> do
        !carry <- index fe i <&> (`unsafeShiftR` 16)
        modify fe i $ \e -> e - carry `unsafeShiftL` 16
        if i < 15
        then modify fe (i+1) $ \e -> e + carry
        else modify fe 0     $ \e -> e + 38 * carry

{-
23 static void fadd(field_elem out, const field_elem a, const field_elem b) /* out = a + b */
24 {
25      int i;
26      for (i = 0; i < 16; ++i) out[i] = a[i] + b[i];
27 }
-}
fadd :: PrimMonad m
    => FieldElemM (PrimState m) -- ^ out = a + b
    -> FieldElemM (PrimState m) -- ^ a
    -> FieldElemM (PrimState m) -- ^ b
    -> m ()
fadd out a b = do
    for16 $ \i -> do
        a' <- index a i
        b' <- index b i
        write out i $! a' + b'

{-
29 static void fsub(field_elem out, const field_elem a, const field_elem b) /* out = a - b */
30 {
31      int i;
32      for (i = 0; i < 16; ++i) out[i] = a[i] - b[i];
33 }
-}

fsub :: PrimMonad m
    => FieldElemM (PrimState m) -- ^ out = a - b
    -> FieldElemM (PrimState m) -- ^ a
    -> FieldElemM (PrimState m) -- ^ b
    -> m ()
fsub out a b = do
    for16 $ \i -> do
        a' <- index a i
        b' <- index b i
        write out i $! a' - b'


{- 35 static void fmul(field_elem out, const field_elem a, const field_elem b) /* out = a * b */
36 {
37      i64 i, j, product[31];
38      for(i=0;i<31;++i)product[i]=0;
39      for(i=0;i<16;++i){
40          for (j = 0; j < 16; ++j) product[i+j] += a[i] * b[j];
41      }
42      for (i = 0; i < 15; ++i) product[i] += 38 * product[i+16];
43      for (i = 0; i < 16; ++i) out[i] = product[i];
44      carry25519(out);
45      carry25519(out);
46      }
-}

fmul :: PrimMonad m
    => FieldElemM (PrimState m) -- ^ out = a - b
    -> FieldElemM (PrimState m) -- ^ a
    -> FieldElemM (PrimState m) -- ^ b
    -> m ()
fmul out a b = do
    prod <- newSized 31
    for16 $ \i ->
        for16 $ \j -> do
            ai <- index a i
            bj <- index b j
            modify prod (i+j) ((ai * bj) +)
    forM_ [0..14] $ \i -> do
        pi16 <- index prod (i+16)
        modify prod i (+ (38 * pi16))
    for16 $ \i -> write out i =<< index prod i
    carry25519 out
    carry25519 out

{-
5 static void finverse(field_elem out, const field_elem in)
6{
7       field_elem c;
8       int i;
9       for (i =0;i < 16; ++i) c[i] = in[i];
10      for (i = 253; i>=0;i--){
11          fmul(c,c,c);
12          if (i != 2 && i != 4) fmul(c,c,in);
13      }
14      for(i=0;i<16;++i)out[i]=c[i];
15      }
-}

finverse :: PrimMonad m
    => FieldElemM (PrimState m) -- ^ out = a^-1
    -> FieldElemM (PrimState m) -- ^ a
    -> m ()
finverse out fe = do
    c <- new
    for16 $ \i -> write c i =<< index fe i
    forM_ [253, 253-1 .. 0 :: Int] $ \i -> do
        fmul c c c
        when (i /= 2 && i /= 4) $
            fmul c c fe
    for16 $ \i -> write out i =<< index c i

    pure ()

testInverseMul :: PrimMonad m
    =>  FieldElem
    -> m ByteString
testInverseMul a = do
    a' <- thaw a
    ainv <- new
    finverse ainv a'
    res <- new
    fmul res a' ainv
    pack25519 res


{-

17 static void swap25519(field_elem p, field_elem q, int bit)
18 {
19      i64 t,i,c=~(bit-1);
20      for(i=0;i<16;++i){
21          t = c & (p[i] ^ q[i]);
22          p[i] ^= t;
23          q[i] ^= t;
24      }
25 }
-}

swap25519 :: PrimMonad m
    => FieldElemM (PrimState m) -- ^ out = a^-1
    -> FieldElemM (PrimState m) -- ^ a
    -> I64
    -> m ()
swap25519 p q bit_ = do
    let !c = complement (bit_ - 1)
    for16 $ \i -> do
        pi_ <- index p i
        qi  <- index q i
        let !t = c .&. (pi_ `xor` qi)
        modify p i (xor t)
        modify q i (xor t)

{-

27 static void pack25519(u8 *out, const field_elem in)
28 {
29      int i, j, carry;
30      field_elem m, t;
31      for(i=0;i<16;++i)t[i]=in[i];
32      carry25519(t); carry25519(t); carry25519(t);
33      for(j=0;j<2;++j){
34          m[0] = t[0] - 0xffed;
35          for(i = 1; i < 15; i++) {
36              m[i] = t[i] - 0xffff - ((m[i-1] >> 16) & 1);
37              m[i-1] &= 0xffff;
38          }
39          m[15] = t[15] - 0x7fff - ((m[14] >> 16) & 1);
40          carry = (m[15] >> 16) & 1;
41          m[14] &= 0xffff;
42          swap25519(t, m, 1 - carry);
43      }
44      for(i=0;i<16;++i){
45          out[2*i] = t[i] & 0xff;
46          out[2*i + 1] = t[i] >> 8;
47      }
48 }

-}

pack25519' :: PrimMonad m
    => FieldElemM (PrimState m) -- ^ out = a where all elements are in [0..2^16-1] and total is mod p
    -> FieldElemM (PrimState m) -- ^ a
    -> m ()
pack25519' out a = do
    m <- new
    let t = out
    for16 $ \i -> write t i =<< index a i
    carry25519 t
    carry25519 t
    carry25519 t
    replicateM_ 2 $ do
        write m 0 =<< (index t 0 <&> (subtract 0xffed))
        forM_ [1..14] $ \i -> do
            ti  <- index t i
            mi1 <- index m (i-1)
            write m i     $! ti - 0xffff - ((mi1 `unsafeShiftR` 16) .&. 1)
            write m (i-1) $! mi1 .&. 0xffff
        m14 <- index m 14
        t15 <- index t 15
        write m 15 $! t15 - 0x7fff - ((m14 `unsafeShiftR` 16) .&. 1)
        m15 <- index m 15
        let !carry = (m15 `unsafeShiftR` 16) .&. 1
        write m 14 $ m14 .&. 0xffff
        swap25519 t m (1 - carry)

pack25519 :: PrimMonad m
    => FieldElemM (PrimState m)
    -> m ByteString
pack25519 a = do
    (FieldElem frozen) <- withFieldElem' $ \out -> pack25519' out a
    let (!bs,_) = BS.unfoldrN 32 f 0
        f i =
            let !i' = i + 1
                !v = fromIntegral $(V.unsafeIndex frozen (i `unsafeShiftR` 1)
                        `unsafeShiftR` (8 * (i .&. 1))
                    ) .&. 0xffff
            in Just $! (v,i')
    pure bs