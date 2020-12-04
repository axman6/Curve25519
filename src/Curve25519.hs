{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{- |
Copyright: (c) 2020 Alex Mason
SPDX-License-Identifier: MIT
Maintainer: Alex Mason <github@me.axman6.com>

See README for more infoPure HAskell iomplementation of Curve255 19
-}

module Curve25519 (Field, testInverseMul, unpack25519, pack25519, scalarmult, finverse) where
    --    ( Field
    --    , FieldM
    --    , withField
    --    , unpack25519
    --    ) where

import Data.Int (Int64)
import Data.Word (Word8)

import Data.Bits

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Unsafe as BSU

import Control.Monad (replicateM_, when, forM_)
import Control.Monad.ST
import Control.Monad.Primitive
import Data.Functor ((<&>))

import Data.Primitive.ByteArray

type I64 = Int64

data Field    = Field  {-# UNPACK #-}!ByteArray            deriving stock Show
data FieldM s = FieldM {-# UNPACK #-}!(MutableByteArray s)

withField :: PrimMonad m => Field -> (FieldM (PrimState m) -> m a) -> m Field
{-# INLINE withField #-}
withField inV f = do
    !minV <- thaw inV
    !_ <- f minV
    unsafeFreeze minV

thaw :: PrimMonad m => Field -> m (FieldM (PrimState m))
{-# INLINE thaw #-}
thaw (Field ba) = do
  let !size = sizeofByteArray ba
  mba <- newByteArray size
  copyByteArray mba 0 ba 0 size
  pure $! FieldM mba

unsafeFreeze :: PrimMonad m => FieldM (PrimState m) -> m Field
{-# INLINE unsafeFreeze #-}
unsafeFreeze (FieldM mba) = do
  !ba <- unsafeFreezeByteArray mba
  pure $! Field ba

withField' :: PrimMonad m => (FieldM (PrimState m) -> m a) -> m Field
{-# INLINE withField' #-}
withField' f = do
    a <- new
    !_ <- f a
    unsafeFreeze a

new :: PrimMonad m => m (FieldM (PrimState m))
{-# INLINE new #-}
new = newSized 16

newSized :: PrimMonad m => Int ->  m (FieldM (PrimState m))
{-# INLINE newSized #-}
newSized numInts = do
  !mba <- newByteArray (numInts * 8)
  setByteArray mba 0 numInts (0::Int64)
  pure $ FieldM mba

index :: PrimMonad m =>  FieldM (PrimState m) -> Int -> m I64
{-# INLINE index #-}
index (FieldM mba) i = readByteArray mba i

unsafeIndex :: Field -> Int -> I64
{-# INLINE unsafeIndex #-}
unsafeIndex (Field ba) i = indexByteArray ba i

write :: PrimMonad m => FieldM (PrimState m) -> Int -> I64 -> m ()
{-# INLINE write #-}
write (FieldM mba) !i !e = writeByteArray mba i e

modify :: PrimMonad m => FieldM (PrimState m) -> Int -> (I64 -> I64) -> m ()
{-# INLINE modify #-}
modify field !i !f = do
  e <- index field i
  write field i $! f e

for16 :: Monad m => (Int -> m a) -> m ()
{-# INLINE for16 #-}
for16 f = forM_ [0..15] f

copy16 :: PrimMonad m => FieldM (PrimState m) -> FieldM (PrimState m) -> m ()
{-# INLINE copy16 #-}
copy16 to from = for16 $ \i -> write to i =<< index from i

(>>>), (<<<) :: Bits a => a -> Int -> a
{-# INLINE (>>>) #-}
{-# INLINE (<<<) #-}
a >>> n = unsafeShiftR a n
a <<< n = unsafeShiftL a n
{-
5 static void unpack25519(field_elem out, const u8 *in)
6{
7     int i;
8     for (i = 0; i < 16; ++i) out[i] = in[2*i] + ((i64) in[2*i + 1] << 8);
9     out[15] &= 0x7fff;
10 }
-}
unpack25519 :: ByteString -> Field
unpack25519 bs
    | BS.length bs /= 32 = error "unpack25519: Input must be 32 bytes long"
    | otherwise = runST $ withField' $ \fe ->
            for16 $ \i -> do
                let !lo = fromIntegral $ BSU.unsafeIndex bs (i*2)
                    !hi = fromIntegral $ BSU.unsafeIndex bs (i*2 + 1)
                write fe i (lo + (hi <<< 8))
                modify fe 15 (.&. 0x7fff)

unpack25519M :: PrimMonad m => ByteString -> m (FieldM (PrimState m))
unpack25519M bs
    | BS.length bs /= 32 = error "unpack25519: Input must be 32 bytes long"
    | otherwise = do
        fe <- new
        for16 $ \i -> do
            let !lo = fromIntegral $ BSU.unsafeIndex bs (i*2)
                !hi = fromIntegral $ BSU.unsafeIndex bs (i*2 + 1)
            write fe i (lo + (hi <<< 8))
            modify fe 15 (.&. 0x7fff)
        pure fe


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
carry25519 :: PrimMonad m => FieldM (PrimState m) -> m ()
carry25519 fe = do
    for16 $ \i -> do
        !carry <- index fe i <&> (>>> 16)
        modify fe i $ \e -> e - carry <<< 16
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
    => FieldM (PrimState m) -- ^ out = a + b
    -> FieldM (PrimState m) -- ^ a
    -> FieldM (PrimState m) -- ^ b
    -> m ()
fadd out a b = do
    for16 $ \i -> do
        a' <- index a i
        b' <- index b i
        write out i $! a' + b'

(+=) :: PrimMonad m
    => FieldM (PrimState m)                             -- ^ out = a + b
    -> (FieldM (PrimState m), FieldM (PrimState m)) -- ^ (a,b)
    -> m ()
out += (a,b) = fadd out a b

{-
29 static void fsub(field_elem out, const field_elem a, const field_elem b) /* out = a - b */
30 {
31      int i;
32      for (i = 0; i < 16; ++i) out[i] = a[i] - b[i];
33 }
-}

fsub :: PrimMonad m
    => FieldM (PrimState m) -- ^ out = a - b
    -> FieldM (PrimState m) -- ^ a
    -> FieldM (PrimState m) -- ^ b
    -> m ()
fsub out a b = do
    for16 $ \i -> do
        a' <- index a i
        b' <- index b i
        write out i $! a' - b'

(-=) :: PrimMonad m
    => FieldM (PrimState m)                             -- ^ out = a + b
    -> (FieldM (PrimState m), FieldM (PrimState m)) -- ^ (a,b)
    -> m ()
out -= (a,b) = fsub out a b


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
    => FieldM (PrimState m) -- ^ out = a - b
    -> FieldM (PrimState m) -- ^ a
    -> FieldM (PrimState m) -- ^ b
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
    copy16 out prod
    carry25519 out
    carry25519 out

(*=) :: PrimMonad m
    => FieldM (PrimState m)                             -- ^ out = a + b
    -> (FieldM (PrimState m), FieldM (PrimState m)) -- ^ (a,b)
    -> m ()
out *= (a,b) = fmul out a b

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
    => FieldM (PrimState m) -- ^ out = a^-1
    -> FieldM (PrimState m) -- ^ a
    -> m ()
finverse out fe = do
    c <- new
    copy16 c fe
    forM_ [253, 253-1 .. 0 :: Int] $ \i -> do
        c *= (c, c)
        when (i /= 2 && i /= 4) $
            c *= (c, fe)
    copy16 out c

(~=) :: PrimMonad m
    => FieldM (PrimState m) -- ^ out = a + b
    -> FieldM (PrimState m) -- ^ a
    -> m ()
out ~= a = finverse out a

testInverseMul :: PrimMonad m
    =>  Field
    -> m ByteString
testInverseMul a = do
    a' <- thaw a
    ainv <- new
    ainv ~= a'
    res <- new
    res *= (a', ainv)
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
    => FieldM (PrimState m) -- ^ out = a^-1
    -> FieldM (PrimState m) -- ^ a
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
    => FieldM (PrimState m) -- ^ out = a where all elements are in [0..2^16-1] and total is mod p
    -> FieldM (PrimState m) -- ^ a
    -> m ()
pack25519' out a = do
    m <- new
    let t = out
    copy16 t a
    carry25519 t
    carry25519 t
    carry25519 t
    replicateM_ 2 $ do
        write m 0 =<< (index t 0 <&> (subtract 0xffed))
        forM_ [1..14] $ \i -> do
            ti  <- index t i
            mi1 <- index m (i-1)
            write m i     $! ti - 0xffff - ((mi1 >>> 16) .&. 1)
            write m (i-1) $! mi1 .&. 0xffff
        m14 <- index m 14
        t15 <- index t 15
        write m 15 $! t15 - 0x7fff - ((m14 >>> 16) .&. 1)
        m15 <- index m 15
        let !carry = (m15 >>> 16) .&. 1
        write m 14 $ m14 .&. 0xffff
        swap25519 t m (1 - carry)

pack25519 :: PrimMonad m
    => FieldM (PrimState m)
    -> m ByteString
pack25519 a = do
    frozen <- withField' $ \out -> pack25519' out a
    let (!bs,_) = BS.unfoldrN 32 f 0
        f i =
            let !i' = i + 1
                !v = fromIntegral $ (unsafeIndex frozen (i >>> 1)
                        >>> (8 * (i .&. 1))
                    ) .&. 0xffff
            in Just $! (v,i')
    pure bs


{-
1 typedef long long i64;
2 typedef i64 field_elem[16];
3 static const field_elem _121665 = {0xDB41, 1},
4
5 void scalarmult(u8 *out, const u8 *scalar, const u8 *point)
6 {
7       u8 clamped[32];
8       i64 bit, i;
9       field_elem a, b, c, d, e, f, x;
10      for (i = 0; i < 31; ++i) clamped[i] = scalar[i];
11      clamped[0] &= 0xf8;
12      clamped[31] = (clamped[31] & 0x7f) | 0x40;
13      unpack25519(x, point);
14      for (i = 0; i < 16; ++i) {
15          b[i] = x[i];
16          d[i] = a[i] = c[i] = 0;
17      }
18      a[0] = d[0] = 1;
19      for (i = 254; i >= 0; --i) {
20          bit = (clamped[i >> 3] >> (i & 7)) & 1;
21          swap25519(a, b, bit);
22          swap25519(c, d, bit);
23          fadd(e, a, c);
24          fsub(a, a, c);
25          fadd(c, b, d);
26          fsub(b, b, d);
27          fmul(d, e, e);
28          fmul(f, a, a);
29          fmul(a, c, a);
30          fmul(c, b, e);
31          fadd(e, a, c);
32          fsub(a, a, c);
33          fmul(b, a, a);
34          fsub(c, d, f);
35          fmul(a, c, _121665);
36          fadd(a, a, d);
37          fmul(c, c, a);
38          fmul(a, d, f);
39          fmul(d, b, x);
40          fmul(b, e, e);
41          swap25519(a, b, bit);
42          swap25519(c, d, bit);
43      }
44      finverse(c, c);
45      fmul(a, a, c);
46      pack25519(out, a);
47 }
-}

scalarmult :: PrimMonad m
    => ByteString
    -> ByteString
    -> m ByteString
scalarmult scalar point = do
    -- static const field_elem _121665 = {0xDB41, 1},
    const_121665 <- new
    write const_121665 0 0xDB41
    write const_121665 1 0x0001
    -- field_elem a, b, c, d, e, f, x;
    a <- new
    b <- new
    c <- new
    d <- new
    e <- new
    f <- new
    -- unpack25519(x, point);
    x <- unpack25519M point
    x' <- unsafeFreeze x
    print x'
    -- for (i = 0; i < 31; ++i) clamped[i] = scalar[i];
    !clamped <- newByteArray (32 * 8)
    setByteArray clamped 0 32 (0::Int64)
    forM_ [0..31] $ \i -> do
        writeByteArray clamped i (BSU.unsafeIndex scalar i)
    -- clamped[0]                   =                  clamped[0]      &  0xf8;
    writeByteArray @Word8 clamped 0 =<< (readByteArray clamped 0 <&> (.&. 0xf8))
    -- clamped[31]            = (               clamped[31]                &  0x7f)  |   0x40;
    -- writeByteArray clamped 31 $! (((BSU.unsafeIndex scalar 31) .&. 0x7f) .|. (0x40 :: Word8))
    writeByteArray clamped 31 =<< (readByteArray clamped 31 <&> (\p -> (p .&. 0x7f) .|. (0x40 :: Word8)))
    -- for (i = 0; i < 16; ++i) {
    --     b[i] = x[i];
    --     d[i] = a[i] = c[i] = 0;
    -- }
    !clamped' <- unsafeFreeze (FieldM clamped)
    print clamped'

    copy16 b x
    -- a[0] = d[0] = 1;
    write a 0 0x1
    write d 0 0x1
    -- for (i = 254; i >= 0; --i) {
    forM_ [254, 254 - 1 .. 0] $ \i -> do
        -- bit = (clamped[i >> 3] >> (i & 7)) & 1;
        clampedi3 <- fromIntegral @Word8<$> readByteArray clamped (i >>> 3)
        let !bit = (clampedi3 >>> (i .&. 7)) .&. 1
        swap25519 a b bit
        swap25519 c d bit
        fadd e a c
        fsub a a c
        fadd c b d
        fsub b b d
        fmul d e e
        fmul f a a
        fmul a c a
        fmul c b e
        fadd e a c
        fsub a a c
        fmul b a a
        fsub c d f
        fmul a c const_121665
        fadd a a d
        fmul c c a
        fmul a d f
        fmul d b x
        fmul b e e
        swap25519 a b bit
        swap25519 c d bit
    finverse c c
    fmul a a c
    pack25519 a


    -- for16 $ \i -> do
    --     !lo <- fromIntegral @Word8 <$> readByteArray clamped (i*2)
    --     !hi <- fromIntegral @Word8 <$> readByteArray clamped (i*2 + 1)
    --     write x i (lo + (hi <<< 8))
    --     modify x 15 (.&. 0x7fff)

{-
1 typedef unsigned char u8;
2 typedef unsigned long long u64;
3 extern void randombytes(u8 *, u64);
4 static const u8 _9[32] = {9};
5
6 void scalarmult_base(u8 *out, const u8 *scalar) 7{
8   scalarmult(out, scalar, _9);
9}
-}

scalarmult_base :: PrimMonad m => ByteString -> m ByteString
scalarmult_base scalar =
    scalarmult scalar "\9\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0"

{-
void generate_keypair(u8 *pk, u8 *sk) {
  randombytes(sk, 32);
    scalarmult_base(pk, sk);
}
-}

generate_keypair :: IO (ByteString, ByteString)  -- (public, private)
generate_keypair = do


{-
void x25519(u8 *out, const u8 *pk, const u8 *sk) {
  scalarmult(out, sk, pk);
}


-}