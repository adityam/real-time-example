Introduction
============

This program finds the best memoryless and real-time communication
schemes for a three-step communication system. In order to be more
efficient, parts of the code are written specifically for a three-step
system rather than for a generic system. However, it should be simple to
extend these ideas to larger systems. This code is written in literate
Haskell; Haskell is a lazy functional language, which appeared to be a
good match for the task at hand. 

> module Main  where
> import Array ((!), Array, array, inRange, Ix)
> import Data.Function (on)
> import Data.List (minimumBy)
> import qualified Data.Map as Map (fromList, toList, Map, elems) 
> import Test.QuickCheck ((==>),quickCheck)
> import System.IO (hFlush, stdout)


Details of the communication system
===================================

We assume that the source is a binary time-homogeneous first-order Markov
source. The variable `initial` denotes the initial pmf (probability mass
function) of the source. Since the source is binary, we need only one quantity
to characterize it, viz, the probability of being in state `0` in the
beginning. 

> type Matrix = Array Pair Rational
> type Vector = Array Bit Rational
> getInitial :: Rational -> Vector
> getInitial p = array (Bit 0, Bit 1) [(Bit 0,p), (Bit 1,1-p)]

The variable `source` represents the matrix of transition probability of
the source. It is characterized by two quantities: the crossover
probabilities at states `0` and `1`. 

> getSource :: Rational -> Rational -> Matrix
> getSource p0 p1 = array bounds1 list where
>   list   = [ ((Bit 0, Bit 0), 1 - p0 )
>            , ((Bit 0, Bit 1), p0     )
>            , ((Bit 1, Bit 0), p1     )
>            , ((Bit 1, Bit 1), 1 - p1 )]

The variable `channel` represents the channel matrix. It is also
characterized by two quantities: the crossover probabilities for inputs
`0` and `1`

> getChannel :: Rational -> Rational -> Matrix
> getChannel = getSource


The variable `distortion` represents the distortion function. It is
characterized by two parameters: the distortion when `0` is not
identified, and the distortion when `1` is not identified.

> getDistortion :: Rational -> Rational -> Matrix
> getDistortion d0 d1 = array bounds1 list where
>   list   = [((Bit 0, Bit 0), 0 )
>            ,((Bit 0, Bit 1), d0)
>            ,((Bit 1, Bit 0), d1)
>            ,((Bit 1, Bit 1), 0 )]

Preliminaries
=============

All the alphabets in this code are binary, so we define some commonly
used lists.

> newtype Bit = Bit Int deriving (Eq, Show, Ord, Ix)
> fromBit (Bit x) = fromIntegral x
> type Pair = (Bit, Bit)

> bits  = [Bit 0, Bit 1] 
> bits2 = [(x,y) | x <- bits, y <- bits]
> bits3 = [(x,y,z) | x <- bits, y <- bits, z <-bits ]

> pair00  = (Bit 0, Bit 0)
> pair11  = (Bit 1, Bit 1)
> bounds1 = (pair00, pair11)
> bounds2 = ( (pair00, pair00), (pair11, pair11) )
> bounds3 = ( (pair00, pair00, pair00), (pair11, pair11, pair11) )

We also define a newtype for time.

> newtype Time = Time Int deriving (Eq, Show, Ord, Ix)

The codebook
============

We want a common syntax to represent codes (both the encoding strategies
and the decoding strategies). We decide to enumerate codes based on
their base2 representation. For example, there are 16 codes for two
inputs:


 AB   0   1   2   3   ...   16  
---- --- --- --- --- ----- ---- 
 11   0   0   0   0   ...    1  
 10   0   0   0   0   ...    1  
 01   0   0   1   1   ...    1  
 00   0   1   0   1   ...    1  

We define `codebook` that does this. First we define a data type `Code`
and a means to display its "number"

> type Code =  Array (Bit,Bit,Bit) Bit

    -- instance Show Code where
    --   show = showCode3

> showCode3 :: Code -> String
> showCode3 f = show value where
>    value :: Int
>    value = 128*f'(Bit 1, Bit 1, Bit 1) + 64*f'(Bit 1, Bit 1, Bit 0) + 32*f'(Bit 1, Bit 0, Bit 1) 
>          +  16*f'(Bit 1, Bit 0, Bit 0) +  8*f'(Bit 0, Bit 1, Bit 1) +  4*f'(Bit 0, Bit 1, Bit 0)
>          +   2*f'(Bit 0, Bit 0, Bit 1) +  f'(Bit 0, Bit 0, Bit 0) 
>    f'    = fromBit.(f!)

Now, the definition of `codebook`. It is based on a recursive evaluation
of base2 coefficients. The function `codebook` is called many times; in
the original implementation it was taking 40% of the time. So, we
decided to use a memoized version. The original version is now called
`codebook'`

> newtype Index = Index Int deriving (Show, Eq, Ord, Ix)
> codebook :: Index -> Code
> codebook = (!) codebookArray
>
> codebookArray :: Array Index Code
> codebookArray = array bounds list where
>   bounds = (Index 0, Index 255) 
>   list   = do
>       n <- map Index [0.. 255]
>       let codeFunction = codebook' n
>           code = array ( (Bit 0, Bit 0, Bit 0), (Bit 1, Bit 1, Bit 1) ) codelist where
>             codelist = do
>                 (x,y,z) <- bits3
>                 let output = codeFunction [x,y,z]
>                 return ((x,y,z), output)
>       return (n, code)

> codebook' :: Index -> ([Bit] -> Bit)
> codebook' (Index n) [] | n < 2 = Bit n
>                        | otherwise = error $ "index out of bounds:" ++ show n
>
> codebook' (Index n) list@(Bit x:xs) = codebook' (Index (n `func` s)) xs where
>   s = 2^(2^(length list - 1))
>   func | x == 0 = rem
>        | x == 1 = div
>        | otherwise = error "coefficient must be binary"

Lets do a quick check to see if the cobebook is working properly.

> prop_Codebook n = inRange (0,255) n  ==> show n == showCode3 (codebook (Index n))
>      where types = n :: Int

Code filters
------------

We need a function to check if a code (from the 3-step codebook)
measurable at time 1 and 2. The following function does that:

> isMeasurable :: Time -> Code -> Bool
> isMeasurable time code = and conditions where
>   conditions | time == Time 1 = map check1 bits
>              | time == Time 2 = map check2 bits2
>              | otherwise = [True]
>   check1   x   = all (code!(x, Bit 0, Bit 0)==) [ code!(x,y,z) | (y,z) <- bits2 ]
>   check2 (x,y) = code!(x,y, Bit 0) == code!(x,y, Bit 1)

We also need a function to check if a code (from a 3-step codebook) is
memoryless at time 1, 2 and 3. 

> isMemoryless :: Time -> Code -> Bool
> isMemoryless time code = and conditions where
>   conditions | time == Time 1 = map check1 bits
>              | time == Time 2 = map check2 bits
>              | time == Time 3 = map check3 bits
>   check1 x = all (code!(    x, Bit 0, Bit 0)==) [code!(x,y,z) | (y,z) <- bits2]
>   check2 y = all (code!(Bit 0,     y, Bit 0)==) [code!(x,y,z) | (x,z) <- bits2]
>   check3 z = all (code!(Bit 0, Bit 0,     z)==) [code!(x,y,z) | (x,y) <- bits2]

Code families
----------------

We define two code families, `memorylessCodes` and `realtimeCodes`.
Later, we will find optimal encoders and decoders from within each
family.

> allCodes :: [Code]
> allCodes = map (codebook . Index) [0.. 255]
>
> type CodeFamily = Array Time [Code]
>
> realtimeCodes, memorylessCodes :: CodeFamily
> realtimeCodes = array (Time 1, Time 3) list where
>   list = do
>       t <- map Time [1,2,3]
>       let codes = filter (isMeasurable t) allCodes
>       return(t,codes)
>
> memorylessCodes = array (Time 1, Time 3) list where
>   list = do
>       t <- map Time [1,2,3]
>       let codes = filter (isMemoryless t) allCodes
>       return(t,codes)

Joint Distributions (Information states)
========================================

> type Distribution1 = Array Pair             Rational
> type Distribution2 = Array (Pair,Pair)      Rational
> type Distribution3 = Array (Pair,Pair,Pair) Rational

This function computes the joint distribution of $(X_1, Y_1)$  for any
stage 1 code.

> distribution1 :: Vector ->  Matrix -> Matrix 
>                -> Code -> Distribution1
> distribution1 initial source channel code = array bounds1 list where
>   list   = do
>       (x1,y1) <- bits2
>       let z1  =  code!(x1, Bit 0, Bit 0) 
>       -- TODO: raise an error if code is not measurable at time 1
>           p   = initial!x1 * channel!(z1, y1)
>       return ((x1,y1), p)

The next function computes the joint distribution of $(X_1, Y_1, X_2,
Y_2)$ (represented as $( (X_1, Y_1), (X_2, Y_2) )$ since this makes it
easier to write the joint distribution for stage 3. Haskell does not
define an instance of `Ix` for `(t1,t2,t3,t4,t5,t6)`. The instance of
`(t1,t2,t3,t4,t5)` defined by GHC uses unsafe operators which are not
exported. So, we cannot define an instance for `(t1,...,t6)` using unsafe
operators. The normal definitoin can be unoptimized. Hence, this
grouping trick). 

> distribution2 :: Vector ->  Matrix -> Matrix -> Distribution1 -> Code 
>               -> Distribution2
> distribution2 initial source channel dist1 code = array bounds2 list where
>   list   = do
>       (x1,y1) <- bits2
>       (x2,y2) <- bits2
>       let z2 = code!(x1,x2, Bit 0)
>       -- TODO: raise an error if code is not measurable at time 2
>           p = channel!(z2, y2)
>             * source !(x1, x2)
>             * dist1  !(x1, y1)
>       return ( ((x1,y1), (x2,y2)), p)

Now we define a function that gives the joint probability of
$((X_1,Y_1), (X_2, Y_2), (X_3, Y_3))$.

> distribution3 ::Vector ->  Matrix -> Matrix -> Distribution2 -> Code
>               -> Distribution3
> distribution3 initial source channel dist2 code = array bounds3 list where
>   list   = do
>       (x1,y1) <- bits2
>       (x2,y2) <- bits2
>       (x3,y3) <- bits2
>       let z3  = code!(x1,x2,x3)
>           p   = channel!(z3, y3)
>               * source !(x2, x3)
>               * dist2  !((x1,y1), (x2,y2))
>       return ( ((x1,y1),(x2,y2),(x3,y3)), p)

Optimal Decoding
================

We define a function to find the best decoder from a given family of
codes (can be `memorylessCodes` or `realtimeCodes`). The function
returns the optimal performance, and the first decoder that achieves it. 

TODO: At some stage, we can consider returning all optimal decoders. But
first, we need to figure out how much does that hurt the complexity of
the algorithm. For this purpose, we abstract out the code that finds the
best from a list.

> best :: (Ord a) => [(a, b)] -> (a, b)
> best = minimumBy (compare `on` fst)

> decode1 :: CodeFamily -> Matrix -> Distribution1
>         -> (Rational, Code)
> decode1 family distortion dist = best values where
>   values = do
>       g1 <- family ! Time 1
>       let errors = do
>           (x1,y1) <- bits2
>           let x'1 = g1!(y1, Bit 0, Bit 0)
>               err = distortion!(x1, x'1) * dist!(x1, y1)
>           return err
>       let cost = sum errors 
>       return (cost, g1)

Now, to find the best decoder at time 2.

> decode2 :: CodeFamily -> Matrix -> Distribution2
>         -> (Rational, Code)
> decode2 family distortion dist = best values where
>   values = do
>       g2 <- family ! Time 2
>       let errors = do
>           (x1, y1) <- bits2
>           (x2, y2) <- bits2
>           let x'2  = g2!(y1, y2, Bit 0)
>               err  = distortion!(x2, x'2) * dist!((x1,y1), (x2,y2))
>           return err
>       let cost = sum errors
>       return (cost, g2)

and, the best decoder at time 3.

> decode3 :: CodeFamily -> Matrix -> Distribution3
>         -> (Rational, Code)
> decode3 family distortion dist = best values where
>   values = do
>       g3 <- family ! Time 3
>       let errors = do
>           (x1, y1) <- bits2
>           (x2, y2) <- bits2
>           (x3, y3) <- bits2
>           let x'3 = g3!(y1,y2,y3)
>               err = distortion!(x3, x'3) * dist!((x1,y1), (x2,y2), (x3,y3))
>           return err
>       let cost = sum errors
>       return (cost, g3)

Information states
==================

Now we construct the reachable set of the information states for each
family of codes. We store the states in a `Map` (Haskell way of doing
hashes).

TODO: Again, we only keep one of the optimal communication strategies.
We can instead use `Map.fromListWith` and combine all the strategies that
lead to the same information state. Until we take care of storing all
optimal decoders, doing this does not make sense.

> states1 ::CodeFamily ->  Vector -> Matrix -> Matrix -> Matrix 
>       -> Map.Map Distribution1 (Rational,(Code, Code))
> states1 family initial source channel distortion = Map.fromList list where
>   decode1' = decode1 family distortion
>   distribution1' = distribution1 initial source channel
>   list = do
>       c1 <- family ! Time 1
>       let dist = distribution1' c1
>           (cost,g1) = decode1' dist
>           strategy  = (cost,(c1,g1))
>       return (dist,strategy) 

Now, we construct all reachable states at time 2 for a given family.

> states2 :: CodeFamily -> Vector -> Matrix -> Matrix -> Matrix 
>         -> Map.Map Distribution2 ([Rational],([Code],[Code]))
> states2 family initial source channel distortion = Map.fromList list where
>   decode2' = decode2 family distortion
>   distribution2' = distribution2 initial source channel 
>   states1' = states1 family initial source channel distortion
>   list = do
>       c2 <- family ! Time 2
>       (dist1, (cost1,(c1,g1))) <- Map.toList states1' 
>       let dist2 = distribution2' dist1 c2
>           (cost2, g2) = decode2' dist2
>           strategy    = ([cost1,cost1 + cost2], ( [c1,c2], [g1,g2] ))
>       return (dist2, strategy)

and, for states at time 3:

> states3 :: CodeFamily -> Vector -> Matrix -> Matrix -> Matrix 
>         -> Map.Map Distribution3 ([Rational],([Code],[Code]))
> states3 family initial source channel distortion = Map.fromList list where
>   decode3' = decode3 family distortion
>   distribution3' = distribution3 initial source channel
>   states2' = states2 family initial source channel distortion
>   list = do
>       c3 <- family ! Time 3
>       (dist2, (cost2,(c12,g12))) <- Map.toList states2'
>       let dist3 = distribution3' dist2 c3
>           (cost3, g3) = decode3' dist3
>           cost  = cost2 ++ [last cost2 + cost3]
>           strategy = (cost, (c12++[c3], g12++[g3])) 
>       return (dist3, strategy)

Optimal Codes
=============

> memoryless initial source channel distortion horizon 
>    = allBest horizon $ Map.elems states where
>       states =  states3 memorylessCodes initial source channel distortion
> realtime initial source channel distortion horizon 
>   = allBest horizon $ Map.elems states  where 
>       states  = states3 realtimeCodes initial source channel distortion
> realtimeFast initial source channel distortion horizon 
>   = allBest horizon $ Map.elems states where
>       states  = states3' initial source channel distortion
>
> -- allBest horizon list = map (\x -> bestAt  x list) [1..horizon]
> allBest = flip (map . flip bestAt) . enumFromTo 1
> 
> bestAt horizon = best . map cost where
>   cost (a,b) = (a!!(horizon-1),b)

Real-time codes revisited
=========================

The above code is clean and fast (it taks about 200 seconds to execute),
but not fast enough to do a lot of case studies. So, we will try to
optimize it. A look at profiler output shows that most of the time is spent
on `decode3` function. This function can be optimized by making use of the
structural results. The new code takes about 6 seconds to execute.

> decode3Fast :: Matrix -> Distribution3
>         -> (Rational, Code)
> decode3Fast distortion dist = (sum errors, array bounds decoder) where
>   bounds = ((Bit 0, Bit 0, Bit 0),(Bit 1, Bit 1, Bit 1))
>   (errors,decoder) = unzip result
>   result = do
>       (y1,y2,y3) <- bits3
>       let (err,output) = optimalDecode (y1,y2,y3)
>       return (err, ((y1,y2,y3), output))
>   totalD (y1,y2,y3) x' = sum $ do
>       (x1,x2,x3) <- bits3
>       let d = distortion!(x3,x') * dist!( (x1,y1), (x2,y2), (x3,y3))
>       return d
>   optimalDecode inputs = min (totalD inputs $ Bit 0, Bit 0) 
>                              (totalD inputs $ Bit 1, Bit 1)

Now we can redefine `states3` as follows

> states3' :: Vector -> Matrix -> Matrix -> Matrix 
>          -> Map.Map Distribution3 ([Rational], ([Code],[Code]))
> states3' initial source channel distortion = Map.fromList list where
>   family = realtimeCodes
>   decode3' = decode3Fast distortion
>   distribution3' = distribution3 initial source channel
>   states2' = states2 family initial source channel distortion
>   list = do
>       c3 <- family ! Time 3
>       (dist2, (cost2,(c12,g12))) <- Map.toList states2' 
>       let dist3 = distribution3' dist2 c3
>           (cost3, g3) = decode3' dist3
>           cost  = cost2 ++ [last cost2 + cost3]
>           strategy = (cost, (c12++[c3], g12++[g3])) 
>       return (dist3, strategy)


Output
======

We output the result in YAML format which will make it easier to postprocess
the result later on.

> showOutput :: Vector -> Matrix -> Matrix -> Matrix -> Int 
>            -> IO()
> showOutput initial source channel distortion horizon = do
>   let ml = memoryless    initial source channel distortion horizon
>       rt = realtimeFast  initial source channel distortion horizon
>   putStrLn "---"
>   putStrLn "system:"
>   putStr   $ showSystem initial source channel distortion horizon
>   putStrLn "memoryless:"
>   putStr   $ showResult ml 
>   putStrLn "realtime:"
>   putStr   $ showResult rt 
>   hFlush stdout 
>   where 
>       showResult list = concatMap showResult' $ zip list [1..]
>       showResult' ((cost,(c,g)),t) = unlines list where
>           list = [ unwords ["- horizon:", show t] 
>                  , unwords ["  performance:"
>                            , show cost
>                            , showR cost]
>                  , unwords ["  encoder:", showCodes c]
>                  , unwords ["  decoder:", showCodes g]] 
>       showSystem initial source channel distortion horizon 
>           = unlines list where
>               list = [ unwords ["- initial:", showR $ initial!Bit 0 ]
>                      , unwords ["- source:" 
>                                , showR $ source!(Bit 0, Bit 1)
>                                , showR $ source!(Bit 1, Bit 0)]
>                      , unwords ["- channel:"
>                                 , showR $ channel!(Bit 0, Bit 1)
>                                 , showR $ channel!(Bit 1, Bit 0)]
>                      , unwords ["- distortion:"
>                                , showR $ distortion!(Bit 0, Bit 1)
>                                , showR $ distortion!(Bit 1, Bit 0)]]
>       showR = show . fromRational
>       showCodes codes = "[" ++ (unwords $ map showCode3 codes) ++ "]"


Now, the main program:

> main = sequence_ outputs where
>   horizon = 3
>   outputs = do
>      i <- [0.4::Rational] -- [0.1, 0.2 .. 0.5 :: Rational ]
>      s0 <- [0.0::Rational] -- [0.0, 0.1 .. 1.0 :: Rational ]
>      s1 <- [0.1::Rational] -- [0.0, 0.1 .. 1.0 :: Rational ]
>      c0 <- [0.1::Rational] -- [0.0, 0.1 .. 0.5 :: Rational ]
>      c1 <- [0.0::Rational] -- [0.0, 0.1 .. 0.5 :: Rational ]
>      let initial    = getInitial    i
>          source     = getSource     s0 s1
>          channel    = getChannel    c0 c1
>          distortion = getDistortion 1.0 1.0
>          output = showOutput initial source channel distortion horizon
>      return output  
