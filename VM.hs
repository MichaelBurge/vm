{- |The program's neighboring buffers are arranged in a cyclic chain starting with the local one.
-}
module VM where
import Control.Monad.State
import Data.Bits
import Data.Maybe
import Safe

data Instruction
    = DBufL        -- ^ Move the destination data buffer pointer left.
    | DBufR        -- ^ Move the destination data buffer pointer right.
    | IBufL        -- ^ Move the destination instruction buffer pointer left.
    | IBufR        -- ^ Move the destination instruction buffer pointer right.
    | Push         -- ^ Pop the front of the local data buffer and send it to the destination. Use instruction buffer if data buffer is empty. A no-op if the local buffer.
    | Pull         -- ^ Pop the front of the destination data buffer and sends it to the local data buffer. Uses instruction buffer if data buffer is empty. A no-op if the local buffer.
    | Clone        -- ^ Clones the front of the local data buffer to the destination. If empty, clones the instruction buffer. 
    | Execute      -- ^ Executes the target instruction buffer using the destination data buffer as local source. Additionally, the instruction and data pointers are reset to 0.
    | IfZero       -- ^ Pop the data buffer and see if it's non-zero or empty. If so, then pop the instruction buffer. 
    | Ascend       -- ^ Pushes the rest of the source instruction & data buffers into the parent. This kills the current instance, but he is reborn anew into his parent.
    | Die          -- ^ You're done with your work here. Ask the VM to inject a new program.
    | DBufSize     -- ^ Gets the size of the data buffer pointed to.
    | IBufSIze     -- ^ Gets the size of the instruction buffer pointed to.
    | Neighbors    -- ^ Each of these arithmetic instructions pops from the source data buffer, and pushes to the destination buffer. If there is not enough data, then no-op. Push the number of data buffers to the destination data buffer.
    | Data Integer -- ^ Send the given integer.
    | Identity     -- ^ Send argument to destination.
    | Not          -- ^ If arg is 0, then send 1. Otherwise, send 0.
    | Increment    -- ^ Increment arg and send.
    | Decrement    -- ^ Decrement arg and send.
    | Sum          -- ^ Add both args and send.
    | Subtract     -- ^ Subtract 2nd arg from first and send.
    | And          -- ^ Bitwise AND of both arguments
    | Or           -- ^ Bitwise OR of both argumenst
    | Xor          -- ^ Bitwise XOR of both arguments
    | Cond         -- ^ Arg1 ? Arg2 : Arg3
      deriving (Eq, Show)

-- |Sum type of all buffers used in a node.
data Buffer = DBuf [Integer] 
            | IBuf [Instruction]
              deriving (Eq, Show)

-- | Predicate for filtering out Data buffers from the main list.
isDBuf :: Buffer -> Bool
isDBuf (DBuf _) = True
isDBuf _        = False

-- | Predicate for filtering out Instruction buffers from the main list.
isIBuf :: Buffer -> Bool
isIBuf (IBuf _) = True
isIBuf _        = False

dBufs :: Node -> [Buffer]
dBufs = filter isDBuf . buffers

iBufs :: Node -> [Buffer]
iBufs = filter isIBuf . buffers

-- |Lifts the given list-processing function on integers to the Buffer type.
dAp :: ([Integer] -> [Integer]) -> (Buffer -> Buffer)
dAp f = let g (DBuf xs) = DBuf $ f xs in g

-- |Lifts the given instruction-processing function to the Buffer type.
iAp :: ([Instruction] -> [Instruction]) -> (Buffer -> Buffer)
iAp f = let g (IBuf xs) = IBuf $ f xs in g

aAp :: ([Integer] -> b) -> Buffer -> b
aAp f (DBuf xs) = f xs
aAp _ _ = error "bAp applied to non-integral list"

-- |Fully defines the execution context for a node in the environment graph.
data Node = RootNode | Node {
      parent :: Node,
      buffers :: [Buffer],
      dPtr :: Integer,
      iPtr :: Integer
} deriving (Eq)

depth :: Node -> Integer
depth RootNode = 0
depth n = 1 + depth (parent n)
instance Show Node where
    show n = show $ depth n

type NodeS a = State Node a

defaultContext instrs = Node RootNode [IBuf instrs, DBuf []] 0 0

atWrap :: [a] -> Integer -> a
atWrap xs n = xs !! ((fromIntegral n) `mod` (length xs))

bufferSize :: (Buffer -> Bool) -> Integer -> State Node Integer
bufferSize pred n = do
  st <- get
  return $ fromIntegral
         $ aAp length
         $ atWrap (filter pred (buffers st))
         $ fromIntegral n

-- |Filter the buffers with a predicate, apply the transformation to the n'th remaining, and return the transformed buffer list.
modBuffers :: (Buffer -> Bool) -> Integer -> (Buffer -> Buffer) -> State Node Buffer
modBuffers pred n trans = 
    let f k (x:xs) = 
            if pred x 
            then if k == 0
                 then let y = trans x 
                      in (y:xs, y)
                 else f (k-1) (x:xs)
            else f k (x:xs)
    in do st <- get
          let (newBufs, ret) = f n $ buffers st
          put st{buffers = newBufs}
          return ret

-- |Transforms the n'th data buffer.
modData :: Integer -> (Buffer -> Buffer) -> State Node Buffer
modData = modBuffers isDBuf

-- |Transforms the n'th instruction buffer.
modInstr :: Integer -> (Buffer -> Buffer) -> State Node Buffer
modInstr = modBuffers isIBuf

-- |Pushes an integer to the n'th data buffer.
pushDTo :: Integer -> Integer -> State Node ()
pushDTo b i = 
    let f (DBuf xs) = DBuf (i:xs)
    in do modData b f
          return ()

-- |Pushes an instruction to the n'th instruction buffer.
pushITo :: Integer -> Instruction -> State Node ()
pushITo b i = 
    let f (IBuf xs) = IBuf (i:xs)
    in do modInstr b f
          return ()

-- |Peeks at the front value on the n'th data buffer. Nothing if it's empty.
peekDFrom :: Integer -> State Node (Maybe Integer)
peekDFrom b = liftM (\(DBuf xs) -> headMay xs) (modData b (dAp id))

-- |Pops a value from the n'th data buffer. Nothing if it's empty.
popDFrom :: Integer -> State Node (Maybe Integer)
popDFrom b = do
  ret <- peekDFrom b
  liftM (\(DBuf xs) -> headMay xs) (modData b (iAp tailSafe))
  return ret

-- |Pops a value from the n'th instruction buffer. Nothing if it's empty.
popIFrom :: Integer -> State Node (Maybe Instruction)
popIFrom b = do
  ret <- peekIFrom b
  liftM (\(DBuf xs) -> headMay xs) (modInstr b (iAp tailSafe))
  return ret

-- |Peeks at the front value on the n'th instruction buffer. Nothing if it's empty.
peekIFrom :: Integer -> State Node (Maybe Instruction)
peekIFrom b = liftM (\(IBuf xs) -> headMay xs) (modInstr b (iAp id))

-- | Attempts the given action for the data buffer. If successful, run a follow-up computation. Otherwise, attempt the action on the instruction buffer. If successful, run a follow-up computation. Otherwise, return nothing.
tryMod :: ((State Node (Maybe Integer)), (Integer -> State Node ()))
       -> ((State Node (Maybe Instruction)), (Instruction -> State Node ()))
       -> (State Node ())
tryMod (ds, de) (is, ie) = do
  i <- ds
  case i of
    Just a -> de a
    Nothing -> do
           j <- is
           case j of
             Just b -> ie b
             Nothing -> return ()

-- |Pops a value from the data or instruction buffer, and sends it to the destination buffer. Takes starting data/instruction values, ending data/instruction values, and returns the state computation on the Node.
transfer :: (Integer, Integer) -> (Integer, Integer) -> State Node ()
transfer (stD, stI) (endD, endI) = 
    tryMod (popDFrom stD, pushDTo endD)
           (popIFrom stI, pushITo endI)

-- |Like transfer, except it doesn't destroy the source buffer value.
clone :: (Integer, Integer) -> (Integer, Integer) -> State Node ()
clone (stD, stI) (endD, endI) =
    tryMod (peekDFrom stD, pushDTo endD)
           (peekIFrom stI, pushITo endI)

-- |Swaps two elements in a list
swap :: Integer -> Integer -> [a] -> [a]
swap 0 n ys = (ys !! (fromIntegral n)):(tail $ take (fromIntegral n) ys) ++ ((head ys):(drop (fromIntegral n) ys))
swap x n (y:ys) = y:(swap (x-1) (n-1) ys)

-- |Executes the target instruction with the source buffer. The child process' buffers may be reordered.
execute :: Integer -> Integer -> State Node ()
execute d i = do
  st <- get
  let newBuffers =  (swap 0 (dPtr st) $ filter (isDBuf) $ buffers st)
                 ++ (swap 0 (iPtr st) $ filter (isIBuf) $ buffers st)
  put st{parent = st,
         buffers = newBuffers,
         dPtr = 0,
         iPtr = 0
        }

-- |Pops the data buffer to see if non-zero. If so, then pop the instruction buffer.
ifZero :: Integer -> Integer -> State Node ()
ifZero d i = peekDFrom d >>= \val -> case val of
  Just x -> unless (x == 0) (popIFrom i >> return ())
  Nothing -> return ()

-- | Concatenate two buffers, throwing a runtime error if they're of different types.
joinBuffers :: Buffer -> Buffer -> Buffer
joinBuffers (DBuf a) (DBuf b) = DBuf (a ++ b)
joinBuffers (IBuf a) (IBuf b) = IBuf (a ++ b)
joinBuffers _ _ = error "Incompatible buffer types in joinBuffer"

mergeInto :: Node -> State Node ()
mergeInto n = do
  st <- get
  put n
  execute (dPtr n) (iPtr n)
  put n{buffers = (joinBuffers (head (buffers st)) (head (buffers n))):(tail $ buffers n)
       }

-- | Defines an arithmetic operation that takes the specified number of arguments. If any element is Nothing, then the operation is a no-op.
arith :: Int -> ([Integer] -> Integer) -> State Node ()
arith n f = do
  st <- get
  args <- sequence $ replicate n (popDFrom $ dPtr st)
  if all isJust args
     then pushDTo (dPtr st) $ f $ catMaybes args
     else put st

-- | Run the provided instruction against the node's context.
process :: Instruction -> State Node ()
process i = do
  st <- get
  case i of
-- TODO: Wrap these modulo data/instruction buffer lengths.
    DBufL     -> put $ st{dPtr = (dPtr st) - 1}
    DBufR     -> put $ st{dPtr = (dPtr st) + 1}
    IBufL     -> put $ st{iPtr = (iPtr st) - 1}
    IBufR     -> put $ st{iPtr = (iPtr st) + 1}
    Push      -> transfer (0, dPtr st) (0, iPtr st)
    Clone     -> clone    (0, dPtr st) (0, iPtr st)
    Pull      -> transfer (dPtr st, 0) (iPtr st, 0)
    Execute   -> execute (dPtr st) (iPtr st)
    IfZero    -> ifZero 0 0
    Ascend    -> mergeInto $ parent st
    DBufSize  -> pushDTo (dPtr st) =<< bufferSize isDBuf (dPtr st)
    IBufSIze  -> pushDTo (dPtr st) =<< bufferSize isIBuf (iPtr st)
    Neighbors -> arith 0 (\_        -> fromIntegral $ length $ dBufs st)
    Data n    -> arith 0 (\_        -> n)
    Identity  -> arith 1 (\(x:xs)   -> x)
    Not       -> arith 1 (\(x:xs)   -> if x == 0 then 1 else 0)
    Increment -> arith 1 (\(x:xs)   -> x + 1)
    Decrement -> arith 1 (\(x:xs)   -> x - 1)
    Sum       -> arith 2 (\(a:b:xs) -> a + b)
    Subtract  -> arith 2 (\(a:b:xs) -> a - b)
    And       -> arith 2 (\(a:b:xs) -> a .&. b)
    Or        -> arith 2 (\(a:b:xs) -> a .|. b)
    Xor       -> arith 2 (\(a:b:xs) -> a `xor` b)
    Cond      -> arith 3 (\(a:b:c:xs) -> if a > 0 then b else c)

runProgram :: [Instruction] -> Node
runProgram instrs = execState (mapM_ process instrs) (defaultContext instrs)