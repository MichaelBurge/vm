module VM where
import Control.Monad.State
import Safe
data Instruction
    = DBufL
    | DBufR
    | IBufL
    | IBufR
    | Push
    | Pull
    | Clone
    | Execute
    | IfZero
    | Ascend
    | Neighbors
    | Data Integer
    | Identity
    | Not
    | Increment
    | Decrement
    | Sum
    | Subtract
    | And
    | Or
    | Xor
    | Cond
      deriving (Eq, Show)

data Buffer = DBuf [Integer] 
            | IBuf [Instruction]
              deriving (Eq, Show)

isDBuf :: Buffer -> Bool
isDBuf (DBuf _) = True
isDBuf _        = False

isIBuf :: Buffer -> Bool
isIBuf (IBuf _) = True
isIBuf _        = False

dAp :: ([Integer] -> [Integer]) -> (Buffer -> Buffer)
dAp f = let g (DBuf xs) = DBuf $ f xs in g

iAp :: ([Instruction] -> [Instruction]) -> (Buffer -> Buffer)
iAp f = let g (IBuf xs) = IBuf $ f xs in g

data Node = Node {
      parent :: Node,
      buffers :: [Buffer],
      dPtr :: Integer,
      iPtr :: Integer
}

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

-- |Pops a value from the n'th data buffer. Nothing if it's empty.
popDFrom :: Integer -> State Node (Maybe Integer)
popDFrom b = 
    let f (DBuf xs) = DBuf $ tailSafe xs
        g (DBuf xs) = headMay xs
    in liftM g (modData b (f))

-- |Peeks at the front value on the n'th data buffer. Nothing if it's empty.
peekDFrom :: Integer -> State Node (Maybe Integer)
peekDFrom b = liftM (\(DBuf xs) -> headMay xs) (modData b (dAp id))

-- |Pops a value from the n'th instruction buffer. Nothing if it's empty.
popIFrom :: Integer -> State Node (Maybe Instruction)
popIFrom b = liftM (\(IBuf xs) -> headMay xs) (modInstr b (iAp tailSafe))

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

-- |Executes the target buffer.
-- TODO: Check execute if I finished it or not...
execute :: Integer -> State Node ()
execute b = do
  st <- get
  let newBuffers =  (swap 0 (dPtr st) $ filter (isDBuf) $ buffers st)
                 ++ (swap 0 (iPtr st) $ filter (isIBuf) $ buffers st)
  put st{parent = st,
         buffers = newBuffers,
         dPtr = 0,
         iPtr = 0
        }

-- |Run the provided instruction against the node's context.
process :: Instruction -> State Node ()
process i = do
  st <- get
  case i of
    Data n -> pushDTo 0 n
-- TODO: Wrap these modulo data/instruction buffer lengths.
    DBufL  -> put $ st{dPtr = (dPtr st) - 1}
    DBufR  -> put $ st{dPtr = (dPtr st) + 1}
    IBufL  -> put $ st{iPtr = (iPtr st) - 1}
    IBufR  -> put $ st{iPtr = (iPtr st) + 1}
    Push   -> transfer (0, dPtr st) (0, iPtr st)
    Clone  -> clone    (0, dPtr st) (0, iPtr st)
    Pull   -> transfer (dPtr st, 0) (iPtr st, 0)
    Execute-> execute $ iPtr st
