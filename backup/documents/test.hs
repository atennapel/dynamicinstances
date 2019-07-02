import Control.Monad.ST
import Data.STRef
import Control.Monad
{-
function f(list) {
  var max = 0;
  for(var i = 0; i < list.length; i++) {
    var cur = list[i];
    if(cur > max) {
      max = cur;
    } else {
      list[i] = max;
    }
  }
  return list;
}
-}
{-
f :: [Int] -> ST s [Int]
f l = do
  max <- newSTRef 0
  newl <- mapM newSTRef l
  f' max newl 0
    where
      f' max newl i = do
        if i >= (length newl) then
          mapM readSTRef newl
        else do
          cmax <- readSTRef max
          let cur = l !! i
          if cur > cmax then
            writeSTRef max cur
          else
            writeSTRef (newl !! i) cmax
          f' max newl (i + 1)
-}


g = runST $ newSTRef 10


--main = putStrLn $ show $ g
