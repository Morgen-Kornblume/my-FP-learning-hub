import Prelude

it :: IO(Maybe Bool) 
it = do
    a <- readLn
    b <- readLn
    return $ return $ a&&b