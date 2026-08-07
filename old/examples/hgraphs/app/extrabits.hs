
getPassphrase :: MaybeT IO String
getPassphrase = do 
    s <- lift getLine
    guard (isValid s)
    return s

isValid :: String -> Bool
isValid s = length s >= 8
    &&  any isAlpha s
    && any isNumber s
    && any isPunctuation s

askPassphrase :: MaybeT IO ()
askPassphrase = do
    lift $ putStrLn "Insert passphrase:"
    val <- msum $ repeat getPassphrase
    lift $ putStrLn "Storing pw"

-- Transformer bit
newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }
newtype IdentityT f a = IdentityT { runIdentityT :: f a }


instance Monad m => Functor (IdentityT m) where
    fmap = liftM
instance Monad a => Applicative (IdentityT a) where 
    pure x = IdentityT (pure x)
    (<*>) = ap
instance Monad m => Monad (IdentityT m) where
    return = IdentityT . return
    x >>= f = IdentityT $ runIdentityT . f =<< runIdentityT x
instance MonadTrans IdentityT where
    lift = IdentityT 
instance Monad m => Monad (MaybeT m) where
    return = MaybeT . return . Just
    x >>= f = MaybeT $ do maybe_value <- runMaybeT x
                          case maybe_value of 
                            Nothing -> return Nothing
                            Just val -> runMaybeT $ f val

instance Monad m => Applicative (MaybeT m) where
    pure x = return x
    (<*>) = ap

instance Monad m => Functor (MaybeT m) where
    fmap = liftM

instance Monad m => Alternative (MaybeT m) where
    empty = MaybeT $ return Nothing
    x <|> y = MaybeT $ do maybe_value <- runMaybeT x
                          case maybe_value of 
                            Nothing -> runMaybeT y
                            Just _ -> return maybe_value

instance Monad m => MonadPlus (MaybeT m) where
    mzero = empty
    mplus = (<|>)

instance MonadTrans MaybeT where
    lift = MaybeT . liftM Just

-- StateT section
newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }

instance Functor m => Functor (StateT s m) where
    fmap f m = StateT $ \s ->
        (\ ~(a, s') -> (f a, s')) <$> runStateT m s

instance (Functor m, Monad m) => Applicative (StateT s m) where
    pure a = StateT $ \s -> return (a, s)
    StateT mf <*> StateT mx = StateT $ \s -> -- take the initial state s
        do
            ~(f, s') <- mf s -- wraps s as m (f: a -> b, s' : s)
            ~(x, s'') <- mx s' -- takes s', updates it after running mx action
            return (f x, s'') -- apply the bound f to the action x, return this, as well as updated state
instance Monad m => Monad (StateT s m) where
    return a = StateT $ \s -> return (a, s)
    (StateT x) >>= f = StateT $ \s -> do
        (v, s') <- x s
        runStateT (f v) s'