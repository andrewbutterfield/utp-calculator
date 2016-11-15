mapM_
  ( \h -> do { eold <- hGetEncoding
             ;case eold of
               { Nothing -> return ()
               ; Just e -> mkTextEncoding (show e ++ "//TRANSLIT")
                           >>= hSetEncoding h
               }
             }
  ) [stdout,stdin,stderr]
