_ = print @(Maybe String) (lookupEnv "FREEST_NOT_SET_12345")
_ = print @Bool (length @(String, String) (getEnvironment ()) > 0)
