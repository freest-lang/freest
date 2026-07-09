-- Wildcard abstraction binders @_ / #_ consume a quantifier anonymously.

-- skip-then-name within a same-sort run (@_ skips a, @b names the second)
snd3 : forall a b -> a -> b -> b
snd3 @_ @b x y = y

-- multiplicity wildcard
appW : forall #m a b -> (a -m-> b) -> a -m-> b
appW #_ f x = f x

-- several wildcards in one equation never conflict
fst3 : forall a b -> a -> b -> a
fst3 @_ @_ x y = x

-- wildcard binder in a lambda
idLam : forall a -> a -> a
idLam = \@_ x -> x

-- kinded wildcard binder in a lambda
idKLam : forall a -> a -> a
idKLam = \@(_ : 1T) x -> x

main : ()
main =
  print ( snd3 1 2
        , appW (\x -> x + 1) 3
        , fst3 4 5
        , idLam 6
        , idKLam 7 )
