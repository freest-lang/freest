module SharedChannelSemi where

-- Channel-conditional CK-Seq, inference path: `*!Int` is a shared channel
-- (`*C`), so `*!Int ; a` is unrestricted regardless of the continuation `a`.
-- Discarding the parameter only type-checks if that result is inferred
-- unrestricted (the deferred `;` must apply the channel-conditional, not the
-- plain join, which would make it linear).
dropShared : forall a -> (*!Int ; a) -> ()
dropShared @a c = ()

main : ()
main = ()
