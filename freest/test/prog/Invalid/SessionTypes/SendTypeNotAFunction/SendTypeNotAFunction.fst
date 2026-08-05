-- A bare `sendType` is a function; its type cannot be the channel alone.
f : !type a. (!a ; Close)
f = sendType @Int
