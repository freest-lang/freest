-- `sendType` consumes a `!type` channel, not a value-output channel.
f : !Int ; Close -> !Int ; Close
f = sendType @Int
