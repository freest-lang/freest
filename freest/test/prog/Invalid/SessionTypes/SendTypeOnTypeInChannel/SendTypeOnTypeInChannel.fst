-- `?type` channels are consumed by `receiveType`, not by `sendType`.
f : (?type a. (?a ; Wait)) -> (?Int ; Wait)
f = sendType @Int
