-- `!type` channels are consumed by `sendType`, not by `receiveType`.
f : (!type a. (!a ; Close)) -> (exists (a : *T), (?a ; Wait))
f = receiveType
