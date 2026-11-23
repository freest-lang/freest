# Leftover messages and program termination: related work

This note looks at what other languages and libraries do in two
situations:

- how a multithreaded program terminates: whether the end of `main` kills the
  other threads, or the program runs until every thread has finished;
- what happens to messages that are still buffered when the program ends, and
  whether anything reports them.

**Caveat.** This survey was written from memory, not from the documentation.
Check the exact message texts, configuration names and defaults against the
current docs before citing them. The Occam/CML row is the least certain.

## Summary

No mainstream language reports messages left in channel buffers when a
program ends normally. They are dropped without a word, and the only standard
runtime diagnostic is for deadlock. The closest precedents are:

- actor runtimes, where a message to a stopped actor counts as a lost
  delivery (Akka/Pekko dead letters);
- reports printed only when a process crashes (Erlang);
- a callback the programmer can use for undelivered elements (Kotlin);
- test-time leak detectors (`goleak`).

## By language

Many runtimes support both termination policies. Each cell names the default
first and then the exceptions.

| Language / library | Termination of multithreaded programs | What happens to unread buffered messages at exit | Any diagnostic? |
|---|---|---|---|
| **Haskell**: `Chan`, `TChan`/`TQueue`, `MVar` | **Main kills all.** When `main` returns, the process exits and the other threads get no exception and no chance to clean up. To wait, you have to do it yourself (`MVar` handshakes, `async`'s `wait`, `withAsync`). | The other threads are killed and buffers are garbage-collected. | None. The runtime only raises `BlockedIndefinitelyOnMVar`/`OnSTM` for a thread that can never wake up. That is deadlock detection, not a buffer check. Cloud Haskell also drops messages sent to dead processes silently. |
| **OCaml**: `Event` (synchronous, CML-style), Domainslib `Chan`, Eio `Stream` | **Main kills all** for `Thread` and for OCaml 5 domains. Eio is the exception: it **waits**, because `Eio_main.run` and `Switch.run` return only after every fiber in the switch has finished. | `Event` channels have no buffer. Domainslib/Eio buffers are dropped. | None. Eio's `Switch` makes sure child fibers finish, but it doesn't look inside streams. |
| **Rust**: `std::sync::mpsc`, crossbeam, tokio `mpsc` | **Main kills all.** Spawned `std::thread`s die when `main` returns unless they are `join`ed. Dropping a tokio runtime cancels its tasks at their next `.await`. The exception is `std::thread::scope`, which **waits** for every thread in the scope. | Dropping the `Receiver` drops the buffered messages and runs their destructors. | Nothing at exit. The closest thing is on the sending side: `send` returns `Err(SendError(msg))` once the receiver is gone, which gives the unsent value back. The `drop_bomb` crate pattern, which panics if a value is dropped without being used, is what session-type libraries rely on to catch unfinished protocols. |
| **Go**: buffered `chan` | **Main kills all.** Goroutines don't survive `main`, and the usual way to wait is `sync.WaitGroup`. | Goroutines end when `main` returns, and buffers are garbage-collected. | Only `fatal error: all goroutines are asleep - deadlock!`. `go vet` and staticcheck don't check this. Uber's `goleak` catches goroutines leaked in tests (often ones blocked on a channel), but not buffered values. |
| **Scala**: Akka / Pekko actors | **Waits**, in a sense. The dispatcher threads are non-daemon, so the JVM keeps running after `main` until something calls `system.terminate()` or the guardian actor stops. A forgotten `terminate()` gives a program that never ends. | Messages still in a stopped actor's mailbox, or sent to it later, go to **dead letters**. | **The closest precedent.** The log looks like: `Message [Foo] from Actor[..] to Actor[..] was not delivered. [n] dead letters encountered. If this is not an expected behavior then Actor[..] may have terminated unexpectedly. This logging can be turned off or adjusted with configuration settings 'akka.log-dead-letters' and 'akka.log-dead-letters-during-shutdown'.` It's a log line, not an error, and is rate-limited. During-shutdown logging is believed to be off by default since Akka 2.6, which means the end-of-program case is exactly the one hidden by default. |
| **Scala**: ZIO / Cats Effect `Queue`, Ox / Gears channels | **Main kills all** in ZIO and Cats Effect. When the main fiber finishes, ZIO interrupts its child fibers and Cats Effect's `IOApp` exits the process. Ox and Gears **wait**: a structured scope (`supervised`, `Async.blocking`) ends only when its forks have finished. Daemon forks are cancelled. | Dropped. | None. Ox channels have explicit `done`/`error` states, but leftover values are not reported. |
| **Erlang / Elixir** | **Neither.** A process ending never ends the node, which keeps running until `halt()` or `init:stop()`. In practice, scripts (`escript`, `mix run` without `--no-halt`) **halt the VM when the main function returns**, killing every other process. | A process's mailbox is thrown away when it exits, and sends to a dead pid are dropped silently. | **Only on abnormal exit:** the `proc_lib` crash report includes `message_queue_len` and `messages: [...]`, so a crash shows the pending mailbox. A `gen_server` crash also prints `** Last message in was ...`. Separately, Elixir's default `GenServer.handle_info/2` logs `... received unexpected message in handle_info/2: ...`. That is about messages nobody expected, not leftovers. A normal exit with a full mailbox says nothing. |
| **Kotlin**: coroutines `Channel` | **Waits** under structured concurrency, because `runBlocking` and `coroutineScope` return only after all their child coroutines finish. Coroutines launched in `GlobalScope` run on daemon threads and are **killed** when `main` ends. | `cancel()` drops the buffered elements. | No warning, but there is a **hook**: `Channel(onUndeliveredElement = { ... })` is called for each element that was sent but never delivered (cancellation, close with buffered items). It's meant for freeing resources, but can be used to log leftovers. |
| **Swift**: `AsyncStream` | **Main kills all** for unstructured `Task {}` and `Task.detached`. Task groups and `async let` **wait**: their scope doesn't end until the child tasks finish. | Buffered elements are dropped when the stream ends. | None, apart from an `onTermination` callback. |
| **C# / Java**: `System.Threading.Channels`, `BlockingQueue` | **Depends on the thread kind.** The process **waits** for foreground threads (C#) or non-daemon threads (Java) and **kills** background or daemon ones. C# `Task`s run on background thread-pool threads, so they are killed. Java `ExecutorService` threads are non-daemon, so an executor that is never `shutdown()` keeps the JVM alive. | Dropped. | None. |
| **Clojure**: `core.async` | **Mixed.** `go` blocks run on daemon threads, so they are **killed**. `future`s and agents use a non-daemon pool, so the JVM keeps running (about a minute, until the idle threads time out) unless `shutdown-agents` is called. | Dropped. | None. |
| **Pony** | **Waits**, in the strongest form. The program ends only at quiescence: every actor is idle *and* every mailbox is empty. `Main` has no special status. | Cannot happen. | Not needed. A non-empty mailbox keeps the program running, so leftovers can't exist, though a forgotten message can give a program that never ends. |
| **Occam / CSP, CML** | Occam **waits**: a `PAR` ends only when every branch has ended. In CML, `RunCML.doit` returns when `RunCML.shutdown` is called, or (unconfirmed) when no thread can make progress. | Channels are synchronous, so there are no buffers. | N/A. |

## Observations

- **Wherever main kills the other threads, leftover messages disappear
  without a trace** (Haskell, Go, Rust, ZIO/Cats Effect, scripts on the BEAM,
  Swift). The program never gets to the point where it could notice them.
- **Waiting runtimes don't report leftovers either.** Pony makes leftovers
  impossible, but a forgotten message gives a program that never ends.
  Structured scopes (Eio, Ox, Kotlin, Swift task groups, `thread::scope`) wait
  for threads to finish but never look inside channels.
- **Why the other languages don't report leftovers.** Nothing in them says a
  message *had* to be received, so reporting leftovers would mostly produce
  noise. That is why Akka lets the log be turned off and hides it during
  shutdown. FreeST can treat leftovers as a mistake because linearity says the
  receive was required. It also means FreeST can draw a line Akka cannot:
  report messages sent on a linear channel and ignore messages in transit on
  a shared channel. The `dev` branch has no leftover check yet.
- **Wording worth borrowing for FreeST's report.** Akka's "may have terminated
  unexpectedly" gives a likely cause. Erlang shows a count plus the actual
  messages. Akka names the setting that silences the message.
- **A related diagnostic FreeST doesn't have:** `goleak`-style reporting of
  threads still blocked on a channel when `main` returns. For a linear
  channel, that is the other side of the same bug.
