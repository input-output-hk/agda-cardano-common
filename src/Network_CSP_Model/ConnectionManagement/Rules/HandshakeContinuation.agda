{-# OPTIONS --guardedness #-}

-- Network 2f1c154: Protocol/Handshake.hs tryHandshake (82–95), Handler.hs
-- 392–405,474–488,514–518. A timeout is an observed ProtocolLimitFailure
-- returned by the restored helper, not an empty promise or STM race. The
-- actual driver time limit/expiry is a supplied scoped observation; no clock
-- arithmetic, deadlines or fairness are asserted. Query delay runs masked
-- interruptibly; cancelDelay/cancelTrace require observed blocking delivery.
-- A bearer SDU read timeout is a thrown MuxError: the outer catch publishes
-- HandlerError and rethrows, unlike the helper ProtocolLimitFailure return.
module ConnectionManagement.Rules.HandshakeContinuation where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import ConnectionManagement.Domain using (ErrorId)
import ConnectionManagement.State as S

-- Protocol time/size limits are caught by the pinned tryHandshake helper. Their concrete
-- byte/deadline bounds and the observed driver failure are scoped inputs.
data LimitKind : Set where
  deadline sizeBound : LimitKind
data Result : Set where
  protocolLimit : LimitKind → ErrorId → Result
  bearerTimeout : ErrorId → Result
  query : Result
asResult : Result → S.HandshakeResult
asResult (protocolLimit kind err) = S.handlerError S.protocolViolation err
asResult (bearerTimeout err) = S.handlerError S.protocolViolation err
asResult query = S.query

data Body : Set where
  normal : Body
  sync async : ErrorId → Body

data PC : Set where
  returned published : Result → PC
  sleeping : PC
  exited : Result → Body → PC

-- Once published, the original result remains observable during delay/unwind.
publication : PC → Maybe Result
publication (returned _) = nothing
publication (published result) = just result
publication sleeping = just query
publication (exited result _) = just result

data Action : Set where
  publish traceReturned delayElapsed rethrowError : Action
  cancelDelay traceFailed cancelTrace : ErrorId → Action

-- A supplied blocking observation identifies the masked interruptible site.
data Window : Set where
  delayBlocked traceBlocked : Window
cancellation : Window → ErrorId → Action
cancellation delayBlocked err = cancelDelay err
cancellation traceBlocked err = cancelTrace err

data Event : Set where
  limitReturned : LimitKind → ErrorId → Event
  bearerTimedOut : ErrorId → Event
  queryReturned : Event
  continue : Action → Event

-- The optional result is written by the real Machine publication dispatcher;
-- local PC changes cannot fabricate that write or a physical Async result.
step : Action → PC → Maybe (PC × Maybe Result)
step publish (returned result) = just (published result , just result)
step traceReturned (published result@(protocolLimit _ _)) = just (exited result normal , nothing)
step traceReturned (published query) = just (sleeping , nothing)
step rethrowError (published result@(bearerTimeout err)) = just (exited result (sync err) , nothing)
step delayElapsed sleeping = just (exited query normal , nothing)
step (cancelDelay err) sleeping = just (exited query (async err) , nothing)
step (traceFailed err) (published result@(protocolLimit _ _)) = just (exited result (sync err) , nothing)
step (traceFailed err) (published query) = just (exited query (sync err) , nothing)
step (cancelTrace err) (published result@(protocolLimit _ _)) = just (exited result (async err) , nothing)
step (cancelTrace err) (published query) = just (exited query (async err) , nothing)
step _ _ = nothing
