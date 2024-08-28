import Std.Time
open Std.Time

def date := date% 1970-01-20

/--
info: 1970-02-01
-/
#guard_msgs in
#eval date + (12 : Day.Offset)

/--
info: 1970-01-08
-/
#guard_msgs in
#eval date - (12 : Day.Offset)

def datetime := date% 2000-01-20:03:02:01

/--
info: 2000-01-20:04:02:01:000000000
-/
#guard_msgs in
#eval datetime + (1 : Hour.Offset)

/--
info: 2000-01-20:02:02:01:000000000
-/
#guard_msgs in
#eval datetime - (1 : Hour.Offset)

/--
info: 2000-01-20:03:12:01:000000000
-/
#guard_msgs in
#eval datetime + (10 : Minute.Offset)

/--
info: 2000-01-20:02:52:01:000000000
-/
#guard_msgs in
#eval datetime - (10 : Minute.Offset)

/--
info: 2000-01-20:03:03:01:000000000
-/
#guard_msgs in
#eval datetime + (60 : Second.Offset)

/--
info: 2000-01-20:03:01:01:000000000
-/
#guard_msgs in
#eval datetime - (60 : Second.Offset)

/--
info: 2000-01-21:03:02:01:000000000
-/
#guard_msgs in
#eval datetime + (1 : Day.Offset)

/--
info: 2000-01-19:03:02:01:000000000
-/
#guard_msgs in
#eval datetime - (1 : Day.Offset)

def time := time% 13:02:01

/--
info: 14:02:01:000000000
-/
#guard_msgs in
#eval time + (1 : Hour.Offset)

/--
info: 12:02:01:000000000
-/
#guard_msgs in
#eval time - (1 : Hour.Offset)

/--
info: 13:12:01:000000000
-/
#guard_msgs in
#eval time + (10 : Minute.Offset)

/--
info: 12:52:01:000000000
-/
#guard_msgs in
#eval time - (10 : Minute.Offset)

/--
info: 13:03:01:000000000
-/
#guard_msgs in
#eval time + (60 : Second.Offset)

/--
info: 13:01:01:000000000
-/
#guard_msgs in
#eval time - (60 : Second.Offset)

def datetimetz := date% 2000-01-20:03:02:01-03:00

/--
info: 2000-01-22:06:02:01:000000000-03:00
-/
#guard_msgs in
#eval datetimetz + (2 : Day.Offset)

/--
info: 2000-01-19:06:02:01:000000000-03:00
-/
#guard_msgs in
#eval datetimetz - (1 : Day.Offset)

/--
info: 2000-01-20:07:02:01:000000000-03:00
-/
#guard_msgs in
#eval datetimetz + (1 : Hour.Offset)

/--
info: 2000-01-20:05:02:01:000000000-03:00
-/
#guard_msgs in
#eval datetimetz - (1 : Hour.Offset)

/--
info: 2000-01-20:06:12:01:000000000-03:00
-/
#guard_msgs in
#eval datetimetz + (10 : Minute.Offset)

/--
info: 2000-01-20:05:52:01:000000000-03:00
-/
#guard_msgs in
#eval datetimetz - (10 : Minute.Offset)

/--
info: 2000-01-20:06:03:01:000000000-03:00
-/
#guard_msgs in
#eval datetimetz + (60 : Second.Offset)

/--
info: 2000-01-20:06:01:01:000000000-03:00
-/
#guard_msgs in
#eval datetimetz - (60 : Second.Offset)

/--
info: "3600s"
-/
#guard_msgs in
#eval (date% 2000-12-20:00:0:00-03:00) - (date% 2000-12-20:00:00:00-02:00)

def now := PlainDateTime.ofUTCTimestamp ⟨1724859638, ⟨907328169, by decide⟩, by decide⟩
def after := PlainDateTime.ofUTCTimestamp ⟨1724859639, ⟨907641224, by decide⟩, by decide⟩
def duration := after.since now

/--
info: "03:40:38.907328169"
-/
#guard_msgs in
#eval now.format "HH:mm:ss.sssssssss"

/--
info: "03.40:39.907641224"
-/
#guard_msgs in
#eval after.format "HH.mm:ss.sssssssss"

/--
info: "1.000313055s"
-/
#guard_msgs in
#eval duration
