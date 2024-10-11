/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.DateTime
import Std.Time.Zoned.TimeZone

namespace Std
namespace Time
namespace TimeZone
open Internal

set_option linter.all true

/--
Represents the type of local time in relation to UTC.
-/
inductive UTLocal
  /--
  Universal Time (UT), often referred to as UTC.
  -/
  | ut

  /--
  Local time that is not necessarily UTC.
  -/
  | local
  deriving Repr, Inhabited

/--
Represents types of wall clocks or standard times.
-/
inductive StdWall
  /--
  Time based on a wall clock, which can include daylight saving adjustments.
  -/
  | wall

  /--
  Standard time without adjustments for daylight saving.
  -/
  | standard
  deriving Repr, Inhabited

/--
Represents a type of local time, including offset and daylight saving information.
-/
structure LocalTimeType where

  /--
  The offset from GMT for this local time.
  -/
  gmtOffset : TimeZone.Offset

  /--
  Indicates if daylight saving time is observed.
  -/
  isDst : Bool

  /--
  The abbreviation for this local time type (e.g., "EST", "PDT").
  -/
  abbreviation : String

  /--
  Indicates if the time is wall clock or standard time.
  -/
  wall : StdWall

  /--
  Distinguishes between universal time and local time.
  -/
  utLocal : UTLocal

  /--
  ID of the timezone
  -/
  identifier : String
  deriving Repr, Inhabited

namespace LocalTimeType

/--
Gets the `TimeZone` offset from a `LocalTimeType`.
-/
def getTimeZone (time : LocalTimeType) : TimeZone :=
  ⟨time.gmtOffset, time.identifier, time.abbreviation, time.isDst⟩

end LocalTimeType

/--
Represents a time zone transition, mapping a time to a local time type.
-/
structure Transition where

  /--
  The specific time of the transition event.
  -/
  time : Second.Offset

  /--
  The local time type associated with this transition.
  -/
  localTimeType : LocalTimeType
  deriving Repr, Inhabited

/--
Represents the rules for a time zone, abstracting away binary data and focusing on key transitions
and types.
-/
structure ZoneRules where

  /--
  The array of local time types for the time zone.
  -/
  localTimes : Array LocalTimeType

  /--
  The array of transitions for the time zone.
  -/
  transitions : Array Transition

  deriving Repr, Inhabited

namespace Transition

/--
Create a TimeZone from a Transition.
-/
def createTimeZoneFromTransition (transition : Transition) : TimeZone :=
  let name := transition.localTimeType.identifier
  let offset := transition.localTimeType.gmtOffset
  let abbreviation := transition.localTimeType.abbreviation
  TimeZone.mk offset name abbreviation transition.localTimeType.isDst

/--
Applies the transition to a Timestamp.
-/
def apply (timestamp : Timestamp) (transition : Transition) : Timestamp :=
  let offsetInSeconds := transition.localTimeType.gmtOffset.hour.mul 3600 |>.add transition.localTimeType.gmtOffset.second
  timestamp.addSeconds offsetInSeconds

end Transition

namespace ZoneRules

/--
Finds the transition corresponding to a given timestamp in `ZoneRules`.
If the timestamp falls between two transitions, it returns the most recent transition before the timestamp.
-/
def findTransitionForTimestamp (zoneRules : ZoneRules) (timestamp : Timestamp) : Option Transition :=
  let value := timestamp.toSecondsSinceUnixEpoch
  if let some idx := zoneRules.transitions.findIdx? (fun t => t.time.val > value.val)
    then zoneRules.transitions.get? (idx - 1)
    else zoneRules.transitions.back?

/--
Find the current `TimeZone` out of a `Transition` in a `ZoneRules`
-/
def timezoneAt (rules : ZoneRules) (tm : Timestamp) : Except String TimeZone :=
  if let some transition := rules.findTransitionForTimestamp tm
    then .ok transition.createTimeZoneFromTransition
    else .error "cannot find local timezone."
