------------------------------------------------------------------------------
--                                                                          --
--                         GNAT RUN-TIME COMPONENTS                         --
--                                                                          --
--                         A D A . R E A L _ T I M E                        --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--          Copyright (C) 1992-2015, Free Software Foundation, Inc.         --
--                                                                          --
-- This specification is derived from the Ada Reference Manual for use with --
-- GNAT. The copyright notice above, and the license provisions that follow --
-- apply solely to the  contents of the part following the private keyword. --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

package Ada_Real_Time with
  SPARK_Mode,
  Abstract_State => (Clock_Time with External => (Async_Readers,
                                                  Async_Writers))
is

   pragma Compile_Time_Error
     (Duration'Size /= 64,
      "this version of Ada.Real_Time requires 64-bit Duration");

   type Duration_Rep is range -(2 ** 63) .. +((2 ** 63 - 1)) with Ghost;
   for Duration_Rep'Size use Duration'Size;

   type Time is private;
   Time_First : constant Time;
   Time_Last  : constant Time;
   Time_Unit  : constant := 10#1.0#E-9;

   type Time_Span is private;
   Time_Span_First : constant Time_Span;
   Time_Span_Last  : constant Time_Span;
   Time_Span_Zero  : constant Time_Span;
   Time_Span_Unit  : constant Time_Span;

   function "+"  (Left : Time;      Right : Time_Span) return Time with
     Global => null,
     Pre => (if Right < Time_Span_Zero then
               To_Duration (Left) >=
                 To_Duration (Time_Span_First) - To_Duration (Right)
             elsif Right > Time_Span_Zero then
               To_Duration (Left) <=
                 To_Duration (Time_Span_Last) - To_Duration (Right));

   function "+"  (Left : Time_Span; Right : Time)      return Time with
     Global => null,
     Pre => (if Left < Time_Span_Zero then
               To_Duration (Right) >=
                 To_Duration (Time_Span_First) - To_Duration (Left)
             elsif Left > Time_Span_Zero then
               To_Duration (Right) <=
                 To_Duration (Time_Span_Last) - To_Duration (Left));

   function "-"  (Left : Time;      Right : Time_Span) return Time with
     Global => null,
     Pre => (if Right < Time_Span_Zero then
               To_Duration (Left) <=
                 To_Duration (Time_Span_Last) + To_Duration (Right)
             elsif Right > Time_Span_Zero then
               To_Duration (Left) >=
                 To_Duration (Time_Span_First) + To_Duration (Right));

   function "-"  (Left : Time;      Right : Time)      return Time_Span with
     Global => null,
     Pre => (if To_Duration (Right) < 0.0 then
               To_Duration (Left) <=
                 Duration'Last + To_Duration (Right)
             elsif To_Duration (Right) > 0.0 then
               To_Duration (Left) >=
                 Duration'First + To_Duration (Right));

   function "<"  (Left, Right : Time) return Boolean with
     Global => null;
   function "<=" (Left, Right : Time) return Boolean with
     Global => null;
   function ">"  (Left, Right : Time) return Boolean with
     Global => null;
   function ">=" (Left, Right : Time) return Boolean with
     Global => null;

   function "+"  (Left, Right : Time_Span)             return Time_Span with
     Global => null,
     Pre => (if Right < Time_Span_Zero then
               To_Duration (Left) >=
                 To_Duration (Time_Span_First) - To_Duration (Right)
             elsif Right > Time_Span_Zero then
               To_Duration (Left) <=
                 To_Duration (Time_Span_Last) - To_Duration (Right));

   function "-"  (Left, Right : Time_Span)             return Time_Span with
     Global => null,
     Pre => (if Right < Time_Span_Zero then
               To_Duration (Left) <=
                 To_Duration (Time_Span_Last) + To_Duration (Right)
             elsif Right > Time_Span_Zero then
               To_Duration (Left) >=
                 To_Duration (Time_Span_First) + To_Duration (Right));

   function "-"  (Right : Time_Span)                   return Time_Span with
     Global => null,
     Pre => Right /= Time_Span_First;

   function "*"  (Left : Time_Span; Right : Integer)   return Time_Span with
     Global => null,
     Pre =>
       (if Right > 0 then
         (if Left > Time_Span_Zero then
            Duration_Rep (To_Duration (Left) / Duration (Duration'Small)) <=
              Duration_Rep (To_Duration (Time_Span_Last) /
                            Duration (Duration'Small)) /
              Duration_Rep (Right)
          elsif Left < Time_Span_Zero then
            Duration_Rep (To_Duration (Left) / Duration (Duration'Small)) >=
              Duration_Rep (To_Duration (Time_Span_First) /
                            Duration (Duration'Small)) /
              Duration_Rep (Right))
        elsif Right < 0 then
         (if Left > Time_Span_Zero then
            (if Right = -1 then
               -Left >= Time_Span_First
             else
                Duration_Rep (To_Duration (Left) / Duration (Duration'Small)) <=
                Duration_Rep (To_Duration (Time_Span_First) /
                              Duration (Duration'Small)) /
                Duration_Rep (Right))
          elsif Left < Time_Span_Zero then
            Duration_Rep (To_Duration (Left) / Duration (Duration'Small)) >=
              Duration_Rep (To_Duration (Time_Span_Last) /
                            Duration (Duration'Small)) /
              Duration_Rep (Right)));

   function "*"  (Left : Integer;   Right : Time_Span) return Time_Span with
     Global => null,
     Pre =>
       (if Left > 0 then
         (if Right > Time_Span_Zero then
            Duration_Rep (To_Duration (Right) / Duration (Duration'Small)) <=
              Duration_Rep (To_Duration (Time_Span_Last) /
                            Duration (Duration'Small)) /
              Duration_Rep (Left)
          elsif Right < Time_Span_Zero then
            Duration_Rep (To_Duration (Right) / Duration (Duration'Small)) >=
              Duration_Rep (To_Duration (Time_Span_First) /
                            Duration (Duration'Small)) /
              Duration_Rep (Left))
        elsif Left < 0 then
         (if Right > Time_Span_Zero then
            (if Left = -1 then
               -Right >= Time_Span_First
             else
                Duration_Rep (To_Duration (Right)) <=
                Duration_Rep (To_Duration (Time_Span_First) /
                              Duration (Duration'Small)) /
                Duration_Rep (Left))
          elsif Right < Time_Span_Zero then
            Duration_Rep (To_Duration (Right) / Duration (Duration'Small)) >=
              Duration_Rep (To_Duration (Time_Span_Last) /
                            Duration (Duration'Small)) /
              Duration_Rep (Left)));

   function "/"  (Left, Right : Time_Span)             return Integer with
     Global => null,
     Pre => Right /= Time_Span_Zero and then
            (if Right = -Time_Span_Unit and then Left = Time_Span_First
             then --  avoid an obvious overflow
                False
             else --  Integer'Range fits into Duration_Rep'Range
                Duration_Rep (To_Duration (Left) / To_Duration (Right)) in
                Duration_Rep (Integer'First) .. Duration_Rep (Integer'Last));

   function "/"  (Left : Time_Span; Right : Integer)   return Time_Span with
     Global => null,
     Pre => Right /= 0 and then
            (if Right = -1 then Left /= Time_Span_First);

   function "abs" (Right : Time_Span) return Time_Span with
     Global => null,
     Pre => Right /= Time_Span_First;

   function "<"  (Left, Right : Time_Span) return Boolean with
     Global => null;
   function "<=" (Left, Right : Time_Span) return Boolean with
     Global => null;
   function ">"  (Left, Right : Time_Span) return Boolean with
     Global => null;
   function ">=" (Left, Right : Time_Span) return Boolean with
     Global => null;

   function To_Duration  (T : Time)       return Duration with Ghost;

   function To_Duration  (TS : Time_Span) return Duration with
     Global => null;
   function To_Time_Span (D : Duration)   return Time_Span with
     Global => null;

   function Nanoseconds  (NS : Integer) return Time_Span with
     Global => null;

   function Microseconds (US : Integer) return Time_Span with
     Global => null;

   function Milliseconds (MS : Integer) return Time_Span with
     Global => null;

   function Seconds (S : Integer) return Time_Span with
     Global => null;
   pragma Ada_05 (Seconds);

   function Minutes (M : Integer) return Time_Span with
     Global => null,
     Pre => Duration_Rep (M) in Duration_Rep'First / (1_000_000_000 * 60) ..
                                Duration_Rep'Last / (1_000_000_000 * 60);
   pragma Ada_05 (Minutes);

   type Seconds_Count is new Long_Long_Integer;
   --  Seconds_Count needs 64 bits, since the type Time has the full range of
   --  Duration. The delta of Duration is 10 ** (-9), so the maximum number of
   --  seconds is 2**63/10**9 = 8*10**9 which does not quite fit in 32 bits.
   --  However, rather than make this explicitly 64-bits we derive from
   --  Long_Long_Integer. In normal usage this will have the same effect. But
   --  in the case of CodePeer with a target configuration file with a maximum
   --  integer size of 32, it allows analysis of this unit.

   procedure Split (T : Time; SC : out Seconds_Count; TS : out Time_Span) with
     Global => null;

   --  Helper functions and constants
   function TS_SC (TS : Time_Span) return Seconds_Count is
      (Seconds_Count (To_Duration (TS))) with Ghost;

   function TS_Fraction (TS : Time_Span) return Duration is
      (To_Duration (TS) - Duration (TS_SC (TS))) with Ghost;

   function Result_SC (SC : Seconds_Count; TS : Time_Span)
      return Seconds_Count is (SC + TS_SC (TS)) with Ghost;

   SC_Lo : constant Seconds_Count with Ghost;
   SC_Hi : constant Seconds_Count with Ghost;
   Fudge : constant Seconds_Count with Ghost;
   FudgeD : constant Duration with Ghost;

   function Time_Of (SC : Seconds_Count; TS : Time_Span) return Time with
     Global => null,
     Pre => SC in 3 * SC_Lo .. 3 * SC_Hi and then
            Result_SC (SC, TS) in SC_Lo - 1 .. SC_Hi + 1 and then
            (if Result_SC (SC, TS) > 0 then
               Duration (Result_SC (SC, TS) - Fudge) + TS_Fraction (TS) <=
               Duration'Last - FudgeD
             else
               Duration (Result_SC (SC, TS) + Fudge) + TS_Fraction (TS) >=
               Duration'First + FudgeD);

private
   pragma SPARK_Mode (Off);
   --  Time and Time_Span are represented in 64-bit Duration value in
   --  nanoseconds. For example, 1 second and 1 nanosecond is represented
   --  as the stored integer 1_000_000_001. This is for the 64-bit Duration
   --  case, not clear if this also is used for 32-bit Duration values.

   type Time is new Duration;

   Time_First : constant Time := Time'First;

   Time_Last  : constant Time := Time'Last;

   -----------------
   -- To_Duration --
   -----------------

   function To_Duration (T : Time) return Duration is (Duration (T));

   type Time_Span is new Duration;

   Time_Span_First : constant Time_Span := Time_Span'First;

   Time_Span_Last  : constant Time_Span := Time_Span'Last;

   Time_Span_Zero  : constant Time_Span := 0.0;

   Time_Span_Unit  : constant Time_Span := 10#1.0#E-9;

   pragma Compile_Time_Error
     (Duration (Time_Span_First) /=
      -Duration (Time_Span_Last) - Duration'Small,
      "preconditions assume that Duration'Range is symmetric" &
      " except for an extra negative value");

   --  Ghost type cannot appear in Compile_Time_Error expressions
   Duration_Rep_Last : constant := Duration_Rep'Last;

   --  Conversion from Integer value of Minutes to Time_Span needs a
   --  precondition; make sure that other conversions are always safe.
   pragma Compile_Time_Error
     (Integer'Last * 1_000_000_000 > Duration_Rep_Last,
      "at least Seconds to Time_Span conversion needs a precondition");

   --  Helper constant values for Time_Of; see the package body for details
   SC_Lo : constant Seconds_Count :=
             Seconds_Count (Duration'First + Duration'(0.5));

   SC_Hi : constant Seconds_Count :=
             Seconds_Count (Duration'Last  - Duration'(0.5));

   Fudge : constant Seconds_Count := 10;

   FudgeD : constant Duration := Duration (Fudge);

   pragma Import (Intrinsic, "<");
   pragma Import (Intrinsic, "<=");
   pragma Import (Intrinsic, ">");
   pragma Import (Intrinsic, ">=");
   pragma Import (Intrinsic, "abs");

   pragma Inline (Microseconds);
   pragma Inline (Milliseconds);
   pragma Inline (Nanoseconds);
   pragma Inline (Seconds);
   pragma Inline (Minutes);

end Ada_Real_Time;
