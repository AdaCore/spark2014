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

package Ada_Real_Time
  with SPARK_Mode => On
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

   function To_Duration (T : Time) return Duration with Ghost;

   function "+"  (Left : Time;      Right : Time_Span) return Time with
     Pre => (if Right < Time_Span_Zero then
               To_Duration (Left) >=
                 To_Duration (Time_Span_First) - To_Duration (Right)
             elsif Right > Time_Span_Zero then
               To_Duration (Left) <=
                 To_Duration (Time_Span_Last) - To_Duration (Right));

   function "+"  (Left : Time_Span; Right : Time)      return Time with
     Pre => (if Left < Time_Span_Zero then
               To_Duration (Right) >=
                 To_Duration (Time_Span_First) - To_Duration (Left)
             elsif Left > Time_Span_Zero then
               To_Duration (Right) <=
                 To_Duration (Time_Span_Last) - To_Duration (Left));

   function "-"  (Left : Time;      Right : Time_Span) return Time with
     Pre => (if Right < Time_Span_Zero then
               To_Duration (Left) <=
                 To_Duration (Time_Span_Last) + To_Duration (Right)
             elsif Right > Time_Span_Zero then
               To_Duration (Left) >=
                 To_Duration (Time_Span_First) + To_Duration (Right));

   function "-"  (Left : Time;      Right : Time)      return Time_Span with
     Pre => (if To_Duration (Right) < 0.0 then
               To_Duration (Left) <=
                 Duration'Last + To_Duration (Right)
             elsif To_Duration (Right) > 0.0 then
               To_Duration (Left) >=
                 Duration'First + To_Duration (Right));

   function "<"  (Left, Right : Time) return Boolean;
   function "<=" (Left, Right : Time) return Boolean;
   function ">"  (Left, Right : Time) return Boolean;
   function ">=" (Left, Right : Time) return Boolean;

   function "+"  (Left, Right : Time_Span)             return Time_Span with
     Pre => (if Right < Time_Span_Zero then
               To_Duration (Left) >=
                 To_Duration (Time_Span_First) - To_Duration (Right)
             elsif Right > Time_Span_Zero then
               To_Duration (Left) <=
                 To_Duration (Time_Span_Last) - To_Duration (Right));

   function "-"  (Left, Right : Time_Span)             return Time_Span with
     Pre => (if Right < Time_Span_Zero then
               To_Duration (Left) <=
                 To_Duration (Time_Span_Last) + To_Duration (Right)
             elsif Right > Time_Span_Zero then
               To_Duration (Left) >=
                 To_Duration (Time_Span_First) + To_Duration (Right));

   function "-"  (Right : Time_Span)                   return Time_Span with
     Pre => Right /= Time_Span_First;

   function "*"  (Left : Time_Span; Right : Integer)   return Time_Span with
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
              Duration_Rep (To_Duration (Time_Span_Last)) /
              Duration_Rep (Right)));

   function "*"  (Left : Integer;   Right : Time_Span) return Time_Span with
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
              Duration_Rep (To_Duration (Time_Span_Last)) /
              Duration_Rep (Left)));

   --  ??? Precondition for this one is tricky; see RM G.2.3 (16-18)

   function "/"  (Left, Right : Time_Span)             return Integer;

   function "/"  (Left : Time_Span; Right : Integer)   return Time_Span with
     Pre => Right /= 0 and then
            (if Right = -1 then Left /= Time_Span_First);

   function "abs" (Right : Time_Span) return Time_Span with
     Pre => Right /= Time_Span_First;

   function "<"  (Left, Right : Time_Span) return Boolean;
   function "<=" (Left, Right : Time_Span) return Boolean;
   function ">"  (Left, Right : Time_Span) return Boolean;
   function ">=" (Left, Right : Time_Span) return Boolean;

   function To_Duration  (TS : Time_Span) return Duration;
   function To_Time_Span (D : Duration)   return Time_Span;

   function Nanoseconds  (NS : Integer) return Time_Span;

   function Microseconds (US : Integer) return Time_Span;

   function Milliseconds (MS : Integer) return Time_Span;

   function Seconds (S : Integer) return Time_Span;
   pragma Ada_05 (Seconds);

   function Minutes (M : Integer) return Time_Span with
     Pre => Duration_Rep (M) <= Duration_Rep'Last / (1_000_000_000 * 60);
   pragma Ada_05 (Minutes);

   type Seconds_Count is new Long_Long_Integer;
   --  Seconds_Count needs 64 bits, since the type Time has the full range of
   --  Duration. The delta of Duration is 10 ** (-9), so the maximum number of
   --  seconds is 2**63/10**9 = 8*10**9 which does not quite fit in 32 bits.
   --  However, rather than make this explicitly 64-bits we derive from
   --  Long_Long_Integer. In normal usage this will have the same effect. But
   --  in the case of CodePeer with a target configuration file with a maximum
   --  integer size of 32, it allows analysis of this unit.

   --  ??? Preconditions for these will require some ghost functions

   procedure Split (T : Time; SC : out Seconds_Count; TS : out Time_Span);
   function Time_Of (SC : Seconds_Count; TS : Time_Span) return Time;

private
   pragma SPARK_Mode (Off);
   --  Time and Time_Span are represented in 64-bit Duration value in
   --  nanoseconds. For example, 1 second and 1 nanosecond is represented
   --  as the stored integer 1_000_000_001. This is for the 64-bit Duration
   --  case, not clear if this also is used for 32-bit Duration values.

   type Time is new Duration;

   Time_First : constant Time := Time'First;

   Time_Last  : constant Time := Time'Last;

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

   pragma Compile_Time_Error
     (Integer'Last * 1_000_000_000 > Duration_Rep_Last,
      "at least Seconds to Time_Span conversion needs a precondition");

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
