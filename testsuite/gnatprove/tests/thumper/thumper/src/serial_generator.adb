---------------------------------------------------------------------------
-- FILE    : serial_generator.adb
-- SUBJECT : Body of a package to abstract the serial number generator.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package body Serial_Generator
  with Refined_State => (State => Current)
is

   -- See: http://nuclear.llnl.gov/CNP/rng/rngman/node4.html
   -- This generator has the maximal period.
   A : constant Serial_Number_Type := 2_862_933_555_777_941_757;
   B : constant Serial_Number_Type := 3_037_000_493;

   Current : Serial_Number_Type;

   procedure Next(Number : out Serial_Number_Type)
     with
        Refined_Global => (In_Out => Current),
        Refined_Depends => ((Current, Number) => Current)
   is
   begin
      Current := A * Current + B;
      Number  := Current;
   end Next;

begin
   declare
      use Ada.Calendar;
      Year    : Year_Number;
      Month   : Month_Number;
      Day     : Day_Number;
      Seconds : Day_Duration;
      Now     : constant Time := Clock;
   begin
      -- Split does read a global timezone info. However, it's not worth modeling fully here.
      pragma Warnings(Off, "no Global contract available for ""Split""");

      Split(Now, Year, Month, Day, Seconds);
      -- Store the date/time into a 64 bit value. The precise layout is not important.
      Current :=
        Serial_Number_Type(Year - Year_Number'First) * 2**54 +  -- 9 bits.
        Serial_Number_Type(  Month) * 2**50 +  -- 4 bits.
        Serial_Number_Type(    Day) * 2**45 +  -- 5 bits.
        Serial_Number_Type(Seconds);
   end;
end Serial_Generator;
