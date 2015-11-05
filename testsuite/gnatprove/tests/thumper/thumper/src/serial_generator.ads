---------------------------------------------------------------------------
-- FILE    : serial_generator.ads
-- SUBJECT : Specification of a package to abstract the serial number generator.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Serial numbers are required to be unique over the lifetime of the system's deployment.
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);
with Ada.Calendar;
pragma Elaborate_All (Ada.Calendar);

package Serial_Generator
  with
     Abstract_State => State,
     Initializes => (State => Ada.Calendar.Clock_Time)
is
   type Serial_Number_Type is mod 2**64;

   -- Computes the next serial number and updates the internal state to prepare for a following
   -- call to Next. This procedure can't fail. However, the numbers it generates cycle with a
   -- period of 2**64.
   --
   procedure Next(Number : out Serial_Number_Type)
     with
        Global => (In_Out => State),
        Depends => ((State, Number) => State);

end Serial_Generator;
