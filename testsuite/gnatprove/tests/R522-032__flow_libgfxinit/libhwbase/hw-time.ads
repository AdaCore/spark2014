--
-- Copyright (C) 2015-2016 secunet Security Networks AG
--
-- This program is free software; you can redistribute it and/or modify
-- it under the terms of the GNU General Public License as published by
-- the Free Software Foundation; either version 2 of the License, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.
--

package HW.Time
   with Abstract_State => (State with External => Async_Writers)
is

   type T is private;

   function Now return T
   with
      Volatile_Function,
      Global => (Input => State);

   function US_From_Now (US : Natural) return T
   with
      Volatile_Function,
      Global => (Input => State);

   function MS_From_Now (MS : Natural) return T
   with
      Volatile_Function,
      Global => (Input => State);

   function Now_US return Int64
   with
      Volatile_Function,
      Global => (Input => State);

   ----------------------------------------------------------------------------

   pragma Warnings
     (GNATprove, Off, "subprogram ""*Delay*"" has no effect",
      Reason => "No effect on dataflow but time always passes.");

   -- Delay execution until Deadline has been reached.
   procedure Delay_Until (Deadline : T)
   with
      Global => (Input => State);

   procedure U_Delay (US : Natural)
   with
      Global => (Input => State);

   procedure M_Delay (MS : Natural)
   with
      Global => (Input => State);

   pragma Warnings
     (GNATprove, On, "subprogram ""*Delay*"" has no effect");

   ----------------------------------------------------------------------------

   function Timed_Out (Deadline : T) return Boolean
   with
      Volatile_Function,
      Global => (Input => State);

private

   type T is new Word64;

end HW.Time;

--  vim: set ts=8 sts=3 sw=3 et:
