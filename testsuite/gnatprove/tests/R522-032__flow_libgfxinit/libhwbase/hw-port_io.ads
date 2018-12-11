--
-- Copyright (C) 2015 secunet Security Networks AG
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

package HW.Port_IO
with
   Abstract_State => (State with External => (Async_Readers, Async_Writers))
is

   type Port_Type is mod 2**16;

   procedure InB (Value : out Word8; Port : Port_Type)
   with
      Global   => (In_Out => State),
      Depends  => ((Value, State) => (Port, State)),
      Inline_Always;

   procedure InW (Value : out Word16; Port : Port_Type)
   with
      Global   => (In_Out => State),
      Depends  => ((Value, State) => (Port, State)),
      Pre      => Port mod 2 = 0,
      Inline_Always;

   procedure InL (Value : out Word32; Port : Port_Type)
   with
      Global   => (In_Out => State),
      Depends  => ((Value, State) => (Port, State)),
      Pre      => Port mod 4 = 0,
      Inline_Always;

   procedure OutB (Port : Port_Type; Value : Word8)
   with
      Global   => (In_Out => State),
      Depends  => (State =>+ (Port, Value)),
      Inline_Always;

   procedure OutW (Port : Port_Type; Value : Word16)
   with
      Global   => (In_Out => State),
      Depends  => (State =>+ (Port, Value)),
      Pre      => Port mod 2 = 0,
      Inline_Always;

   procedure OutL (Port : Port_Type; Value : Word32)
   with
      Global   => (In_Out => State),
      Depends  => (State =>+ (Port, Value)),
      Pre      => Port mod 4 = 0,
      Inline_Always;

end HW.Port_IO;
