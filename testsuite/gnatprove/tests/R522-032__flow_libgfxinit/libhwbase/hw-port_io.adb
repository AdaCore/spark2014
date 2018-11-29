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

with System;
with System.Machine_Code;

package body HW.Port_IO
with
   Refined_State  => (State => null),
   SPARK_Mode     => Off
is

   generic
      type Word is private;
   procedure Port_In (Value : out Word; Port : Port_Type);

   procedure Port_In (Value : out Word; Port : Port_Type) is
   begin
      System.Machine_Code.Asm
        ("in %1, %0",
         Inputs   => (Port_Type'Asm_Input ("Nd", Port)),
         Outputs  => (Word'Asm_Output ("=a", Value)),
         Volatile => True);
   end Port_In;

   procedure InB_Body is new Port_In (Word => Word8);
   procedure InB (Value : out Word8; Port : Port_Type) renames InB_Body;

   procedure InW_Body is new Port_In (Word => Word16);
   procedure InW (Value : out Word16; Port : Port_Type) renames InW_Body;

   procedure InL_Body is new Port_In (Word => Word32);
   procedure InL (Value : out Word32; Port : Port_Type) renames InL_Body;

   ----------------------------------------------------------------------------

   generic
      type Word is private;
   procedure Port_Out (Port : Port_Type; Value : Word);

   procedure Port_Out (Port : Port_Type; Value : Word) is
   begin
      System.Machine_Code.Asm
        ("out %1, %0",
         Inputs   => (Port_Type'Asm_Input ("Nd", Port),
                      Word'Asm_Input ("a", Value)),
         Volatile => True);
   end Port_Out;

   procedure OutB_Body is new Port_Out (Word => Word8);
   procedure OutB (Port : Port_Type; Value : Word8) renames OutB_Body;

   procedure OutW_Body is new Port_Out (Word => Word16);
   procedure OutW (Port : Port_Type; Value : Word16) renames OutW_Body;

   procedure OutL_Body is new Port_Out (Word => Word32);
   procedure OutL (Port : Port_Type; Value : Word32) renames OutL_Body;

end HW.Port_IO;

--  vim: set ts=8 sts=3 sw=3 et:
