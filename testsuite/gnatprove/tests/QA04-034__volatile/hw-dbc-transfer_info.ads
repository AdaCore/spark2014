--
-- Copyright (C) 2016-2017 secunet Security Networks AG
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

private package HW.DbC.Transfer_Info
with
   Abstract_State => (State with Part_Of  => HW.DbC.State)
is

   procedure Start
     (Endpoint : in     Endpoint_Range;
      Length   : in     Natural;
      Id       :    out Transfer_Id;
      Success  :    out Boolean);

   procedure Restart
     (Id       : Transfer_Id;
      Length   : Natural);

   procedure Append
     (Endpoint : in     Endpoint_Range;
      Length   : in out Natural;
      Offset   :    out Natural;
      Id       :    out Transfer_Id);

   procedure Finish
     (DMA_Physical      : Word64;
      Remaining_Length  : Natural;
      Status            : Error);

   procedure Reset (Id : Transfer_Id);

   ----------------------------------------------------------------------------

   procedure Walk_Started
     (Minimum_Ctr : in out Word64;
      Id          :    out Transfer_Id;
      Success     :    out Boolean);

   procedure Walk_Finished
     (Endpoint    : in     Endpoint_Range;
      Minimum_Ctr : in out Word64;
      Id          :    out Transfer_Id;
      Success     :    out Boolean);

   ----------------------------------------------------------------------------

   function Get_Endpoint (Id : Transfer_Id) return Endpoint_Range;

   function Get_Offset (Id : Transfer_Id) return Natural;

   procedure Set_Offset (Id : Transfer_Id; Offset : Natural);

   function Get_Length (Id : Transfer_Id) return Natural;

   function Get_Status (Id : Transfer_Id) return Error;

   function Physical (Id : Transfer_Id) return Word64;

   ----------------------------------------------------------------------------

   procedure Dump_Stats;

end HW.DbC.Transfer_Info;

--  vim: set ts=8 sts=3 sw=3 et:
