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

private package HW.DbC.Transfer_Rings
with
   Abstract_State => ((State with Part_Of  => HW.DbC.State),
                      (DMA   with Part_Of  => HW.DbC.DMA,
                                  External => (Async_Readers, Async_Writers)))
is

   function Physical (EP : Endpoint_Range) return Word64;

   function Full (EP : Endpoint_Range) return Boolean;

   function Last_Started (EP : Endpoint_Range) return Boolean;

   ----------------------------------------------------------------------------

   procedure Toggle_CS (EP : Endpoint_Range);

   ----------------------------------------------------------------------------

   procedure Initialize (EP : Endpoint_Range);

   ----------------------------------------------------------------------------

   procedure Dequeue
     (EP                : Endpoint_Range;
      Pointer           : Word64;
      Status            : Error;
      Remaining_Length  : Natural);

   ----------------------------------------------------------------------------

   use type Word64;
   procedure Enqueue_Data_TRB
     (EP                : Endpoint_Range;
      Data_Length       : Natural;
      Data_Buf          : Word64;
      Toggle_CS         : Boolean)
   with
      Pre =>
         Data_Length <= 2 ** 16 and
         Data_Buf / 2 ** 16 =
           (Data_Buf + Word64 (Data_Length) - 1) / 2 ** 16 and
         Data_Buf + Word64 (Data_Length) - 1 <= Word64'Last;

   procedure Requeue_Data_TRB
     (EP       : Endpoint_Range;
      Length   : Natural;
      Buf_Addr : Word64)
   with
      Pre =>
         Length <= 2 ** 16 and
         Buf_Addr / 2 ** 16 =
           (Buf_Addr + Word64 (Length) - 1) / 2 ** 16 and
         Buf_Addr + Word64 (Length) - 1 <= Word64'Last;

end HW.DbC.Transfer_Rings;

--  vim: set ts=8 sts=3 sw=3 et:
