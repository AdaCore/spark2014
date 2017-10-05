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

with System;
with System.Storage_Elements;

with HW.Debug;
with HW.DbC.DMA_Buffers;
with HW.DbC.Transfer_Info;
with HW.DbC.TRBs;

package body HW.DbC.Transfer_Rings
with
   Refined_State =>
     (State => (PCS, Pointers),
      DMA   => (Rings))
is

   type Transfer_Ring_Array is array (Endpoint_Range) of TRBs.Transfer_Ring
   with
      Pack;
   Rings : Transfer_Ring_Array
   with
      Volatile,
      Async_Readers,
      Async_Writers,
      Address => System'To_Address (DMA_Buffers.Transfer_Rings_Base);

   type PCS_Array is array (Endpoint_Range) of Bit;
   PCS : PCS_Array;

   type Transfer_Pointers is record
      Enqueue  : TRBs.Ring_Range;
      Dequeue  : TRBs.Ring_Range;
      Full     : Boolean;
      Toggle   : TRBs.Ring_Range;
      Overrun  : Boolean;
   end record;
   type Transfer_Pointers_Array is array (Endpoint_Range) of Transfer_Pointers;
   Pointers : Transfer_Pointers_Array;

   --  Returns the physical address of the transfer ring specified by given EP.
   function Get_Ring_Address (EP : Endpoint_Range) return Word64;

   ----------------------------------------------------------------------------

   function Physical (EP : Endpoint_Range) return Word64
   is
   begin
      return
         DMA_Buffers.Transfer_Rings_Base + (Word64 (EP) - 2) * TRBs.Ring_Size;
   end Physical;

   function Full (EP : Endpoint_Range) return Boolean
   is
   begin
      return Pointers (EP).Full;
   end Full;

   function Last_Started (EP : Endpoint_Range) return Boolean
   is
      use type TRBs.Ring_Range;
   begin
      return
         not Pointers (EP).Overrun and
         Pointers (EP).Toggle = Pointers (EP).Enqueue;
   end Last_Started;

   function Get_Ring_Address (EP : Endpoint_Range) return Word64
   with SPARK_Mode => Off
   is
   begin
      return Word64
        (System.Storage_Elements.To_Integer (Rings (EP)'Address));
   end Get_Ring_Address;

   ----------------------------------------------------------------------------

   procedure Initialize (EP : Endpoint_Range)
   is
   begin
      pragma Debug (Debug.Put ("Initializing Transfer_Ring at "));
      pragma Debug (Debug.Put_Word64 (Get_Ring_Address (EP)));
      pragma Debug (Debug.Put (" (phys: "));
      pragma Debug (Debug.Put_Word64 (Physical (EP)));
      pragma Debug (Debug.Put_Line (")"));
      TRBs.Init_Cycle_Ring
        (Physical => Physical (EP),
         Ring     => Rings (EP));

      PCS (EP)       := 1;
      Pointers (EP)  := Transfer_Pointers'
        (Enqueue => TRBs.Ring_Range'First,
         Dequeue => TRBs.Ring_Range'First,
         Full    => False,
         Toggle  => TRBs.Ring_Range'First,
         Overrun => False);
   end Initialize;

   ----------------------------------------------------------------------------

   procedure Toggle_CS (EP : Endpoint_Range)
   is
      use type TRBs.Ring_Range;
      Toggle : TRBs.Ring_Range;
   begin
      Toggle := Pointers (EP).Toggle;
      while Toggle /= Pointers (EP).Enqueue or Pointers (EP).Overrun loop
         TRBs.Set_Cycle (Rings (EP) (Toggle), PCS (EP));
         if Toggle = TRBs.Ring_Range'Last then
            PCS (EP) := 1 - PCS (EP);
         end if;
         Toggle := Toggle + 1;

         Pointers (EP).Overrun := False;
      end loop;
      Pointers (EP).Toggle := Toggle;
   end Toggle_CS;

   ----------------------------------------------------------------------------

   function Prev (Current : TRBs.Ring_Range) return TRBs.Ring_Range
   is
      use type TRBs.Ring_Range;
   begin
      return Current - (if Current = TRBs.Ring_Range'First then 2 else 1);
   end Prev;

   function Next (Current : TRBs.Ring_Range) return TRBs.Ring_Range
   is
      use type TRBs.Ring_Range;
   begin
      return Current + (if Current + 1 = TRBs.Ring_Range'Last then 2 else 1);
   end Next;

   procedure Enqueue_TRB (EP : Endpoint_Range)
   is
      use type TRBs.Ring_Range;
   begin
      Pointers (EP).Enqueue := Next (Pointers (EP).Enqueue);
      if Pointers (EP).Enqueue = Pointers (EP).Toggle then
         Pointers (EP).Overrun := True;
      end if;
      if Pointers (EP).Enqueue = Pointers (EP).Dequeue then
         Pointers (EP).Full := True;
      end if;
   end Enqueue_TRB;

   procedure Dequeue_TRB (EP : Endpoint_Range)
   is
   begin
      Pointers (EP).Dequeue := Next (Pointers (EP).Dequeue);
      Pointers (EP).Full := False;
   end Dequeue_TRB;

   ----------------------------------------------------------------------------

   procedure Dequeue
     (EP                : Endpoint_Range;
      Pointer           : Word64;
      Status            : Error;
      Remaining_Length  : Natural)
   is
      use type TRBs.Ring_Range;

      Current : TRBs.Ring_Range;
      Invalid : Boolean;
   begin
      if Physical (EP) <= Pointer and
         Pointer - Physical (EP) < TRBs.Ring_Size and
         (Pointer - Physical (EP)) mod TRBs.TRB_Size = 0
      then
         Current := TRBs.Ring_Range
           ((Pointer - Physical (EP)) / TRBs.TRB_Size);

         if Pointers (EP).Dequeue < Pointers (EP).Enqueue then
            Invalid :=
               Current >= Pointers (EP).Enqueue or
               Current < Pointers (EP).Dequeue;
         else
            Invalid :=
               Current >= Pointers (EP).Enqueue and
               Current < Pointers (EP).Dequeue;
         end if;
         Invalid := Invalid or Current = TRBs.Ring_Range'Last;
      else
         Current := TRBs.Ring_Range'First;
         Invalid := True;
      end if;

      if not Invalid then
         while Pointers (EP).Dequeue /= Current loop
            -- Finish transfers that have been skipped by the controller
            pragma Debug (Debug.Put_Line ("WARNING: Skipped TD."));
            declare
               Cur_Address : constant Word64
                 := TRBs.Get_Parameter (Rings (EP) (Pointers (EP).Dequeue));
            begin
               Transfer_Info.Finish
                 (DMA_Physical      => Cur_Address,
                  Status            => Controller_Error,
                  Remaining_Length  => Max_Bulk_Size);
            end;
            Dequeue_TRB (EP);
         end loop;
         declare
            Cur_Address : constant Word64
              := TRBs.Get_Parameter (Rings (EP) (Current));
         begin
            Transfer_Info.Finish
              (DMA_Physical      => Cur_Address,
               Status            => Status,
               Remaining_Length  => Remaining_Length);
         end;
         Dequeue_TRB (EP);
      end if;

      pragma Debug (Invalid, Debug.Put_Reg64
        ("WARNING: Invalid dequeue pointer", Pointer));
      pragma Debug (Invalid, Debug.Put_Reg64
        ("                   Ring physical", Physical (EP)));
      pragma Debug (Invalid, Debug.Put ("Enqueue: "));
      pragma Debug (Invalid, Debug.Put_Int32 (Int32 (Pointers (EP).Enqueue)));
      pragma Debug (Invalid, Debug.Put ("; Dequeue: "));
      pragma Debug (Invalid, Debug.Put_Int32 (Int32 (Pointers (EP).Dequeue)));
      pragma Debug (Invalid, Debug.Put ("; Current: "));
      pragma Debug (Invalid, Debug.Put_Int32 (Int32 (Current)));
      pragma Debug (Invalid, Debug.New_Line);
   end Dequeue;

   ----------------------------------------------------------------------------

   procedure Enqueue_Data_TRB
     (EP                : Endpoint_Range;
      Data_Length       : Natural;
      Data_Buf          : Word64;
      Toggle_CS         : Boolean)
   is
      Current : TRBs.Ring_Range;
   begin
      Current := Pointers (EP).Enqueue;

      TRBs.Clear (Rings (EP) (Current), PCS (EP));
      TRBs.Set_Parameter (Rings (EP) (Current), Data_Buf);
      TRBs.Set_Length (Rings (EP) (Current), Data_Length);

      TRBs.Set_Type (Rings (EP) (Current), TRBs.Normal);
      TRBs.Set_IOC (Rings (EP) (Current));
      TRBs.Set_ISP (Rings (EP) (Current));

      Enqueue_TRB (EP);
      if Toggle_CS then
         Transfer_Rings.Toggle_CS (EP);
      end if;
   end Enqueue_Data_TRB;

   procedure Requeue_Data_TRB
     (EP       : Endpoint_Range;
      Length   : Natural;
      Buf_Addr : Word64)
   is
   begin
      Pointers (EP).Enqueue := Prev (Pointers (EP).Enqueue);
      Enqueue_Data_TRB (EP, Length, Buf_Addr, False);
   end Requeue_Data_TRB;

end HW.DbC.Transfer_Rings;

--  vim: set ts=8 sts=3 sw=3 et:
