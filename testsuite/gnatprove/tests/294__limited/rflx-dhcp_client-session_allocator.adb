--
-- Generated by RecordFlux 0.10.1.dev8+g53cf133e on 2023-07-26
--
-- Copyright (C) 2018-2023 AdaCore GmbH
--
-- This file is distributed under the terms of the GNU Affero General Public License version 3.
--

pragma Style_Checks ("N3aAbCdefhiIklnOprStux");
pragma Warnings (Off, "redundant conversion");

package body RFLX.DHCP_Client.Session_Allocator with
  SPARK_Mode
is

   procedure Initialize (S : out Slots; M : Memory) with
     SPARK_Mode =>
       Off
   is
   begin
      S.Slot_Ptr_1 := M.Slot_1'Unrestricted_Access;
      S.Slot_Ptr_2 := M.Slot_2'Unrestricted_Access;
      S.Slot_Ptr_3 := M.Slot_3'Unrestricted_Access;
      S.Slot_Ptr_4 := M.Slot_4'Unrestricted_Access;
      S.Slot_Ptr_5 := M.Slot_5'Unrestricted_Access;
      S.Slot_Ptr_6 := M.Slot_6'Unrestricted_Access;
      S.Slot_Ptr_7 := M.Slot_7'Unrestricted_Access;
   end Initialize;

   procedure Finalize (S : in out Slots) with
     SPARK_Mode =>
       Off
   is
   begin
      S.Slot_Ptr_1 := null;
      S.Slot_Ptr_2 := null;
      S.Slot_Ptr_3 := null;
      S.Slot_Ptr_4 := null;
      S.Slot_Ptr_5 := null;
      S.Slot_Ptr_6 := null;
      S.Slot_Ptr_7 := null;
   end Finalize;

end RFLX.DHCP_Client.Session_Allocator;