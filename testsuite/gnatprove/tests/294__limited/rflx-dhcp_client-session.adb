--
-- Generated by RecordFlux 0.10.1.dev8+g53cf133e on 2023-07-26
--
-- Copyright (C) 2018-2023 AdaCore GmbH
--
-- This file is distributed under the terms of the GNU Affero General Public License version 3.
--

pragma Restrictions (No_Streams);
pragma Style_Checks ("N3aAbCdefhiIklnOprStux");
pragma Warnings (Off, "redundant conversion");

package body RFLX.DHCP_Client.Session with
  SPARK_Mode
is
   procedure Initialize (Ctx : in out Context'Class) is
      Discover_Buffer : RFLX_Types.Bytes_Ptr;
      Offer_Buffer : RFLX_Types.Bytes_Ptr;
      Request_Buffer : RFLX_Types.Bytes_Ptr;
      Ack_Buffer : RFLX_Types.Bytes_Ptr;
   begin
      DHCP_Client.Session_Allocator.Initialize (Ctx.P.Slots, Ctx.P.Memory);
      Discover_Buffer := Ctx.P.Slots.Slot_Ptr_1;
      pragma Warnings (Off, "unused assignment");
      Ctx.P.Slots.Slot_Ptr_1 := null;
      pragma Warnings (On, "unused assignment");
      DHCP.Message.Initialize (Ctx.P.Discover_Ctx, Discover_Buffer);
      Offer_Buffer := Ctx.P.Slots.Slot_Ptr_2;
      pragma Warnings (Off, "unused assignment");
      Ctx.P.Slots.Slot_Ptr_2 := null;
      pragma Warnings (On, "unused assignment");
      DHCP.Message.Initialize (Ctx.P.Offer_Ctx, Offer_Buffer);
      Request_Buffer := Ctx.P.Slots.Slot_Ptr_3;
      pragma Warnings (Off, "unused assignment");
      Ctx.P.Slots.Slot_Ptr_3 := null;
      pragma Warnings (On, "unused assignment");
      DHCP.Message.Initialize (Ctx.P.Request_Ctx, Request_Buffer);
      Ack_Buffer := Ctx.P.Slots.Slot_Ptr_4;
      pragma Warnings (Off, "unused assignment");
      Ctx.P.Slots.Slot_Ptr_4 := null;
      pragma Warnings (On, "unused assignment");
      DHCP.Message.Initialize (Ctx.P.Ack_Ctx, Ack_Buffer);
      Ctx.P.Next_State := S_Create_Discover;
   end Initialize;

end RFLX.DHCP_Client.Session;