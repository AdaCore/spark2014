--
-- Generated by RecordFlux 0.10.1.dev8+g53cf133e on 2023-07-26
--
-- Copyright (C) 2018-2023 AdaCore GmbH
--
-- This file is distributed under the terms of the GNU Affero General Public License version 3.
--

with RFLX.RFLX_Types;

package RFLX.DHCP.Message with
  SPARK_Mode,
  Always_Terminates
is

   type Virtual_Field is (F_Initial, F_Op, F_Htype, F_Hlen, F_Hops, F_Xid, F_Secs, F_Broadcast_Flag, F_Reserved_Flags, F_Ciaddr, F_Yiaddr, F_Siaddr, F_Giaddr, F_Chaddr, F_Sname, F_File, F_Magic_Cookie, F_Options, F_Final);

   subtype Field is Virtual_Field range F_Op .. F_Options;

   type Field_Cursor is private with
     Default_Initial_Condition =>
       False;

   type Field_Cursors is private with
     Default_Initial_Condition =>
       False;

   type Context (Buffer_First, Buffer_Last : RFLX_Types.Index := RFLX_Types.Index'First; First : RFLX_Types.Bit_Index := RFLX_Types.Bit_Index'First; Last : RFLX_Types.Bit_Length := RFLX_Types.Bit_Length'First) is private;

   procedure Initialize (Ctx : out Context; Buffer : in out RFLX_Types.Bytes_Ptr; Written_Last : RFLX_Types.Bit_Length := 0);

   procedure Initialize (Ctx : out Context; Buffer : in out RFLX_Types.Bytes_Ptr; First : RFLX_Types.Bit_Index; Last : RFLX_Types.Bit_Length; Written_Last : RFLX_Types.Bit_Length := 0);

private

   type Cursor_State is (S_Valid, S_Well_Formed, S_Invalid, S_Incomplete);

   type Field_Cursor (State : Cursor_State := S_Invalid) is
      record
         case State is
            when S_Valid | S_Well_Formed =>
               First : RFLX_Types.Bit_Index := RFLX_Types.Bit_Index'First;
               Last : RFLX_Types.Bit_Length := RFLX_Types.Bit_Length'First;
               Value : RFLX_Types.Base_Integer := 0;
            when S_Invalid | S_Incomplete =>
               null;
         end case;
      end record;

   type Field_Cursors is array (Virtual_Field) of Field_Cursor;

   type Context (Buffer_First, Buffer_Last : RFLX_Types.Index := RFLX_Types.Index'First; First : RFLX_Types.Bit_Index := RFLX_Types.Bit_Index'First; Last : RFLX_Types.Bit_Length := RFLX_Types.Bit_Length'First) is
      record
         Buffer : RFLX_Types.Bytes_Ptr := null;
         Cursors : Field_Cursors := (others => (State => S_Invalid));
      end record;

end RFLX.DHCP.Message;
