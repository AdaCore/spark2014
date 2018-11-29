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

with HW.Time;
with HW.GFX.DP_Defs;

use type HW.Word8;
use type HW.GFX.DP_Defs.Aux_Message_Command;

package body HW.GFX.DP_Aux_Ch is

   DP_AUX_I2C_WRITE           : constant := 16#0#;
   DP_AUX_I2C_READ            : constant := 16#1#;
   DP_AUX_I2C_WR_STATUS_REQ   : constant := 16#2#;
   DP_AUX_I2C_MOT             : constant := 16#4#;
   DP_AUX_NATIVE_WRITE        : constant := 16#8#;
   DP_AUX_NATIVE_READ         : constant := 16#9#;

   procedure Fill_Aux_Request
     (Request  :    out DP_Defs.Aux_Request;
      Command  : in     DP_Defs.Aux_Message_Command;
      Address  : in     DP_Defs.Aux_Message_Address;
      Length   : in     DP_Defs.Aux_Payload_Length)
   is
   begin
      Request :=
        (0      => Shift_Left (Word8 (Command), 4) or
                   Word8 (Shift_Right (Word32 (Address), 16)),
         1      => Word8 (Shift_Right (Word32 (Address),  8) and 16#ff#),
         2      => Word8 (Shift_Right (Word32 (Address),  0) and 16#ff#),
         3      => Word8 (Length) - 1,
         others => 0);  -- Don't care
   end Fill_Aux_Request;

   function Is_Empty (Request : DP_Defs.Aux_Request) return Boolean is
   begin
      return Request (3) = 16#ff#;
   end Is_Empty;

   function Is_Aux_Ack (Response : DP_Defs.Aux_Response) return Boolean
   with
      Depends => (Is_Aux_Ack'Result => Response)
   is
   begin
      return (Response (0) and 16#30#) = 16#00#;
   end Is_Aux_Ack;

   function Is_Aux_Defer (Response : DP_Defs.Aux_Response) return Boolean is
   begin
      return (Response (0) and 16#30#) = 16#20#;
   end Is_Aux_Defer;

   function Is_I2C_Ack (Response : DP_Defs.Aux_Response) return Boolean
   with
      Depends => (Is_I2C_Ack'Result => Response)
   is
   begin
      return (Response (0) and 16#c0#) = 16#00#;
   end Is_I2C_Ack;

   function Is_I2C_Defer (Response : DP_Defs.Aux_Response) return Boolean is
   begin
      return (Response (0) and 16#c0#) = 16#80#;
   end Is_I2C_Defer;

   ----------------------------------------------------------------------------

   procedure Do_Aux_Request
     (Port              : in     T;
      Request           : in     DP_Defs.Aux_Request;
      Request_Length    : in     DP_Defs.Aux_Request_Length;
      Response          :    out DP_Defs.Aux_Response;
      Response_Length   :    out DP_Defs.Aux_Response_Length;
      Success           :    out Boolean)
   is
   begin
      for Try in Positive range 1 .. 32 loop
         Aux_Request
           (Port              => Port,
            Request           => Request,
            Request_Length    => Request_Length,
            Response          => Response,
            Response_Length   => Response_Length,
            Success           => Success);

         exit when not (Success and Is_Aux_Defer (Response));
         Time.U_Delay (500);
      end loop;

      Success := Success and then Is_Aux_Ack (Response);
   end Do_Aux_Request;

   ----------------------------------------------------------------------------

   procedure Aux_Read
     (Port     : in     T;
      Address  : in     DP_Defs.Aux_Message_Address;
      Length   : in out DP_Defs.Aux_Payload_Length;
      Data     :    out DP_Defs.Aux_Payload;
      Success  :    out Boolean)
   is
      Request : DP_Defs.Aux_Request;
      Response : DP_Defs.Aux_Response;
      Response_Length : DP_Defs.Aux_Response_Length;
   begin
      Data := (others => 0);  -- Initialize

      Fill_Aux_Request
        (Request  => Request,
         Command  => DP_AUX_NATIVE_READ,
         Address  => Address,
         Length   => Length);

      Do_Aux_Request
        (Port              => Port,
         Request           => Request,
         Request_Length    => 4,
         Response          => Response,
         Response_Length   => Response_Length,
         Success           => Success);

      Success := Success and then Response_Length > 1;
      if Success then
         pragma Assert (Response_Length > 1);
         Length := Response_Length - 1;
         Data (0 .. Length - 1) :=  Response (1 .. Length);
      end if;
   end Aux_Read;

   procedure Aux_Write
     (Port     : in     T;
      Address  : in     DP_Defs.Aux_Message_Address;
      Length   : in     DP_Defs.Aux_Payload_Length;
      Data     : in     DP_Defs.Aux_Payload;
      Success  :    out Boolean)
   is
      Request : DP_Defs.Aux_Request;

      Ignored_Response        : DP_Defs.Aux_Response;
      Ignored_Response_Length : DP_Defs.Aux_Response_Length;
   begin
      Fill_Aux_Request
        (Request  => Request,
         Command  => DP_AUX_NATIVE_WRITE,
         Address  => Address,
         Length   => Length);
      Request (4 .. Length + 4 - 1) := Data (0 .. Length - 1);

      pragma Warnings (GNATprove, Off,
                       "unused assignment to ""Ignored_Response*""",
                       Reason => "No response expected here");
      Do_Aux_Request
        (Port              => Port,
         Request           => Request,
         Request_Length    => 4 + Length,
         Response          => Ignored_Response,
         Response_Length   => Ignored_Response_Length,
         Success           => Success);
   end Aux_Write;

   ----------------------------------------------------------------------------

   procedure I2C_Out_Packet
     (Port              : in     T;
      Command           : in     DP_Defs.Aux_Message_Command;
      Address           : in     DP_Defs.Aux_Message_Address;
      Length            : in     DP_Defs.Aux_Payload_Length;
      Data              : in     DP_Defs.Aux_Payload;
      Success           :    out Boolean)
   is
      Request : DP_Defs.Aux_Request;

      Response : DP_Defs.Aux_Response;
      Ignored_Response_Length : DP_Defs.Aux_Response_Length;
   begin
      Fill_Aux_Request
        (Request  => Request,
         Command  => Command,
         Address  => Address,
         Length   => Length);
      Request (4 .. Length + 4 - 1) := Data (0 .. Length - 1);
      for Try in Positive range 1 .. 7 loop
         pragma Warnings (GNATprove, Off,
                          "unused assignment to ""Ignored_Response_Length""",
                          Reason => "No response expected here");
         Do_Aux_Request
           (Port              => Port,
            Request           => Request,
            Request_Length    => (if Is_Empty (Request) then 3 else 4 + Length),
            Response          => Response,
            Response_Length   => Ignored_Response_Length,
            Success           => Success);
         exit when not (Success and Is_I2C_Defer (Response));

         -- Command was already AUX-acked. Thus, only query for
         -- new status from now on until we get I2C-acked too.
         Fill_Aux_Request
           (Request  => Request,
            Command  => (Command and DP_AUX_I2C_MOT) or DP_AUX_I2C_WR_STATUS_REQ,
            Address  => Address,
            Length   => 0);
         Time.U_Delay (500);
      end loop;
      Success := Success and then Is_I2C_Ack (Response);
   end I2C_Out_Packet;

   procedure I2C_In_Packet
     (Port              : in     T;
      Command           : in     DP_Defs.Aux_Message_Command;
      Address           : in     DP_Defs.Aux_Message_Address;
      Length            : in     DP_Defs.Aux_Payload_Length;
      Response          :    out DP_Defs.Aux_Response;
      Response_Length   :    out DP_Defs.Aux_Response_Length;
      Success           :    out Boolean)
   is
      Request : DP_Defs.Aux_Request;
   begin
      Fill_Aux_Request
        (Request  => Request,
         Command  => Command,
         Address  => Address,
         Length   => Length);
      for Try in Positive range 1 .. 7 loop
         Do_Aux_Request
           (Port              => Port,
            Request           => Request,
            Request_Length    => (if Is_Empty (Request) then 3 else 4),
            Response          => Response,
            Response_Length   => Response_Length,
            Success           => Success);
         exit when not (Success and Is_I2C_Defer (Response));

         Time.U_Delay (500);
      end loop;
      Success := Success and then Is_I2C_Ack (Response);
   end I2C_In_Packet;

   procedure I2C_Empty_Packet
     (Port              : in     T;
      Command           : in     DP_Defs.Aux_Message_Command;
      Address           : in     DP_Defs.Aux_Message_Address;
      Success           :    out Boolean)
   is
      Ignored_Response        : DP_Defs.Aux_Response;
      Ignored_Response_Length : DP_Defs.Aux_Response_Length;
   begin
      pragma Warnings (GNATprove, Off,
                       "unused assignment to ""Ignored_Response*""",
                       Reason => "No response expected here");
      I2C_In_Packet
        (Port              => Port,
         Command           => Command,
         Address           => Address,
         Length            => 0,
         Response          => Ignored_Response,
         Response_Length   => Ignored_Response_Length,
         Success           => Success);
   end I2C_Empty_Packet;

   ----------------------------------------------------------------------------

   procedure Do_I2C_Write
     (Port     : in     T;
      Address  : in     I2C.Transfer_Address;
      Length   : in     DP_Defs.Aux_Payload_Length;
      Data     : in     DP_Defs.Aux_Payload;
      Success  :    out Boolean)
   is
      Ignored_Success : Boolean;
   begin
      -- I2C address "start" packet
      I2C_Empty_Packet
        (Port     => Port,
         Command  => DP_AUX_I2C_WRITE or DP_AUX_I2C_MOT,
         Address  => DP_Defs.Aux_Message_Address (Address),
         Success  => Success);

      if Success then
         I2C_Out_Packet
           (Port              => Port,
            Command           => DP_AUX_I2C_WRITE or DP_AUX_I2C_MOT,
            Address           => DP_Defs.Aux_Message_Address (Address),
            Length            => Length,
            Data              => Data,
            Success           => Success);

         pragma Warnings
           (GNATprove, Off, "unused assignment to ""Ignored_Success""",
            Reason => "Doesn't matter as long as the transfer itself succeeds");
         -- I2C address "stop" packet
         I2C_Empty_Packet
           (Port     => Port,
            Command  => DP_AUX_I2C_WRITE,
            Address  => DP_Defs.Aux_Message_Address (Address),
            Success  => Ignored_Success);
      end if;
   end Do_I2C_Write;

   procedure Do_I2C_Read
     (Port     : in     T;
      Address  : in     I2C.Transfer_Address;
      Length   : in out I2C.Transfer_Length;
      Data     : in out I2C.Transfer_Data;
      Success  :    out Boolean)
   is
      Xfered   : Natural := 0;
      Chunk    : DP_Defs.Aux_Payload_Length := DP_Defs.Aux_Payload_Length'Last;

      Tries       : Natural := 0;
      Max_Tries   : constant := 4;

      Response : DP_Defs.Aux_Response;
      Response_Length : DP_Defs.Aux_Response_Length;

      Ignored_Success : Boolean;
   begin
      -- I2C address "start" packet
      I2C_Empty_Packet
        (Port     => Port,
         Command  => DP_AUX_I2C_READ or DP_AUX_I2C_MOT,
         Address  => DP_Defs.Aux_Message_Address (Address),
         Success  => Success);

      while Success and then (Xfered < Length and Tries < Max_Tries) loop
         I2C_In_Packet
           (Port              => Port,
            Command           => DP_AUX_I2C_READ or DP_AUX_I2C_MOT,
            Address           => DP_Defs.Aux_Message_Address (Address),
            Length            => Natural'Min (Chunk, Length - Xfered),
            Response          => Response,
            Response_Length   => Response_Length,
            Success           => Success);

         if Success and then Response_Length >= 2 then
            Chunk := Natural'Min (Response_Length - 1, Length - Xfered);
            Data (Xfered .. Xfered + Chunk - 1) := Response (1 .. Chunk);
            Xfered := Xfered + Chunk;
            Tries := 0;
         else
            Tries := Tries + 1;
         end if;
         pragma Loop_Invariant (Xfered <= Length);
      end loop;

      if Success then
         pragma Warnings
           (GNATprove, Off, "unused assignment to ""Ignored_Success""",
            Reason => "Doesn't matter as long as the transfer itself succeeds");
         -- I2C address "stop" packet
         I2C_Empty_Packet
           (Port     => Port,
            Command  => DP_AUX_I2C_READ,
            Address  => DP_Defs.Aux_Message_Address (Address),
            Success  => Ignored_Success);
      end if;

      Success := Success and then Tries < Max_Tries;
      Length := Xfered;
   end Do_I2C_Read;

   ----------------------------------------------------------------------------

   procedure I2C_Read
     (Port     : in     T;
      Address  : in     I2C.Transfer_Address;
      Length   : in out I2C.Transfer_Length;
      Data     :    out I2C.Transfer_Data;
      Success  :    out Boolean)
   is
      Index_Payload : DP_Defs.Aux_Payload;
   begin
      Data := (others => 16#00#);

      Index_Payload := (others => 16#00#);   -- send index 0
      Do_I2C_Write (Port, Address, 1, Index_Payload, Success);

      if Success then
         Do_I2C_Read (Port, Address, Length, Data, Success);
      end if;
   end I2C_Read;

end HW.GFX.DP_Aux_Ch;
