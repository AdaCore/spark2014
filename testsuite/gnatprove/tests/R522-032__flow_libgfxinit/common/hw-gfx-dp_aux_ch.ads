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

with HW.GFX.I2C;
with HW.GFX.DP_Defs;

private generic

   type T (<>) is limited private;

   with procedure Aux_Request
     (Port              : in     T;
      Request           : in     DP_Defs.Aux_Request;
      Request_Length    : in     DP_Defs.Aux_Request_Length;
      Response          :    out DP_Defs.Aux_Response;
      Response_Length   :    out DP_Defs.Aux_Response_Length;
      Success           :    out Boolean);

package HW.GFX.DP_Aux_Ch is

   procedure Aux_Read
     (Port     : in     T;
      Address  : in     DP_Defs.Aux_Message_Address;
      Length   : in out DP_Defs.Aux_Payload_Length;
      Data     :    out DP_Defs.Aux_Payload;
      Success  :    out Boolean);

   procedure Aux_Write
     (Port     : in     T;
      Address  : in     DP_Defs.Aux_Message_Address;
      Length   : in     DP_Defs.Aux_Payload_Length;
      Data     : in     DP_Defs.Aux_Payload;
      Success  :    out Boolean);

   ----------------------------------------------------------------------------

   procedure I2C_Read
     (Port     : in     T;
      Address  : in     I2C.Transfer_Address;
      Length   : in out I2C.Transfer_Length;
      Data     :    out I2C.Transfer_Data;
      Success  :    out Boolean);

end HW.GFX.DP_Aux_Ch;
