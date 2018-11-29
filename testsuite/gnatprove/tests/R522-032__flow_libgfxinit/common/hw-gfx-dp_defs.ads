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

package HW.GFX.DP_Defs is

   type Aux_Message_Command is mod 2 ** 4;
   type Aux_Message_Address is mod 2 ** 20;

   subtype Aux_Payload_Length is Natural range 0 .. 16;
   subtype Aux_Payload_Index is Natural range 0 .. Aux_Payload_Length'Last - 1;
   subtype Aux_Payload is Buffer (Aux_Payload_Index);

   subtype Aux_Request_Length is Natural range 3 .. 20;
   subtype Aux_Request_Index is Natural range 0 .. Aux_Request_Length'Last - 1;
   subtype Aux_Request is Buffer (Aux_Request_Index);

   subtype Aux_Response_Length is Natural range 1 .. 17;
   subtype Aux_Response_Index is
      Natural range 0 .. Aux_Response_Length'Last - 1;
   subtype Aux_Response is Buffer (Aux_Response_Index);

end HW.GFX.DP_Defs;
