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

with HW.GFX.DP_Defs;

private package HW.GFX.GMA.DP_Aux_Request is

   procedure Do_Aux_Request
     (Port              : in     DP_Port;
      Request           : in     DP_Defs.Aux_Request;
      Request_Length    : in     DP_Defs.Aux_Request_Length;
      Response          :    out DP_Defs.Aux_Response;
      Response_Length   :    out DP_Defs.Aux_Response_Length;
      Success           :    out Boolean);

end HW.GFX.GMA.DP_Aux_Request;
