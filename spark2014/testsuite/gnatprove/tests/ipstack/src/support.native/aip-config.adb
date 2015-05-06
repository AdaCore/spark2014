------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with Ada.Command_Line;

package body AIP.Config with
  SPARK_Mode => Off
is

   type String_Ptr is access all String;
   Params : String_Ptr;

   --------------------------
   -- Interface_Parameters --
   --------------------------

   function Interface_Parameters return System.Address is
   begin
      if Params = null and then Ada.Command_Line.Argument_Count > 0 then
         Params := new String'(Ada.Command_Line.Argument (1) & ASCII.NUL);
      end if;

      if Params = null then
         return System.Null_Address;
      else
         return Params.all'Address;
      end if;
   end Interface_Parameters;

end AIP.Config;
