------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--             Copyright (C) 2010, Free Software Foundation, Inc.           --
------------------------------------------------------------------------------

package AIP_Ctypes is

   type S8_T is range -2 ** 7 .. 2 ** 7 - 1;

   type U8_T is mod 2 ** 8;
   type U16_T is mod 2 ** 16;
   type U32_T is mod 2 ** 32;

   subtype Err_T is S8_T;
   NOERR : constant Err_T := 0;

end AIP_Ctypes;
