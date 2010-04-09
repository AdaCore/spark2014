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
   ERR_MEM : constant Err_T := -1;
   ERR_ABRT : constant Err_T := -4;

   type SI_T is mod 2 ** 64;
   --  State Index type, to be used to access application state pools and as
   --  user data id across callbacks. This needs to be machine address size as
   --  long as we rely on the original LWIP implementation.

   NOSID : constant SI_T := 0;

end AIP_Ctypes;
