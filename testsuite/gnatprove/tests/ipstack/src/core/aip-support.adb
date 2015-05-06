------------------------------------------------------------------------------
--                            IPSTACK COMPONENTS                            --
--          Copyright (C) 2010-2014, Free Software Foundation, Inc.         --
------------------------------------------------------------------------------

with GNAT.IO;

package body AIP.Support is

   ---------
   -- Log --
   ---------

   procedure Log (Msg : String) with
     SPARK_Mode => Off
   is
   begin
      GNAT.IO.Put_Line (Msg);
   end Log;

   ------------
   -- Verify --
   ------------

   procedure Verify (T : Boolean) with
      SPARK_Mode => Off
   is
   begin
      if not T then
         raise Program_Error;
      end if;
   end Verify;

   -------------------
   -- Verify_Or_Err --
   -------------------

   procedure Verify_Or_Err
     (T        : Boolean;
      Err      : out AIP.Err_T;
      Err_Type : AIP.Err_T) is
   begin
      if not T then
         Err := Err_Type;
      else
         Err := AIP.NOERR;
      end if;
   end Verify_Or_Err;

end AIP.Support;
