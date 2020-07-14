with Ada.Text_IO;
package body P is
   protected body PT is
      --  The following is *not* a protected subprogram, because it can only be
      --  called from within protected object after it has been already locked;
      --  also, it doesn't match the strict definition of (Ada RM 9.4).
      procedure Fake is
      begin
         Ada.Text_IO.Put_Line ("OK");
      end;

      procedure Real is
      begin
         Fake;
      end;
   end;
end;
