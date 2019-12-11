with Pack;

package body Weird is

   procedure P (B : Boolean) is
   begin
      if B then
         P (not B);
      else
         Pack.Call_Jump (B);
      end if;
   end P;

   procedure Q (B : Boolean) renames P;

   procedure R (B : Boolean) is
   begin
      raise Program_Error;
   end R;

end Weird;
