with Pack;

package body Weird is

   procedure PG (B : Boolean) is
   begin
      if B then
         PG (not B);
      else
         Pack.Call_Jump (B);
      end if;
   end PG;

   procedure QG (B : Boolean) is
   begin
      if B then
         QG (not B);
      else
         Pack.Call_Jump (B);
      end if;
   end QG;

   procedure RG (B : Boolean) is
   begin
      raise Program_Error;
   end RG;

end Weird;
