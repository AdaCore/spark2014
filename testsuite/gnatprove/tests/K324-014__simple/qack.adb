with Pack;
package body Qack is

   procedure Flip is
   begin
      X := not X;
   end Flip;

   procedure Bad is
   begin
      Pack.Indirect;
   end Bad;

end;
