with Pack;
package body Qack is

   X : Boolean;

   procedure Flip is
   begin
      X := not X;
   end Flip;

   procedure Bad
     with Post => X = X'Old; -- should not be provable (actually it is false)

   procedure Bad is
   begin
      Pack.Indirect;
   end Bad;

end;
