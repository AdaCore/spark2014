package body Upd is

   procedure Test_01 (X : in out R2)
   is
   begin
      X := X'Update (U => (X => 1, Y => 2));
   end Test_01;

end Upd;
