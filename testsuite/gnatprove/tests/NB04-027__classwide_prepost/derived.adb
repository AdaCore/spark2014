package body Derived is

   procedure Create (X : out D) is
   begin
      X.B := False;
   end Create;

   procedure Do_Stuff (X : in out D) is
   begin
      null;
   end Do_Stuff;

end Derived;
