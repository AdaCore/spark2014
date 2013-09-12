package body Main
is

   type R is record
      A : T;
      B : T;
   end record;

   procedure Do_Stuff (X : in out T)
   is
   begin
      X.A := X.B;
      X.B := False;
   end Do_Stuff;

   procedure Do_Stuff_02 (X : in out R)
   is
   begin
      X.A := X.B;
      X.A.B := False;
   end Do_Stuff_02;

   procedure Do_Stuff_03 (X : in out U)
   is
   begin
      X.A := X.B;
      X.B := False;
   end Do_Stuff_03;

   --  procedure Do_Stuff_04 (X : in out V)
   --  is
   --  begin
   --     X.A := X.B;
   --     X.B := False;
   --  end Do_Stuff_04;


end Main;
