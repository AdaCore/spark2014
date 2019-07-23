procedure Mypre is

   procedure Havoc (X : in out Boolean)
   with Global => null,
        Pre => True;

   procedure Havoc (X : in out Boolean) is
   begin
      X := not X;
   end Havoc;

   A, B : Boolean := True;

   procedure Pre_Check with Pre => A and then B;

   procedure Pre_Check is
   begin
      null;
   end Pre_Check;

begin
   Havoc (B);
   Pre_Check;
end Mypre;
