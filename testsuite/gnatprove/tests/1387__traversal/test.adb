procedure Test with SPARK_Mode is

   --  Test call to traversal function with discriminants on a private type

   package Nested is
      type T (D : Natural) is private;
      function Reference (X : aliased in out T) return not null access Integer with
        Global => null, Import;
   private
      type Int_Arr is array (Positive range <>) of aliased Integer;
      type T (D : Natural) is record
         Content : Int_Arr (1 .. D);
      end record;
   end Nested;

   procedure Test_Reference is
      X : aliased Nested.T (12);
      I : not null access Integer := Nested.Reference (X);
   begin
      I.all := 13;
   end Test_Reference;
begin
   null;
end;
