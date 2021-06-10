procedure Bad_Moves_Of_Shallow with SPARK_Mode is
   type Int_Ptr is access all Integer;
   X1 : aliased Integer := 10;
   X2 : aliased Integer := 10;
   X3 : aliased Integer := 10;
   Y : Int_Ptr := X2'Access;

   package Nested is
      X3 : aliased Integer := 10;
      Z  : Int_Ptr := X3'Access; -- Error, X3 moved during elaboration
   end Nested;

   procedure Bad_1 with Global => (Input => X1) is -- Error, X1 is moved on return
      Z : Int_Ptr := X1'Access;
   begin
      pragma Assert (X1 = 10); -- Error, X1 is moved
   end Bad_1;

   procedure Bad_2 (X : aliased in out Integer) with Global => null is -- Error, X is moved on return
      type Loc_Int_Ptr is access all Integer;
      Z : Loc_Int_Ptr := X'Access;
   begin
      pragma Assert (X = 10); -- Error, X is moved
   end Bad_2;

   function Get return Int_Ptr is -- Error, X3 is moved on return
     (X3'Access);
begin
   Y.all := 12;
   X2 := 15;                -- Error, X2 is moved
   pragma Assert (X2 = 10); -- Error, X2 is moved
end Bad_Moves_Of_Shallow;
