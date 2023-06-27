procedure Main with SPARK_Mode is
   type A is record
      V : aliased Integer;
   end record;
   type B is record
      F_A : aliased A;
   end record;
   type C is record
      F_B : aliased B;
   end record;
   function At_End (X : access constant C) return access constant C is (X)
     with Ghost, Global => null, Annotate => (GNATprove, At_End_Borrow);
   procedure F (X : aliased in out C) is
      Y : access C := X'Access;
      Z : constant access constant B := At_End (Y).F_B'Access with Ghost;
      T : constant access constant A := Z.F_A'Access with Ghost;
      U : constant access constant Integer := T.V'Access with Ghost;
   begin
      pragma Assert (Z.F_A.V = U.all);
      pragma Assert (T.all = Y.F_B.F_A); --@ASSERT:FAIL
      Y.F_B.F_A := (V => 1);
   end F;
begin
   null;
end Main;
