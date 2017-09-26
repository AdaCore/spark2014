package body Globs with
  SPARK_Mode,
  Refined_State => (State => X)
is
   X : Integer := 1;

   function Pub return Integer with Refined_Global => X is
   begin
      return X;
   end Pub;

   procedure Pub_Out is
      Tmp : Integer;
   begin
      X := 1;
      Tmp := Pub;
   end Pub_Out;

end Globs;
