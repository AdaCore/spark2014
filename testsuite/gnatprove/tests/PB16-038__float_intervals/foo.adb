package body Foo is

   type Float64 is digits 15;

   subtype Unit_T is Float64 range -1.0 .. 1.0;
   subtype Inv_T  is Float64 range -400.0 .. 400.0;

   subtype Safe_Unit_T is Unit_T
     with Static_Predicate => Safe_Unit_T not in -0.0025 .. 0.0025;

   procedure Test_01 (X : Unit_T;
                      Y : out Inv_T)
   is
   begin
      if X in 0.0 .. 0.0025 then
         Y := Inv_T'Last;
      elsif X in -0.0025 .. -0.0 then
         Y := Inv_T'First;
      else
         Y := 1.0 / X;  --  codepeer can prove this
      end if;
   end Test_01;

   procedure Test_02 (X : Safe_Unit_T;
                      Y : out Inv_T)
   is
   begin
      Y := 1.0 / X;
   end Test_02;

   procedure Test_03 (X : Unit_T;
                      Y : out Inv_T)
   is
   begin
      if X not in -0.0025 .. 0.0025 then
         Y := 1.0 / X;  --  codepeer can prove this
      elsif X >= 0.0025 then
         Y := Inv_T'Last;
      else
         pragma Assert (X <= -0.0025);
         Y := Inv_T'First;
      end if;
   end Test_03;

end Foo;
