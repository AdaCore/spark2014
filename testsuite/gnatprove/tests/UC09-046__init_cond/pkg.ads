package Pkg
with SPARK_Mode,
     Initial_Condition => not Configured
is
  -- pragma Elaborate_Body;

   function Configured return Boolean with Ghost;

   procedure Configure
   with Pre => not Configured,
        Post => Configured;

private

   Is_Configured : Boolean := False;
   function Configured return Boolean is (Is_Configured);

end Pkg;
