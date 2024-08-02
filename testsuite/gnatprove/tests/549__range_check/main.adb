procedure Main with SPARK_Mode is

   function Rand (X : Integer) return Integer with
     Global => null,
     Import;

   package P5 is
      subtype My_Pos is Positive range 1 .. Rand (5);

      type A is array (Positive range 1 .. 10) of My_Pos
        with Default_Component_Value => 5; --  @RANGE_CHECK:FAIL

      type R is record
         F : A;
      end record;
   end P5;
   X5 : P5.R;
begin
   null;
end Main;
