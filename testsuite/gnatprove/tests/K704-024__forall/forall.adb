procedure Forall is
   pragma SPARK_Mode (Off);  --  iterator on array

   type R is record X, Y : Boolean; end record;
   type Rrrs is array (Integer range 1 .. 10) of R;

   Body_Violations : Rrrs;

   function Body_Is_Computed_In_Alfa return Boolean is
     (for all S of Body_Violations => not S.X);

begin
   null;
end Forall;
