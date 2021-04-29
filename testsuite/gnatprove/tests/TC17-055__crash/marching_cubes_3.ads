package Marching_Cubes_3
with SPARK_Mode => On
is
   type Int_Ptr is access Integer;
   type Holder is record
      C : Int_Ptr;
   end record;
   procedure P (X : in out Holder) with
     Post => (Boolean'(X.C = null)'Old = (X.C = null)); --@POSTCONDITION:FAIL

end Marching_Cubes_3;
