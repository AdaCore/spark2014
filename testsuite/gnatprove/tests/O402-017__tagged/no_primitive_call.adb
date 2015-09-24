package body No_Primitive_Call with SPARK_Mode is
   procedure Init (I : in out Root; C : Natural) is
   begin
      I.F := C;
   end Init;

   procedure Internal (X : in out Root'Class) is
   begin
      X.Init (0);
   end Internal;
end No_Primitive_Call;
