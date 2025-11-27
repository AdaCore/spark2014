package Affine_Cipher with SPARK_Mode is

   function Safe_Bounds (A, B : Integer) return Boolean is
     (
      (declare
         Scale : constant Integer := A * Character'Pos (Character'Last);
       begin
         Scale <= Integer'Last - B and
         Scale >= Integer'First - B
      ));

end Affine_Cipher;
