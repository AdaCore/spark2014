package Test with
SPARK_Mode
is

   type E_Type is (A, B);

   type C_Type is
      record
         E : E_Type;
      end record;

   function Get_E (C : C_Type) return E_Type is
      (C.E);

   procedure Test with
     Pre => (if Get_E (C_Type'(E => A)) = A and then Get_E (C_Type'(E => A)) = B then True else True);

end Test;
