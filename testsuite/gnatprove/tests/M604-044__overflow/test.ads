package Test
is
   type Enum_T is (Elem_0, Elem_1, Elem_2);

   function Range_Check_Error (A : in Enum_T) return Enum_T;
end Test;
