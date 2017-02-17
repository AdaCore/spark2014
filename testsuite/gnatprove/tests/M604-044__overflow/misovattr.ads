package Misovattr
is
   type Enum_T is (A, B, C);
   subtype Enum_S is Enum_T range A .. B;


   function Range_Check_Error (A : in Enum_T) return Enum_T;
end Misovattr;
