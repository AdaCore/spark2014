package body Misovattr
is
   function Range_Check_Error (A : in Enum_T) return Enum_T
   is
   begin
      pragma Assert (Enum_S'Succ (A) > A);
      pragma Assert (Enum_T'Succ (A) > A);
      pragma Assert (Enum_S'Pred (A) < A);
      pragma Assert (Enum_T'Pred (A) < A);
      return A;
   end Range_Check_Error;
end Misovattr;
