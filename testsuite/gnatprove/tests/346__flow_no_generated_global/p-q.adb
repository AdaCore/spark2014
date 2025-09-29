package body P.Q is
   function F1 return Boolean
   is (Read_Private_And_Body_State);  --  no legal Refined_Global possible

   function F2 return Boolean
   is (P.Private_State)
   with Refined_Global => P.Private_State;
end;
