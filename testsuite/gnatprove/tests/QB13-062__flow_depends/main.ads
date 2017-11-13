package Main with Abstract_State => S is

   procedure Test with Depends => (null => S);
   --  The explicit Depends references a state whose non-singleton refinement
   --  is visible at the body, so flow will still generate a (Refined_)Global
   --  contract.

end;
