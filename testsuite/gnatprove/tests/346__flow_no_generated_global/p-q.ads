package P.Q is
   function F1 return Boolean with Global => Full_State;
   function F2 return Boolean with Global => Full_State;
   --  One of these needs a Refined_Global while the other can't have it
end;
