package Private_Q is
   function G1 return Integer;
   function G2 return Integer;
   function G3 return Integer;
   function G4 return Integer;
private
   function G4 return Integer is (G1 + G3 - 1);
   function G1 return Integer is (1);
end Private_Q;
