package Q is
   function G1 return Integer is (1);
   function G2 return Integer;
   function G3 return Integer;
   function G4 return Integer is (G1 + G3 - 1);
end Q;
