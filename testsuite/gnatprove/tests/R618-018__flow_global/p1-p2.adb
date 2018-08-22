package body P1.P2 with Refined_State => (S2 => X2) is
   X2 : Integer := 0;
   function F2 return Integer with Refined_Global => X2 is
   begin
      return X2;
   end;
end;
