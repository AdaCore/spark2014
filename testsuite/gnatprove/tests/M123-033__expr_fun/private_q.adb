with Unknown;
with Private_P; use Private_P;
package body Private_Q is
   procedure Q1 is
   begin
      case Unknown.Value is
         when 0 =>
            pragma Assert (F1 = 1);
         when 1 =>
            pragma Assert (F2 = 1);
         when 2 =>
            pragma Assert (F3 = 1); -- unprovable
         when 3 =>
            pragma Assert (F4 = 1); -- unprovable
         when 4 =>
            pragma Assert (G1 = 1);
         when 5 =>
            pragma Assert (G2 = 1);
         when 6 =>
            pragma Assert (G3 = 1);
         when 7 =>
            pragma Assert (G4 = 1);
         when others =>
            null;
      end case;
   end Q1;

   procedure Q2 is
   begin
      case Unknown.Value is
         when 0 =>
            pragma Assert (F1 = 1);
         when 1 =>
            pragma Assert (F2 = 1);
         when 2 =>
            pragma Assert (F3 = 1); -- unprovable
         when 3 =>
            pragma Assert (F4 = 1); -- unprovable
         when 4 =>
            pragma Assert (G1 = 1);
         when 5 =>
            pragma Assert (G2 = 1);
         when 6 =>
            pragma Assert (G3 = 1);
         when 7 =>
            pragma Assert (G4 = 1);
         when others =>
            null;
      end case;
   end Q2;

   function G2 return Integer is (G1 + G3 - 1);
   function G3 return Integer is (1);
end Private_Q;
