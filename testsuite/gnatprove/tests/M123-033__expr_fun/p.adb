with Unknown;
package body P is
   procedure P1 is
   begin
      case Unknown.Value is
         when 0 =>
            pragma Assert (F1 = 1);
         when 1 =>
            pragma Assert (F2 = 1);
         when 2 =>
            pragma Assert (F3 = 1);
         when 3 =>
            pragma Assert (F4 = 1); -- unprovable
         when 4 =>
            pragma Assert (G1 = 1);
         when 5 =>
            pragma Assert (G2 = 1); -- unprovable
         when 6 =>
            pragma Assert (G3 = 1); -- unprovable
         when 7 =>
            pragma Assert (G4 = 1); -- unprovable
         when others =>
            null;
      end case;
   end P1;

   function F3 return Integer is (1);

   procedure P2 is
   begin
      case Unknown.Value is
         when 0 =>
            pragma Assert (F1 = 1);
         when 1 =>
            pragma Assert (F2 = 1);
         when 2 =>
            pragma Assert (F3 = 1);
         when 3 =>
            pragma Assert (F4 = 1); -- unprovable
         when 4 =>
            pragma Assert (G1 = 1);
         when 5 =>
            pragma Assert (G2 = 1); -- unprovable
         when 6 =>
            pragma Assert (G3 = 1); -- unprovable
         when 7 =>
            pragma Assert (G4 = 1); -- unprovable
         when others =>
            null;
      end case;
   end P2;
end P;
