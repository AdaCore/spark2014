package body Casing is

   function G (X : Two) return Integer is
      Res : Integer;
   begin
      case X is
         when M => Res := 0;
         when N => Res := 1;
      end case;
      return Res;
   end G;

   function F (X : En) return Integer is
      Res : Integer;
   begin
      case X is
         when A => Res := 0;
         when B => Res := 1;
         when C .. D => Res := 2;
         when others => Res := 3;
      end case;
      return Res;
   end F;

end Casing;
