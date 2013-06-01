package body Casing is

   function F (X : Integer) return Integer is
      Res : Integer;
   begin
      case X is
         when 0 => Res := 1;
         when 1 => Res := 2;
         when others => Res := X + 1;
      end case;
      return Res;
   end F;

   function G (X : Integer) return Integer is
      Res : Integer;
   begin
      Res :=
         (case X is
            when 0 => 1,
            when 1 => 2,
            when others => X + 1);
      return Res;
   end G;
end Casing;
