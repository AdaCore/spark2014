procedure P (I : Integer) is
begin
   case I is

      when 11 =>
         declare
            -- A character from the ASCII range (0 .. 127)
            X : Character := ASCII.SOH;
         begin
            pragma Assert (X = 'B');
         end;

      when 12 =>
         declare
            -- A character from the Latin-1 Supplement block (128 .. 255)
            X : Character := Character'Val (233); -- LC_E_Acute
         begin
            pragma Assert (X = 'B');
         end;

      when 13 =>
         declare
            -- A character from the Latin-1 Supplement block (128 .. 255)
            X : Character := 'é'; -- LC_E_Acute
         begin
            pragma Assert (X = 'B');
         end;

      when 21 =>
         declare
            X : String := ASCII.SOH & Character'Val (233);
         begin
            pragma Assert (X = "");
         end;

      when 22 =>
         declare
            X : String := String'(1 => ASCII.SOH, 2 => Character'Val (233));
         begin
            pragma Assert (X = "");
         end;

      when 23 =>
         declare
            X : String := (1 => ASCII.SOH, 2 => Character'Val (233));
         begin
            pragma Assert (X = "");
         end;

      when others =>
         null;

   end case;
end;
