procedure P (I : Integer) is
begin
   case I is

      when 1 =>
         declare
            X : String := ASCII.SOH & "";
         begin
            pragma Assert (X /= X);
         end;

      when 2 =>
         declare
            X : String := String'(1 => ASCII.SOH);
         begin
            pragma Assert (X /= X);
         end;

      when 3 =>
         declare
            X : String := (1 => ASCII.SOH);
         begin
            pragma Assert (X /= X);
         end;

      when others =>
         null;

   end case;
end;
