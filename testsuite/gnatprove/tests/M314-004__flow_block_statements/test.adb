package body Test is
   procedure Compare_And_Swap (X, Y : in out Integer) is
   begin
      if Y > X then 
         Swap:
            declare
               Temp : Integer;
            begin
               Temp := X; X := Y; Y := Temp;
            end Swap;
      end if;
   end Compare_And_Swap;
end Test;
