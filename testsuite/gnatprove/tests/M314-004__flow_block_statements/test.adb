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

   procedure Parallel_Block_Statements (Operation: Integer ; X, Y : in out Integer) is
   begin
      case Operation is
         when 1 =>
            declare
               temp1, temp2 : Integer;
            begin
               temp1 := X + Y;
               temp2 := X - Y;
               X := temp1;
               Y := temp2;
            end;
         when 2 =>
           declare
               temp1, temp2 : Integer;
            begin
               temp1 := X * Y;
               temp2 := X / Y;
               X := temp1;
               Y := temp2;
            end;
         when 3 =>
           declare
               temp1, temp2 : Integer;
            begin
               temp1 := X mod Y;
               temp2 := X rem Y;
               X := temp1;
               Y := temp2;
            end;
         when others =>
            null;
      end case;
   end Parallel_Block_Statements;

   procedure Nested_Block_Statements (X, Y : in out Integer) is
   begin
      declare
         temp : Integer := X;
      begin
         declare
            temp : Integer := Y;
         begin
            X := X * temp;
         end;
         Y := Y * temp;
      end;
      pragma Assert (X = Y);
   end Nested_Block_Statements;
end Test;
