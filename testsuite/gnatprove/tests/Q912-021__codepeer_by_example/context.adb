with Assign_Arr; use Assign_Arr;
procedure Context is
   X : Arr;
   procedure Local is
   begin
      for J in X'Range loop
         X (J) := X (J) + 1;
      end loop;
   end Local;
begin
   X := (others => 1);
   Local;
end Context;
