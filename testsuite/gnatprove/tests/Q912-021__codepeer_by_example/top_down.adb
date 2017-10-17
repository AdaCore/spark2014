with Assign_Arr; use Assign_Arr;
procedure Top_Down (Y : out Integer) is
   A : Arr := (others => 1);
   function Ident (X : Integer) return Integer is
   begin
      if A (X) > 0 then
         return X;
      else
         return 0;
      end if;
   end Ident;
begin
   Y := A (Ident (3));
end Top_Down;

