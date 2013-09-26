procedure Dyn is
   function F return Integer is (1);
   X : String (F .. F) := (F - 1 => '0');
begin
   null;
end Dyn;
