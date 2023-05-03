pragma Ada_2022;
procedure Iter
  with SPARK_Mode
is
   function Get (I : Positive) return Character is
      X : Positive;
   begin
      X := I + 1;
      return ' ';
   end Get;

   S : String := (for I in 1 .. 15 => Get (I));
begin
   null;
end;
