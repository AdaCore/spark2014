package body Max is

   function Max (Left, Right : Float) return Float is
   begin
      return (if Right > Left then Right else Left);
   end Max;

end Max;
