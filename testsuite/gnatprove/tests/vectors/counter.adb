package body Counter is

   Count : Natural := 0;

   function Bump_Counter return Positive is
      pragma SPARK_Mode (Off);  --  function with side-effect
   begin
      Count := Count + 1;
      return Count;
   end Bump_Counter;

end Counter;
