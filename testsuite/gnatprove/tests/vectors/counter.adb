package body Counter is

   Count : Natural := 0;

   function Bump_Counter return Positive is
   begin
      Count := Count + 1;
      return Count;
   end Bump_Counter;

end Counter;
