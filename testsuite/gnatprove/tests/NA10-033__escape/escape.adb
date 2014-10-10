package body Escape
   with SPARK_Mode
is

   function Backslash_Escape (S : String) return String is
      Count_Bs : Natural := 0;
   begin
      for I in S'Range loop
         if S (I) = '\' then
            Count_Bs := Count_Bs + 1;
         end if;
      end loop;
      declare
         Len    : constant Natural := S'Length + Count_Bs;
         Result : String (1 .. Len);
         TI     : Positive := 1;
      begin
         for I in S'Range loop
            Result (TI) := S (I);
            TI := TI + 1;
            if S (I) = '\' then
               Result (TI) := '\';
               TI := TI + 1;
            end if;
         end loop;
         return Result;
      end;
   end Backslash_Escape;


end Escape;
