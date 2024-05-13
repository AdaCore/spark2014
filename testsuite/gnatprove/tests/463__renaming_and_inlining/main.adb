procedure Main with SPARK_Mode is

   type TA is array (1 .. 5) of Integer;

   function PROC1 (A : Integer := 1; B : TA := (1 .. 5 => 1)) return Integer is
   begin
      for I in 1 .. 5 loop
         if A = B (I) then
            null; --return I;
         end if;
      end loop;
      return 0;
   end PROC1;

   function PROCA
     (C : Integer := 1; D : TA := (1 .. 5 => 1)) return Integer renames
     PROC1;

begin

   if PROCA /= 1 then
      null;
   end if;
end Main;
