package body Test is
   type Table_T is array (Positive range 1 .. 9) of Integer;

   procedure QE_1 (Table : in out Table_T) is
   begin
      for I in reverse 1 .. 9 loop
	 Table (10 - I) := I;
      end loop;
      pragma Assert (for some X in 1 .. 9 => X = Table (X));
      if (for all X in 1 .. 9 => Table (X) > 0) then
         Table (5) := 0;
      end if;
   end QE_1;

   procedure QE_2 (Table : in out Table_T) is
   begin
      QE_1 (Table);

      declare
         Temp_Table : Table_T;
      begin
         for I in 1 .. 9 loop
            Temp_Table (I) := I;
         end loop;

         pragma Assert (for all X in 1 .. 9 => Table (X) /= Temp_Table (X));
      end;
   end QE_2;
end Test;
