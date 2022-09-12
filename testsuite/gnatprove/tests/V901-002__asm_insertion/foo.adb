with Interfaces.C; use Interfaces.C;
with System.Machine_Code; use System.Machine_Code;

package body Foo with SPARK_Mode => On is

   procedure Add4 is
   begin
      Asm_Insn'(Asm ("addl $4, -4(%%rbp)", Volatile=>True));
   end;

   function Check (Input : Eight_Byte_Array) return Natural  is
      Result : Natural := 0;
   begin
      for I in Input'Range loop
          pragma Loop_Invariant (Result >= 0 and then Result < 4);
         if Input(I) /= Character'Pos ('0') then
            Result := Result + 1;
            if Result = 4 then
                Result := Result - 1;
            end if;
         end if;
      end loop;
      pragma Assert (Result >= 0 and then Result < 4);
      Asm ("addl $4, -4(%%rbp)", Volatile=>True);
      return Result;
   end Check;
end Foo;
