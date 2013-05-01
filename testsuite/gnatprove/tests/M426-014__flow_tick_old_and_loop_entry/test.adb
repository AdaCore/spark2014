package body Test
is

   procedure Test_01 (X : out Integer;
                      Y : Boolean;
                      A : Integer)
   is
   begin
      if Y then
         X := A;
      end if;

      for I in Integer range 1 .. 10 loop
         X := 0;
         X := X + 1;
         pragma Loop_Invariant (X = X'Loop_Entry + I);  --  uninitialized
         pragma Loop_Variant (Increases => X);
      end loop;
   end Test_01;

end Test;
