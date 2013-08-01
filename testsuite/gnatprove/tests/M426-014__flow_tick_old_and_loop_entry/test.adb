package body Test
is

   procedure Test_01 (X : out Integer)
   is
   begin
      for I in Integer range 1 .. 10 loop
         X := 0;
         pragma Loop_Invariant (X = X'Loop_Entry);  --  uninitialized
      end loop;
   end Test_01;

   procedure Test_02 (X : out Integer)
   is
   begin
      Wibble: for I in Integer range 1 .. 10 loop
         X := 0;
         pragma Loop_Invariant (X = X'Loop_Entry (Wibble));  --  uninitialized
      end loop Wibble;
   end Test_02;

   procedure Test_03 (X : out Integer)
   is
   begin
      Wibble: for I in Integer range 1 .. 10 loop
         X := 0;
         for J in Integer loop
            pragma Loop_Invariant (X = X'Loop_Entry (Wibble));  --  uninitialized
            null;
         end loop;
      end loop Wibble;
   end Test_03;

   procedure Test_04 (X : out Integer)
   is
   begin
      Wibble: for I in Integer range 1 .. 10 loop
         X := 0;
         for J in Integer loop
            pragma Loop_Invariant (X = X'Loop_Entry);  --  OK
            null;
         end loop;
         pragma Loop_Invariant (X = X'Loop_Entry);  --  uninitialized
      end loop Wibble;
   end Test_04;

   procedure Test_05 (X : out Integer)
   is
   begin
      for I in Integer range 1 .. 10 loop
         X := 0;
         pragma Loop_Variant (Increases => X'Loop_Entry);  --  uninitialized
      end loop;
   end Test_05;

   procedure Test_06 (X : out Integer)
   is
   begin
      for I in Integer range 1 .. 10 loop
         X := 0;
         pragma Assert (X'Loop_Entry = 0);  --  uninitialized
      end loop;
   end Test_06;

end Test;
