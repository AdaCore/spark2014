procedure Test_Alias with SPARK_Mode is
   X : aliased Integer := 10 with Alignment => 4;
   Y : aliased Integer with Import, Alignment => 4, Address => X'Address;

   function Rand (X : Integer) return Boolean with Import;
   procedure Set (I : Integer; X : in out Integer) with Import;
   procedure Set_X (I : Integer) with Import,
     Global => (In_Out => X);
begin
   if Rand (0) then
      for I in 1 .. 100 loop
         pragma Assert (Y = Y'Loop_Entry); --@ASSERT:FAIL
         X := I;
      end loop;
   elsif Rand (1) then
      for I in 1 .. 100 loop
         pragma Assert (Y = Y'Loop_Entry); --@ASSERT:FAIL
         Set (I, X);
      end loop;
   elsif Rand (2) then
      for I in 1 .. 100 loop
         pragma Assert (Y = Y'Loop_Entry); --@ASSERT:FAIL
         Set_X (I);
      end loop;
   elsif Rand (3) then
      for I in 1 .. 100 loop
         pragma Assert (Y = Y'Loop_Entry); --@ASSERT:FAIL
         declare
            Z : aliased Integer with Import, Alignment => 4, Address => X'Address;
         begin
            Z := 15;
         end;
      end loop;
   elsif Rand (4) then
      for I in 1 .. 100 loop
         pragma Assert (Y = Y'Loop_Entry); --@ASSERT:FAIL
         declare
            Z : aliased Integer := 6 with Alignment => 4, Address => X'Address;
         begin
            null;
         end;
      end loop;
   elsif Rand (5) then
      for I in 1 .. 100 loop
         pragma Assert (Y = Y'Loop_Entry); --@ASSERT:PASS
         declare
            Z : aliased Integer with Import, Alignment => 4, Address => X'Address;
         begin
            null;
         end;
      end loop;
   end if;
end Test_Alias;
