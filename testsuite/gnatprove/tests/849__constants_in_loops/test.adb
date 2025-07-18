procedure Test with SPARK_Mode is

   procedure Test_1 with Global => null is
   begin
      for I in 1 .. 100 loop
         pragma Loop_Invariant (True);
         declare
            C : constant Integer := I;
         begin
            pragma Assert (C = I); --  No warning, C is declared after the invariant
         end;
      end loop;
   end Test_1;

   procedure Test_2 with Global => null is
   begin
      for I in 1 .. 100 loop
         declare
            C : constant Integer := I;
         begin
            pragma Loop_Invariant (True);
            pragma Assert (C = I); --  No warning, C is declared just before the invariant
         end;
      end loop;
   end Test_2;

   procedure Test_3 with Global => null is
      V : Integer;
   begin
      for I in 1 .. 100 loop
         declare
            C : constant Integer := I;
         begin
            V := C;
            pragma Assert (C = I); --  No warning, C is unused after the invariant
            pragma Loop_Invariant (True);
         end;
      end loop;
   end Test_3;

   procedure Test_4 with Global => null is
      V : Integer;
   begin
      for I in 1 .. 100 loop
         declare
            C : constant Integer := I;
         begin
            V := C;
            pragma Assert (C = I); --  No warning, C is before the implicit invariant
         end;
      end loop;
   end Test_4;

   procedure Test_5 with Global => null is
      V : Integer;
   begin
      for I in 1 .. 100 loop
         declare
            C : constant Integer := I;
         begin
            V := C;
            pragma Loop_Invariant (True);
            pragma Assert (C = I);  -- @ASSERT:FAIL Warning, the value of C is imprecisely known at this point
         end;
      end loop;
   end Test_5;

   procedure Test_6 with Global => null is
      V : Integer;
   begin
      for I in 1 .. 100 loop
         declare
            C : constant Integer := I;
         begin
            V := C;
            pragma Loop_Invariant (True);

            for J in 1 .. 100 loop
               declare
                  D : constant Integer := J;
               begin
                  V := D;
                  pragma Loop_Invariant (True);
                  pragma Assert (C = I);  -- @ASSERT:FAIL Warning, the value of C is imprecisely known at this point
                  pragma Assert (D = J);  -- @ASSERT:FAIL Warning, the value of C is imprecisely known at this point
               end;
            end loop;
         end;
      end loop;
   end Test_6;

begin
   null;
end;
