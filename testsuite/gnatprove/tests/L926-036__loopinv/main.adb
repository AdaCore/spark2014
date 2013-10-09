with Ada.Text_IO; use Ada.Text_IO;
with Counters;    use Counters;

procedure Main is
   pragma SPARK_Mode (Off);  --  exception handlers

   function Factorial (Val : Natural) return Natural;
   --  Val!

   ---------------
   -- Factorial --
   ---------------

   function Factorial (Val : Natural) return Natural is
   begin
      if Val = 1 then
         return 1;
      else
         return Factorial (Val - 1) * Val;
      end if;
   end Factorial;

--  Start of processing for Main

begin
   --  Check invariant

   begin
      for J in 1 .. 2 loop
         pragma Loop_Invariant (Factorial (3) = 6);
         null;
      end loop;
      Put_Line ("OK 1");
   exception
      when others =>
         Put_Line ("ERROR 1: should not raise exception");
   end;

   --  Check invariant

   begin
      for J in 1 .. 2 loop
         pragma Loop_Invariant (Factorial (2) = 123);
         Put_Line ("ERROR 2: should not get here");
      end loop;
   exception
      when others => Put_Line ("OK 2");
   end;

   --  Check increases (all values increase)

   declare
      C1 : Counter (Increase, 3);
      C2 : Counter (Increase, 3);
      C3 : Counter (Increase, 3);
   begin
      for J in 1 .. 3 loop
         Tick (C1);
         Tick (C2);
         Tick (C3);

         pragma Loop_Variant
           (Increases => Value (C1),
            Increases => Value (C2),
            Increases => Value (C3));
      end loop;
      Put_Line ("OK 3");
   exception
      when others =>
         Put_Line ("ERROR 3: should not raise exception");
   end;

   --  Check increase (all values increase, last decreases on iteration 2)

   declare
      C1 : Counter (Increase, 3);
      C2 : Counter (Increase, 3);
      C3 : Counter (Increase_Then_Decrease, 2);
   begin
      for J in 1 .. 3 loop
         Put_Line ("Test 4, iteration:" & J'Img);

         Tick (C1);
         Tick (C2);
         Tick (C3);

         pragma Loop_Variant
           (Increases => Value (C1),
            Increases => Value (C2),
            Increases => Value (C3));
      end loop;
      Put_Line ("OK 4");
   exception
      when others =>
         Put_Line ("ERROR 4: should not raise exception");
   end;

   --  Check increase (first one decreases on iteration 2, all other increase)

   declare
      C1 : Counter (Increase_Then_Decrease, 2);
      C2 : Counter (Increase, 3);
      C3 : Counter (Increase, 3);
   begin
      for J in 1 .. 3 loop
         Put_Line ("Test 5, iteration:" & J'Img);

         Tick (C1);
         Tick (C2);
         Tick (C3);

         pragma Loop_Variant
           (Increases => Value (C1),
            Increases => Value (C2),
            Increases => Value (C3));
      end loop;
      Put_Line ("ERROR 5: should not get here");
   exception
      when others => Put_Line ("OK 5");
   end;

   --  Check increase (first remains the same, second one decreases on
   --                  iteration 2, last one increases)

   declare
      C1 : Counter (Same, 3);
      C2 : Counter (Increase_Then_Decrease, 2);
      C3 : Counter (Increase, 3);
   begin
      for J in 1 .. 3 loop
         Put_Line ("Test 6, iteration:" & J'Img);

         Tick (C1);
         Tick (C2);
         Tick (C3);

         pragma Loop_Variant
           (Increases => Value (C1),
            Increases => Value (C2),
            Increases => Value (C3));
      end loop;
      Put_Line ("ERROR 6: should not get here");
   exception
      when others => Put_Line ("OK 6");
   end;

   --  Check increase (first two remain the same, last one decreases on
   --                  iteration 2)

   declare
      C1 : Counter (Same, 3);
      C2 : Counter (Same, 3);
      C3 : Counter (Increase_Then_Decrease, 2);
   begin
      for J in 1 .. 3 loop
         Put_Line ("Test 7, iteration:" & J'Img);

         Tick (C1);
         Tick (C2);
         Tick (C3);

         pragma Loop_Variant
           (Increases => Value (C1),
            Increases => Value (C2),
            Increases => Value (C3));
      end loop;
      Put_Line ("ERROR 7: should not get here");
   exception
      when others => Put_Line ("OK 7");
   end;

   --  Check decrease (all values decrease)

   declare
      C1 : Counter (Decrease, 3);
      C2 : Counter (Decrease, 3);
      C3 : Counter (Decrease, 3);
   begin
      for J in 1 .. 3 loop
         Tick (C1);
         Tick (C2);
         Tick (C3);

         pragma Loop_Variant
           (Decreases => Value (C1),
            Decreases => Value (C2),
            Decreases => Value (C3));
      end loop;
      Put_Line ("OK 8");
   exception
      when others =>
         Put_Line ("ERROR 8: should not raise exception");
   end;

   --  Check decrease (all values decrease, last increases on iteration 2)

   declare
      C1 : Counter (Decrease, 3);
      C2 : Counter (Decrease, 3);
      C3 : Counter (Decrease_Then_Increase, 2);
   begin
      for J in 1 .. 3 loop
         Put_Line ("Test 9, iteration:" & J'Img);

         Tick (C1);
         Tick (C2);
         Tick (C3);

         pragma Loop_Variant
           (Decreases => Value (C1),
            Decreases => Value (C2),
            Decreases => Value (C3));
      end loop;
      Put_Line ("OK 9");
   exception
      when others =>
         Put_Line ("ERROR 9: should not raise exception");
   end;

   --  Check decrease (first one increases on iteration 2, all other decrease)

   declare
      C1 : Counter (Decrease_Then_Increase, 2);
      C2 : Counter (Decrease, 3);
      C3 : Counter (Decrease, 3);
   begin
      for J in 1 .. 3 loop
         Put_Line ("Test 10, iteration:" & J'Img);

         Tick (C1);
         Tick (C2);
         Tick (C3);

         pragma Loop_Variant
           (Decreases => Value (C1),
            Decreases => Value (C2),
            Decreases => Value (C3));
      end loop;
      Put_Line ("ERROR 10: should not get here");
   exception
      when others => Put_Line ("OK 10");
   end;

   --  Check decrease (first demains the same, second one increases on
   --                  iteration 2, last one decreases)

   declare
      C1 : Counter (Same, 3);
      C2 : Counter (Decrease_Then_Increase, 2);
      C3 : Counter (Decrease, 3);
   begin
      for J in 1 .. 3 loop
         Put_Line ("Test 11, iteration:" & J'Img);

         Tick (C1);
         Tick (C2);
         Tick (C3);

         pragma Loop_Variant
           (Decreases => Value (C1),
            Decreases => Value (C2),
            Decreases => Value (C3));
      end loop;
      Put_Line ("ERROR 11: should not get here");
   exception
      when others => Put_Line ("OK 11");
   end;

   --  Check decrease (first two remain the same, last one increases on
   --                  iteration 2)

   declare
      C1 : Counter (Same, 3);
      C2 : Counter (Same, 3);
      C3 : Counter (Decrease_Then_Increase, 2);
   begin
      for J in 1 .. 3 loop
         Put_Line ("Test 12, iteration:" & J'Img);

         Tick (C1);
         Tick (C2);
         Tick (C3);

         pragma Loop_Variant
           (Decreases => Value (C1),
            Decreases => Value (C2),
            Decreases => Value (C3));
      end loop;
      Put_Line ("ERROR 12: should not get here");
   exception
      when others => Put_Line ("OK 12");
   end;

   --  Check mixed (all remain the same)

   declare
      C1 : Counter (Same, 3);
      C2 : Counter (Same, 3);
      C3 : Counter (Same, 3);
   begin
      for J in 1 .. 3 loop
         Put_Line ("Test 13, iteration:" & J'Img);

         Tick (C1);
         Tick (C2);
         Tick (C3);

         pragma Loop_Variant
           (Increases => Value (C1),
            Decreases => Value (C2),
            Increases => Value (C3));
      end loop;
      Put_Line ("ERROR 13: should not get here");
   exception
      when others => Put_Line ("OK 13");
   end;
end Main;
