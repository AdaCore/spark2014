procedure Nested_Loops_Frame_Condition with SPARK_Mode is
   X : Integer := 0;
   Y : Integer := 0;
   Seed : Integer := 0;
   procedure Twist
     with Import, Global => (In_Out => Seed),
     Always_Terminates;
   function Random (I : Integer := 0) return Boolean
     with Import, Global => (Input => Seed);
begin

   while Random loop
      Twist;
      pragma Loop_Invariant (True);
      while Random loop
         Twist;
         pragma Loop_Invariant (True);
         X := X + 1; --@OVERFLOW_CHECK:FAIL
         if Random then
            Twist;
            goto L;
            Twist;
         end if;
      end loop;
      Twist;
      return;
      <<L>>
   end loop;
   Twist;

   while Random loop
      Twist;
      pragma Loop_Invariant (True);
      if Random then
         Twist;
         while Random loop
            Twist;
            pragma Loop_Invariant (True);
            Y := Y + 1; --@OVERFLOW_CHECK:FAIL
         end loop;
         Twist;
         return;
         Twist;
      end if;
      Twist;
      pragma Assert (Y = 0);
   end loop;
   Twist;

end Nested_Loops_Frame_Condition;
