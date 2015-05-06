package body State_Machine_With_Discriminant with SPARK_Mode is

   procedure Move_To_A (Current : in out State) is
   begin
      Current := (A, Current.Common_Value, Current.Value_For_C);
   end Move_To_A;

   procedure Move_To_B (Current : in out State) is
   begin
      Current := (B, Current.Common_Value);
   end Move_To_B;

   procedure Move_To_C (Current : in out State) is
   begin
      Current := (C, Current.Common_Value, Current.Value_For_A);
   end Move_To_C;

   procedure Stay_Here (Current : in out State) is
   begin
      if Current.Kind = C or else Can_Increase_Value (Current) then
         Current.Common_Value := Current.Common_Value + 1;
      end if;
   end Stay_Here;

   procedure Do_Something (States : in out State_Array) is
   begin
      for I in States'Range loop
         if Can_Move_To_A (States (I)) then
            Move_To_A (States (I));
         elsif Can_Move_To_B (States (I)) then
            Move_To_B (States (I));
         elsif Can_Move_To_C (States (I)) then
            Move_To_C (States (I));
         else
            Stay_Here (States (I));
         end if;
      end loop;
   end Do_Something;
end State_Machine_With_Discriminant;
