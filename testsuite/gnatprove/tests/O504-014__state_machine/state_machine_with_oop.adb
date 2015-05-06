package body State_Machine_With_Oop with SPARK_Mode is
   function Move_To_A (Current : State_A) return Root_State'Class is
   begin
      raise Program_Error;
      return Current;
   end Move_To_A;
   function Move_To_B (Current : State_A) return Root_State'Class is
   begin
      return State_B'(Common_Value => Current.Common_Value);
   end Move_To_B;
   function Move_To_C (Current : State_A) return Root_State'Class is
   begin
      return State_C'(Common_Value => Current.Common_Value,
                      Value_For_C  => Current.Value_For_A);
   end Move_To_C;
   procedure Stay_Here (Current : in out State_A) is
   begin
      raise Program_Error;
   end Stay_Here;

   function Move_To_A (Current : State_B) return Root_State'Class is
   begin
      raise Program_Error;
      return Current;
   end Move_To_A;
   function Move_To_B (Current : State_B) return Root_State'Class is
   begin
      raise Program_Error;
      return Current;
   end Move_To_B;
   function Move_To_C (Current : State_B) return Root_State'Class is
   begin
      raise Program_Error;
      return Current;
   end Move_To_C;
   procedure Stay_Here (Current : in out State_B) is
   begin
      if Can_Increase_Value (Current) then
         Current.Common_Value := Current.Common_Value + 1;
      end if;
   end Stay_Here;

   function Move_To_A (Current : State_C) return Root_State'Class is
   begin
      return State_A'(Common_Value => Current.Common_Value,
                      Value_For_A  => Current.Value_For_C);
   end Move_To_A;
   function Move_To_B (Current : State_C) return Root_State'Class is
   begin
      raise Program_Error;
      return Current;
   end Move_To_B;
   function Move_To_C (Current : State_C) return Root_State'Class is
   begin
      raise Program_Error;
      return Current;
   end Move_To_C;
   procedure Stay_Here (Current : in out State_C) is
   begin
      Current.Common_Value := Current.Common_Value + 1;
   end Stay_Here;

   procedure Do_Something (States : in out State_Vectors.Vector) is
      use State_Vectors;
   begin
      for I in First_Index (States) .. Last_Index (States) loop
         pragma Loop_Invariant
           (Last_Index (States) = Last_Index (States)'Loop_Entry);
         declare
            E : Root_State'Class := Element (States, I);
         begin
            if Can_Move_To_A (E) then
               Replace_Element (States, I, Move_To_A (E));
            elsif Can_Move_To_B (E) then
               Replace_Element (States, I, Move_To_B (E));
            elsif Can_Move_To_C (E) then
               Replace_Element (States, I, Move_To_C (E));
            else
               Stay_Here (E);
               Replace_Element (States, I, E);
            end if;
         end;
      end loop;
   end Do_Something;
end State_Machine_With_Oop;
