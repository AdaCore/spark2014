package SM_Types
  with SPARK_Mode
is

   -- These are the system states. Try adding a new
   -- state or removing an original state to see
   -- how the tools may detect such an error.
   type States_T is (Start, Progress, Finish, Invalid_State);
--   type States_T is (Start, Progress, Finish, Invalid_State);

   -- These are the system triggers. Try adding a new
   -- trigger or removing an original trigger to see
   -- how the tools may detect such an error.
   type Triggers_T is (Btn_Pressed, Btn_Released, Btn_Start, Btn_Finish, Invalid_Trigger);

end SM_Types;
