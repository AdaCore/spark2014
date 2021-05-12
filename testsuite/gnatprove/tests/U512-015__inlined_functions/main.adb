procedure Main with SPARK_Mode is
   type My_Rec is record
      X : Integer;
   end record;

   function Create return My_Rec with Relaxed_Initialization => Create'Result;
   function Create return My_Rec is
      X : My_Rec with Relaxed_Initialization;
   begin
      return X; --@INIT_BY_PROOF:FAIL
   end Create;

   function Create2 return My_Rec with Pre => True, Relaxed_Initialization => Create2'Result;
   function Create2 return My_Rec is
      X : My_Rec with Relaxed_Initialization;
   begin
      return X;
   end Create2;

   function Create3 return My_Rec with Relaxed_Initialization => Create3'Result;
   function Create3 return My_Rec is
      X : My_Rec with Relaxed_Initialization;
   begin
      return X; --Should be OK, as the call of Create3 occurs in a variable with relaxed init
   end Create3;

   X : My_Rec := Create;
   Y : My_Rec := Create2; --@INIT_BY_PROOF:FAIL
   W : My_Rec := Create2 with Relaxed_Initialization;
   Z : My_Rec := Create3 with Relaxed_Initialization;
begin
   null;
end Main;
