package body Globals with
  SPARK_Mode,
  Refined_State => (State_X => X, State_Y => Y)
is
   Y : T;

   procedure Create is  --  @INVARIANT_CHECK:NONE
   begin
      X := 1;  --  @INVARIANT_CHECK:NONE
   end Create;

   procedure Update is  --  @INVARIANT_CHECK:NONE
   begin
      if X /= T'First then
         X := abs (X);  --  @INVARIANT_CHECK:NONE
      end if;
   end Update;

   function Get return Integer is (Integer (X));

   procedure Abs_Create is
   begin
      Y := 1;  --  @INVARIANT_CHECK:NONE
   end Abs_Create;

   procedure Abs_Update is
   begin
      if Y /= T'First then
         Y := abs (Y);  --  @INVARIANT_CHECK:NONE
      end if;
   end Abs_Update;

   function Abs_Get return Integer is (Integer (Y));

   procedure Gen_Create is
   begin
      X := 1;  --  @INVARIANT_CHECK:NONE
   end Gen_Create;

   procedure Gen_Update is
   begin
      if X /= T'First then
         X := abs (X);  --  @INVARIANT_CHECK:NONE
      end if;
   end Gen_Update;

   function Gen_Get return Integer is (Integer (X));

   procedure Abs_Gen_Create is
   begin
      Y := 1;  --  @INVARIANT_CHECK:NONE
   end Abs_Gen_Create;

   procedure Abs_Gen_Update is
   begin
      if Y /= T'First then
         Y := abs (Y);  --  @INVARIANT_CHECK:NONE
      end if;
   end Abs_Gen_Update;

   function Abs_Gen_Get return Integer is (Integer (Y));

end Globals;
