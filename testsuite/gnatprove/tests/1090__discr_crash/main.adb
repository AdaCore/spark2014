procedure Main
  with SPARK_Mode => On
is
   type Index_Type is range 1 .. 10;

   type Ar is array (Index_Type range <>) of Integer;

   type State_T (F, L : Index_Type) is record
      Sources : Ar (F .. L);
   end record;

   procedure Update (State_Before : State_T;
                     State_After  : out State_T)
   is
   begin
      State_After.Sources := State_Before.Sources; --@LENGTH_CHECK:FAIL
   end;

   procedure Update_2 (State_Before : State_T;
                       State_After  : out State_T) with
     Pre => State_Before.L >= State_Before.F
       and State_Before.L - State_Before.F = State_After.L - State_After.F;

   procedure Update_2 (State_Before : State_T;
                       State_After  : out State_T)
   is
   begin
      State_After.Sources := State_Before.Sources; --@LENGTH_CHECK:PASS
      pragma Assert (State_After.Sources (State_After.F) = State_Before.Sources (State_Before.F)); --@ASSERT:PASS
   end;

begin
  null;
end;
