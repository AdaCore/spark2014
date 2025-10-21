procedure Main
  with SPARK_Mode => On
is
   type Index_Type is range 1 .. 10;

   type Ar is array (Index_Type range <>) of Integer;

   type D_Enum is (A, B);

   type State_T (F, L : Index_Type) is record
      Sources : Ar (F .. L);
   end record;

   procedure Update (State_Before : State_T;
                     State_After  : out State_T)
   is
   begin
      State_After.Sources := State_Before.Sources;
   end;

begin
  null;
end;
