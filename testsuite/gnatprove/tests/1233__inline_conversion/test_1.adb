procedure Test_1 is
   type R is record
      F : Integer;
   end record;

   type R_Pos is new R with Predicate => R_Pos.F > 0;

   procedure Test_In (X : in out R_Pos);

   procedure Test_In (X : in out R_Pos) is null;

   procedure Call_In (X : in out R) is
   begin
      Test_In (R_Pos (X)); --  @PREDICATE_CHECK:FAIL
   end Call_In;
begin
   null;
end Test_1;
