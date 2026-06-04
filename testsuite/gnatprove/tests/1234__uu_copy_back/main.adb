procedure Main with SPARK_Mode is

   type R_B (B : Boolean := True) is record
      case B is
         when True =>
            F : Integer;
         when False =>
            G : integer;
      end case;
   end record;

   type R_UU is new R_B with Unchecked_Union;

   procedure Test (X : in out R_UU) with
     Pre => (Static => not X'Constrained);

   procedure Test (X : in out R_UU) is
   begin
      X := (False, G => 12);
   end Test;

   procedure Call_In (X : in out R_B) is
   begin
      Test (R_UU (X)); --  @UU_RESTRICTION:FAIL
   end Call_In;

   X : R_B := (True, 42);
begin
   Call_In (X);
end Main;
