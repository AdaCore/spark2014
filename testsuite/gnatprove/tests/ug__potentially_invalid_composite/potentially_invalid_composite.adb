procedure Potentially_Invalid_Composite with SPARK_Mode is

   type R is record
      F, G : Positive;
   end record;

   procedure P (X : in out R; Y : out R) with
      Global => null,
      Potentially_Invalid => (X, Y)
   is
   begin
      X.F := 12;
      pragma Assert (X.F'Valid);
      Y.F := 12;
      Y.G := 13;
      pragma Assert (Y'Valid_Scalars);
   end P;

begin
  null;
end;
