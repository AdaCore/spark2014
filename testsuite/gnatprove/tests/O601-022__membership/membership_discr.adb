procedure Membership_Discr with SPARK_Mode is
   type Root (C : Natural) is tagged null record;
   type Root_01 is new Root (0) with null record;
   subtype Root_02 is Root (0);
   type Child is new Root with null record;
   type Child_01 is new Root_01 with null record;
   type Child_02 is new Root_02 with null record;
   type Child_03 is new Child (0) with null record;
   subtype Child_04 is Child (0);

   procedure Bad_1 with Pre => True is
      R1  : Root (1);
   begin
      pragma Assert (Root'Class (R1) in Root_02); --@ASSERT:FAIL
   end Bad_1;

   procedure Bad_2 with Pre => True is
      R01 : Root_01;
   begin
      pragma Assert (R01 in Root_01); -- OK
      pragma Assert (Root'Class (R01) in Root_02); --@ASSERT:FAIL
   end Bad_2;

   procedure Bad_3 with Pre => True is
      R02 : Root_02;
   begin
      pragma Assert (R02 in Root); -- OK
      pragma Assert (Root'Class (R02) in Root_01); --@ASSERT:FAIL
   end Bad_3;

   R00 : Root (0);
   C00 : Child (0);
   C01 : Child_01;
   C02 : Child_02;
   C03 : Child_03;
begin
   pragma Assert (R00 in Root); -- OK
   pragma Assert (Root'Class (R00) in Root_02); -- OK
   pragma Assert (C00 in Child); -- OK
   pragma Assert (Child'Class (C00) in Child_04); -- OK
end Membership_Discr;
