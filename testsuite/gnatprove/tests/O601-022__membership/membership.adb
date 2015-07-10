procedure Membership with SPARK_Mode is
   type Root is tagged null record;
   type Child is new  Root with null record;
   type Grand_Child is new Child with null record;
   type Brother is new Root with null record;

   procedure Bad1 with Pre => True is
      R : Root;
   begin
      pragma Assert (Root'Class (R) in Root);
      pragma Assert (Root'Class (R) in Child); --@ASSERT:FAIL
   end Bad1;

   procedure Bad2 with Pre => True is
      B : Brother;
   begin
      pragma Assert (Root'Class (B) in Child); --@ASSERT:FAIL
   end Bad2;

   procedure Bad3 with Pre => True is
      C : Child;
   begin
      pragma Assert (Root'Class (C) in Root); --@ASSERT:FAIL
   end Bad3;

   procedure Bad4 with Pre => True is
      G : Grand_Child;
   begin
      pragma Assert (Child'Class (G) in Child); --@ASSERT:FAIL
   end Bad4;

   procedure Bad5 with Pre => True is
      B : Brother;
   begin
      pragma Assert (Root'Class (B) in Root); --@ASSERT:FAIL
   end Bad5;

   procedure Bad6 with Pre => True is
      B : Brother;
   begin
      pragma Assert (Root'Class (B) in Root | Child | Grand_Child); --@ASSERT:FAIL
   end Bad6;

   C : Child;
   G : Grand_Child;
begin
   pragma Assert (Child'Class (C) in Child); --@ASSERT:PASS
   pragma Assert (Root'Class (G) in Grand_Child); --@ASSERT:PASS
   pragma Assert (Root'Class (C) in Root | Child | Grand_Child); --@ASSERT:PASS
end Membership;
