package body Tagged_Conv with SPARK_Mode is

   procedure P is
      C : constant Child := (others => <>);
      R : constant Root := (others => <>);
      CC : constant Root'Class := C;
      RC : constant Root'Class := R;

      procedure Conv_Child_To_Root_Ok with Pre => True is
         R2 : Root := Root (C);
         RC2 : Root'Class := Root'Class (R2);
         CC2 : Child := Child (CC);  --@TAG_CHECK:PASS
      begin
         null;
      end Conv_Child_To_Root_Ok;

      procedure Conv_Root_To_Child_Ok with Pre => True is
         RC2 : Root := Root (RC);
         CC2 : Root := Root (CC);
         CC3 : Root'Class := Root'Class (CC2);
      begin
         null;
      end Conv_Root_To_Child_Ok;

      procedure Bad1 with Pre => True is
         RC2 : Child'Class := Child'Class (RC);  --@TAG_CHECK:FAIL
      begin
         null;
      end Bad1;

      procedure Bad2 with Pre => True is
         RC3 : Child := Child (RC);  --@TAG_CHECK:FAIL
      begin
         null;
      end Bad2;

      procedure Bad3 with Pre => True is
         RC2 : Root := Root (RC);
         RC3 : Root'Class := Root'Class (RC);
         RC4 : Child := Child (RC3);  --@TAG_CHECK:FAIL
      begin
         null;
      end Bad3;

      procedure Bad4 with Pre => True is
         R2 : Root := Root (C);
         RC2 : Root'Class := Root'Class (R2);
         C3 : Child := Child (RC2);  --@TAG_CHECK:FAIL
      begin
         null;
      end Bad4;

      procedure Bad5 with Pre => True is
         CC2 : Root := Root (CC);
         CC3 : Root'Class := Root'Class (CC2);
         CC4 : Child := Child (CC3); --@TAG_CHECK:FAIL
      begin
         null;
      end Bad5;
   begin
      Conv_Child_To_Root_Ok;
      Conv_Root_To_Child_Ok ;
      Bad1;
      Bad2;
      Bad3;
      Bad4;
      Bad5;
   end P;

end Tagged_Conv;
