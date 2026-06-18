package body Ext with SPARK_Mode is

   protected body T_1 is
      procedure P_Nested (X : in out R) with Modifies => X.F;

      procedure P (X : in out R) is
         procedure P_Nested_2 (X : in out R) with Modifies => X.F;

         procedure P_Nested_2 (X : in out R) is
         begin
            X.F := C;
            C := 1;
         end P_Nested_2;
      begin
         X.F := C;
         C := 1;
      end P;

      procedure P_Nested (X : in out R) is
      begin
         X.F := C;
         C := 1;
      end P_Nested;
   end T_1;

   protected body P is
      procedure P_Nested (X : in out R) with Modifies => X.F;

      procedure P (X : in out R) is
         procedure P_Nested_2 (X : in out R) with Modifies => X.F;

         procedure P_Nested_2 (X : in out R) is
         begin
            X.F := Part_Of_V;
            Part_Of_V := 1;
         end P_Nested_2;
      begin
         X.F := Part_Of_V;
         Part_Of_V := 1;
      end P;

      procedure P_Nested (X : in out R) is
      begin
         X.F := Part_Of_V;
         Part_Of_V := 1;
      end P_Nested;
   end P;
end Ext;
