package Record_Equality with SPARK_Mode is
   type Root (C : Natural) is tagged record
      F1 : Natural := 0;
   end record;
   type Child is new Root with record
      F2 : Natural := 0;
   end record;
   type GrandChild is new Child with record
      F3 : Natural := 0;
   end record;

   subtype Root_0 is Root (C => 0);
   subtype Child_0 is Child (C => 0);

   procedure Test_Eq_Ok;
   procedure Test_Eq_Ko;
   procedure Test_Eq_Ko_D;
   procedure Test_Eq_Ko_D2;
   procedure Test_Eq_Ko_D3;
end Record_Equality;
