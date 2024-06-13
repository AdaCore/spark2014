procedure Test_Call with SPARK_Mode is

   type Root is tagged record
      F : Integer;
   end record;

   type Child is new Root with record
      G : Integer;
   end record;

   procedure Set (X : out Root; Y : Root) with
     Global => null
   is
   begin
      X := Y;
   end Set;

   procedure Bad is
      C1 : Child := (1, 1);
      C2 : Child := (2, 2);
   begin
      Set (Root (C1), Root (C2));
      pragma Assert (C1.G = 2); -- @ASSERT:FAIL
   end Bad;

   procedure OK is
      C1 : Child := (1, 1);
      C2 : Child := (2, 2);
   begin
      Set (Root (C1), Root (C2));
      pragma Assert (C1.G = 1); -- @ASSERT:PASS
   end OK;

   procedure Set_Ext (X : out Root; Y : Root) with
     Global => null,
     --  Pre  => Root'Class (X) in Child and Root'Class (Y) in Child,
     Extensions_Visible => True
     -- Post => Root'Class (X) = Root'Class (Y)
   is
   begin
      Root'Class (X) := Root'Class (Y);
   end Set_Ext;

   procedure Bad_Ext is
      C1 : Child := (1, 1);
      C2 : Child := (2, 2);
   begin
      Set_Ext (Root (C1), Root (C2));
      pragma Assert (C1.G = 1); -- @ASSERT:FAIL
   end Bad_Ext;

   procedure OK_Ext is
      C1 : Child := (1, 1);
      C2 : Child := (2, 2);
   begin
      Set_Ext (Root (C1), Root (C2));
      pragma Assert (C1.G = 2); -- Not provable for now as the Post cannot be stated
   end OK_Ext;

   procedure Set_Class (X : out Root'Class; Y : Root'Class) with
     Global => null,
     Pre  => X in Child and Y in Child,
     Post => X = Y
   is
   begin
     X := Y;
   end Set_Class;

   procedure Bad_Class is
      C1 : Child := (1, 1);
      C2 : Child := (2, 2);
   begin
      Set_Class (Root (C1), Root (C2));
      pragma Assert (C1.G = 1); -- @ASSERT:FAIL
   end Bad_Class;

   procedure OK_Class is
      C1 : Child := (1, 1);
      C2 : Child := (2, 2);
   begin
      Set_Class (Root (C1), Root (C2));
      pragma Assert (C1.G = 2); -- @ASSERT:PASS
   end OK_Class;

begin
   null;
end Test_Call;
