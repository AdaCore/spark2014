package body A is
   --  Initializes should be just Var and VI1.

   function Add (X, Y : Integer) return Integer is (X + Y);

   function Add_Annotated (X, Y : Integer) return Integer is (X + Y);

   function Add_Annotated_Local (X, Y : Integer)
                                 return Integer
   is (X + Y)
   with Global => null;

   Var : Integer := 0;

   --  All of these are constant without variable inputs, so should not appear.
   C1 : constant Integer := 42;
   C2 : constant Integer := C1 + 2;
   C3 : constant Integer := Add_Annotated_Local (C1, C2);
   C4 : constant Integer := Add_Annotated_Local (C1, C3);
   C5 : constant Integer := Add_Annotated (C3, C4);
   C6 : constant Integer := Add_Annotated (C3, C5);
   C7 : constant Integer := Add (C5, C6);
   C8 : constant Integer := Add (C5, C7);

   --  All of these are constant with variable inputs, so should appear.
   VI1 : constant Integer := Var;

   function Test_01 return Integer with Pre => True;
   function Test_02 return Integer with Pre => True;
   function Test_03 return Integer with Pre => True, Global => null;
   function Test_04 return Integer with Pre => True, Global => VI1;

   function Test_01 return Integer
   is
   begin
      return C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8;
   end Test_01;

   function Test_02 return Integer
   is
   begin
      return VI1;
   end Test_02;

   function Test_03 return Integer
   is
   begin
      return C1 + C2 + C3 + C4 + C5 + C6 + C7 + C8;
   end Test_03;

   function Test_04 return Integer
   is
   begin
      return VI1;
   end Test_04;

end A;
