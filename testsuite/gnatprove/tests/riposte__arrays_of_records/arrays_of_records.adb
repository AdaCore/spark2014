package body Arrays_Of_Records
is
   pragma Warnings (Off, "* has no effect");

   type    Counter is range 0 .. 1002;
   subtype Index   is Counter range 0 .. 1001;
   type    Value   is range -23 .. 69;

   type Basic_Record is record
      Flag         : Boolean;
      First_Value  : Value;
      Second_Value : Value;
   end record;

   type Array_Of_Records is array (Index) of Basic_Record;

   -- Arrays of Records --

   procedure AR_Constant_Access (A : in Array_Of_Records)
     with Depends => (null => A)
   is
   begin
      pragma Assert (A(17).First_Value = 23);  --  @ASSERT:FAIL
   end AR_Constant_Access;

   procedure AR_Variable_Access (A : in Array_Of_Records; I : in Index)
     with Depends => (null => (A, I))
   is
   begin
      pragma Assert (A(I).First_Value = 23);  --  @ASSERT:FAIL
   end AR_Variable_Access;

   procedure AR_Constant_Update_And_Access (A : in out Array_Of_Records)
     with Depends => (A =>+ null),
          Post    => A(17).First_Value = 23  --  @POSTCONDITION:FAIL
   is
   begin
      A(17).First_Value := 42;
   end AR_Constant_Update_And_Access;

   procedure AR_Variable_Update_And_Access (A : in out Array_Of_Records;
                                            I : in     Index)
     with Depends => (A =>+ I),
          Post    => A(I).First_Value = 23  --  @POSTCONDITION:FAIL
   is
   begin
      A(I).First_Value := 42;
   end AR_Variable_Update_And_Access;



   procedure AR_Constant_Update_And_Access_With_Irrelevant_Modifications
     (A : in out Array_Of_Records)
     with Depends => (A =>+ null),
          Post    => A(17).First_Value = 23  --  @POSTCONDITION:FAIL
   is
   begin
      A(17).Flag          := True;
      A(17).First_Value   := 42;
      A(101).Second_Value := 23;
      pragma Assert (A(101).Second_Value = 23);  --  @ASSERT:PASS
   end AR_Constant_Update_And_Access_With_Irrelevant_Modifications;

   procedure AR_Variable_Update_And_Access_With_Irrelevant_Modifications
     (A : in out Array_Of_Records;
      I : in     Index)
     with Depends => (A =>+ I),
          Post    => A(I).First_Value = 23  --  @POSTCONDITION:FAIL
   is
   begin
      A(I).Flag := True;
      A(I).First_Value := 42;
      A(I).Second_Value := 23;
      pragma Assert (A(I).Second_Value = 23);  --  @ASSERT:PASS
   end AR_Variable_Update_And_Access_With_Irrelevant_Modifications;



   procedure AR_Constant_Overwrite (A : in out Array_Of_Records)
     with Depends => (A =>+ null),
          Post    => A(17).First_Value = 42  --  @POSTCONDITION:FAIL
   is
   begin
      A(17).First_Value := 42;
      A(17).First_Value := 23;
   end AR_Constant_Overwrite;

   procedure AR_Variable_Overwrite (A : in out Array_Of_Records; I : in Index)
     with Depends => (A =>+ I),
          Post    => A(I).First_Value = 42  --  @POSTCONDITION:FAIL
   is
   begin
      A(I).First_Value := 42;
      A(I).First_Value := 23;
   end AR_Variable_Overwrite;



   procedure AR_Constant_Overwrite_With_Irrelevant_Modifications
     (A : in out Array_Of_Records)
     with Depends => (A =>+ null),
          Post    => A(17).First_Value = 42  --  @POSTCONDITION:FAIL
   is
   begin
      A(23).Second_Value := 69;
      A(17).First_Value  := 42;
      A(17).First_Value  := 23;
      A(5).Flag          := False;
      pragma Assert (A(23).Second_Value = 69);  --  @ASSERT:PASS
   end AR_Constant_Overwrite_With_Irrelevant_Modifications;

   procedure AR_Variable_Overwrite_With_Irrelevant_Modifications
     (A : in out Array_Of_Records;
      I : in     Index)
     with Depends => (A =>+ I),
          Post    => A(I).First_Value = 42  --  @POSTCONDITION:FAIL
   is
   begin
      A(I).Second_Value := 69;
      A(I).First_Value  := 42;
      A(I).First_Value  := 23;
      A(I).Flag         := False;
      pragma Assert (A(I).Second_Value = 69);  --  @ASSERT:PASS
   end AR_Variable_Overwrite_With_Irrelevant_Modifications;



   procedure AR_Constant_Passthrough (A : in out Array_Of_Records)
     with Depends => (A =>+ null),
          Post    => A(17).First_Value /= 23  --  @POSTCONDITION:FAIL
   is
   begin
      A(17).First_Value := 23;
      A(5).First_Value  := 42;
   end AR_Constant_Passthrough;

   procedure AR_Variable_Passthrough (A    : in out Array_Of_Records;
                                      I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A(I).First_Value /= 23  --  @POSTCONDITION:FAIL
   is
   begin
      A(I).First_Value := 23;
      A(J).First_Value := 42;
   end AR_Variable_Passthrough;



   procedure AR_Constant_Passthrough_With_Irrelevant_Modifications
     (A : in out Array_Of_Records)
     with Depends => (A =>+ null),
          Post    => A(17).First_Value /= 23  --  @POSTCONDITION:FAIL
   is
   begin
      A(23).Second_Value := 69;
      A(17).First_Value  := 23;
      A(5).First_Value   := 42;
      A(23).Flag         := True;
      pragma Assert (A(23).Second_Value = 69);  --  @ASSERT:PASS
   end AR_Constant_Passthrough_With_Irrelevant_Modifications;

   procedure AR_Variable_Passthrough_With_Irrelevant_Modifications
     (A    : in out Array_Of_Records;
      I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A(I).First_Value /= 23  --  @POSTCONDITION:FAIL
   is
   begin
      A(I).Second_Value := 69;
      A(I).First_Value  := 23;
      A(J).First_Value  := 42;
      A(I).Flag         := True;
      pragma Assert (A(I).Second_Value = 69);  --  @ASSERT:PASS
   end AR_Variable_Passthrough_With_Irrelevant_Modifications;



   procedure AR_Constant_Swap (A : in out Array_Of_Records)
     with Depends => (A =>+ null),
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp               := A(17).First_Value;
      A(17).First_Value := A(5).First_Value;
      A(5).First_Value  := Tmp;
   end AR_Constant_Swap;

   procedure AR_Constant_Swap_B (A : in out Array_Of_Records)
     with Depends => (A =>+ null),
          Post    => A = A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp               := A(17).First_Value;
      A(17).First_Value := A(5).First_Value;
      A(5).First_Value  := Tmp;
   end AR_Constant_Swap_B;

   procedure AR_Variable_Swap (A    : in out Array_Of_Records;
                               I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp              := A(I).First_Value;
      A(I).First_Value := A(J).First_Value;
      A(J).First_Value := Tmp;
   end AR_Variable_Swap;



   procedure AR_Constant_Swap_With_Irrelevant_Modifications
     (A : in out Array_Of_Records)
     with Depends => (A =>+ null),
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp                := A(17).First_Value;
      A(23).Flag         := True;
      A(17).First_Value  := A(5).First_Value;
      A(23).Second_Value := Tmp;
      A(5).First_Value   := Tmp;
   end AR_Constant_Swap_With_Irrelevant_Modifications;

   procedure AR_Variable_Swap_With_Irrelevant_Modifications
     (A    : in out Array_Of_Records;
      I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp               := A(I).First_Value;
      A(I).Flag         := False;
      A(I).First_Value  := A(J).First_Value;
      A(J).Second_Value := Tmp;
      A(J).First_Value  := Tmp;
   end AR_Variable_Swap_With_Irrelevant_Modifications;




   procedure AR_Constant_Two_Array_Swap (A, B : in out Array_Of_Records)
     with Depends => ((A, B) => (A, B)),
          Post    => A /= A'Old and B /= B'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp               := A(17).First_Value;
      A(17).First_Value := B(5).Second_Value;
      B(5).Second_Value := Tmp;
   end AR_Constant_Two_Array_Swap;

   procedure AR_Variable_Two_Array_Swap (A, B : in out Array_Of_Records;
                                         I, J : in Index)
     with Depends => ((A, B) => (A, B, I, J)),
          Post    => A /= A'Old and B /= B'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp               := A(I).First_Value;
      A(I).First_Value  := B(J).Second_Value;
      B(J).Second_Value := Tmp;
   end AR_Variable_Two_Array_Swap;


   procedure AR_Constant_Two_Array_Swap_Internal (A : in out Array_Of_Records)
     with Depends => (A =>+ null),
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp               := A(17).First_Value;
      A(17).First_Value := A(5).Second_Value;
      A(5).Second_Value := Tmp;
   end AR_Constant_Two_Array_Swap_Internal;

   procedure AR_Variable_Two_Array_Swap_Internal
     (A    : in out Array_Of_Records;
      I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp               := A(I).First_Value;
      A(I).First_Value  := A(J).Second_Value;
      A(J).Second_Value := Tmp;
   end AR_Variable_Two_Array_Swap_Internal;

   pragma Warnings (On, "* has no effect");
end Arrays_Of_Records;
