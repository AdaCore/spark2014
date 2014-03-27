package body Arrays_In_Records
is
   pragma Warnings (Off, "* has no effect");

   type    Counter is range 0 .. 1002;
   subtype Index   is Counter range 0 .. 1001;
   type    Value   is range -23 .. 69;

   type Basic_Array is array (Index) of Value;

   type Record_With_Arrays is record
      Counter      : Index;
      First_Array  : Basic_Array;
      Second_Array : Basic_Array;
   end record;

   -- Records including Arrays --

   procedure RA_Constant_Access (A : in Record_With_Arrays)
     with Depends => (null => A)
   is
   begin
      pragma Assert (A.First_Array(17) = 23);  --  @ASSERT:FAIL
   end RA_Constant_Access;

   procedure RA_Variable_Access (A : in Record_With_Arrays; I : in Index)
     with Depends => (null => (A, I))
   is
   begin
      pragma Assert (A.First_Array(I) = 23);  --  @ASSERT:FAIL
   end RA_Variable_Access;



   procedure RA_Constant_Update_And_Access (A : in out Record_With_Arrays)
     with Depends => (A =>+ null),
          Post    => A.First_Array(17) = 23  --  @POSTCONDITION:FAIL
   is
   begin
      A.First_Array(17) := 42;
   end RA_Constant_Update_And_Access;

   procedure RA_Variable_Update_And_Access (A : in out Record_With_Arrays;
                                            I : in     Index)
     with Depends => (A =>+ I),
          Post    => A.First_Array(I) = 23  --  @POSTCONDITION:FAIL
   is
   begin
      A.First_Array(I) := 42;
   end RA_Variable_Update_And_Access;



   procedure RA_Constant_Update_And_Access_With_Irrelevant_Modifications
     (A : in out Record_With_Arrays)
     with Depends => (A =>+ null),
          Post    => A.First_Array(17) = 23  --  @POSTCONDITION:FAIL
   is
   begin
      A.Counter           := 100;
      A.First_Array(17)   := 42;
      A.Second_Array(101) := 23;
      pragma Assert (A.Second_Array(101) = 23);  --  @ASSERT:PASS
   end RA_Constant_Update_And_Access_With_Irrelevant_Modifications;

   procedure RA_Variable_Update_And_Access_With_Irrelevant_Modifications
     (A : in out Record_With_Arrays;
      I : in     Index)
     with Depends => (A =>+ I),
          Pre     => A.First_Array(I) = 23
   is
   begin
      A.Counter         := I;
      A.First_Array(I)  := 42;
      A.Second_Array(I) := 23;
      pragma Assert (A.Second_Array(I) = 23);  --  @ASSERT:PASS
   end RA_Variable_Update_And_Access_With_Irrelevant_Modifications;



   procedure RA_Constant_Overwrite (A : in out Record_With_Arrays)
     with Depends => (A =>+ null),
          Post    => A.First_Array(17) = 42  --  @POSTCONDITION:FAIL
   is
   begin
      A.First_Array(17) := 42;
      A.First_Array(17) := 23;
   end RA_Constant_Overwrite;

   procedure RA_Variable_Overwrite (A : in out Record_With_Arrays;
                                    I : in     Index)
     with Depends => (A =>+ I),
          Post    => A.First_Array(I) = 42  --  @POSTCONDITION:FAIL
   is
   begin
      A.First_Array(I) := 42;
      A.First_Array(I) := 23;
   end RA_Variable_Overwrite;



   procedure RA_Constant_Overwrite_With_Irrelevant_Modifications
     (A : in out Record_With_Arrays)
     with Depends => (A =>+ null),
          Post    => A.First_Array(17) = 42  --  @POSTCONDITION:FAIL
   is
   begin
      A.Second_Array(23) := 69;
      A.First_Array(17)  := 42;
      A.First_Array(17)  := 23;
      A.Counter := 100;
      pragma Assert (A.Second_Array(23) = 69);  --  @ASSERT:PASS
   end RA_Constant_Overwrite_With_Irrelevant_Modifications;

   procedure RA_Variable_Overwrite_With_Irrelevant_Modifications
     (A : in out Record_With_Arrays;
      I : in     Index)
     with Depends => (A =>+ I),
          Post    => A.First_Array(I) = 42  --  @POSTCONDITION:FAIL
   is
   begin
      A.Second_Array(I) := 69;
      A.First_Array(I)  := 42;
      A.First_Array(I)  := 23;
      A.Counter         := 100;
      pragma Assert (A.Second_Array(I) = 69);  --  @ASSERT:PASS
   end RA_Variable_Overwrite_With_Irrelevant_Modifications;



   procedure RA_Constant_Passthrough (A : in out Record_With_Arrays)
     with Depends => (A =>+ null),
          Post    => A.First_Array(17) /= 23  --  @POSTCONDITION:FAIL
   is
   begin
      A.First_Array(17) := 23;
      A.First_Array(5)  := 42;
   end RA_Constant_Passthrough;

   procedure RA_Variable_Passthrough (A    : in out Record_With_Arrays;
                                      I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A.First_Array(I) /= 23  --  @POSTCONDITION:FAIL
   is
   begin
      A.First_Array(I) := 23;
      A.First_Array(J) := 42;
   end RA_Variable_Passthrough;



   procedure RA_Constant_Passthrough_With_Irrelevant_Modifications
     (A : in out Record_With_Arrays)
     with Depends => (A =>+ null),
          Post    => A.First_Array(17) /= 23  --  @POSTCONDITION:FAIL
   is
   begin
      A.Second_Array(23) := 69;
      A.First_Array(17)  := 23;
      A.First_Array(5)   := 42;
      A.Counter          := 100;
      pragma Assert (A.Second_Array(23) = 69);  --  @ASSERT:PASS
   end RA_Constant_Passthrough_With_Irrelevant_Modifications;

   procedure RA_Variable_Passthrough_With_Irrelevant_Modifications
     (A    : in out Record_With_Arrays;
      I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A.First_Array(I) /= 23  --  @POSTCONDITION:FAIL
   is
   begin
      A.Second_Array(I) := 69;
      A.First_Array(I)  := 23;
      A.First_Array(J)  := 42;
      A.Counter         := 100;
      pragma Assert (A.Second_Array(I) = 69);  --  @ASSERT:PASS
   end RA_Variable_Passthrough_With_Irrelevant_Modifications;



   procedure RA_Constant_Swap (A : in out Record_With_Arrays)
     with Depends => (A =>+ null),
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp               := A.First_Array(17);
      A.First_Array(17) := A.First_Array(5);
      A.First_Array(5)  := Tmp;
   end RA_Constant_Swap;

   procedure RA_Variable_Swap (A    : in out Record_With_Arrays;
                               I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp              := A.First_Array(I);
      A.First_Array(I) := A.First_Array(J);
      A.First_Array(J) := Tmp;
   end RA_Variable_Swap;



   procedure RA_Constant_Swap_With_Irrelevant_Modifications
     (A : in out Record_With_Arrays)
     with Depends => (A =>+ null),
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp                := A.First_Array(17);
      A.Counter          := 17;
      A.First_Array(17)  := A.First_Array(5);
      A.Second_Array(23) := Tmp;
      A.First_Array(5)   := Tmp;
   end RA_Constant_Swap_With_Irrelevant_Modifications;

   procedure RA_Variable_Swap_With_Irrelevant_Modifications
     (A    : in out Record_With_Arrays;
      I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp               := A.First_Array(I);
      A.Counter         := I;
      A.First_Array(I)  := A.First_Array(J);
      A.Second_Array(J) := Tmp;
      A.First_Array(J)  := Tmp;
   end RA_Variable_Swap_With_Irrelevant_Modifications;



   procedure RA_Constant_Two_Array_Swap (A, B : in out Record_With_Arrays)
     with Depends => ((A, B) => (A, B)),
          Post    => A /= A'Old and B /= B'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp               := A.First_Array(17);
      A.First_Array(17) := B.Second_Array(5);
      B.Second_Array(5) := Tmp;
   end RA_Constant_Two_Array_Swap;

   procedure RA_Variable_Two_Array_Swap (A, B : in out Record_With_Arrays;
                                         I, J : in     Index)
     with Depends => ((A, B) => (A, B, I, J)),
          Post    => A /= A'Old and B /= B'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp               := A.First_Array(I);
      A.First_Array(I)  := B.Second_Array(J);
      B.Second_Array(J) := Tmp;
   end RA_Variable_Two_Array_Swap;

   procedure RA_Constant_Two_Array_Swap_Internal
     (A : in out Record_With_Arrays)
     with Depends => (A =>+ null),
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp               := A.First_Array(17);
      A.First_Array(17) := A.Second_Array(5);
      A.Second_Array(5) := Tmp;
   end RA_Constant_Two_Array_Swap_Internal;

   procedure RA_Variable_Two_Array_Swap_Internal
     (A    : in out Record_With_Arrays;
      I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp               := A.First_Array(I);
      A.First_Array(I)  := A.Second_Array(J);
      A.Second_Array(J) := Tmp;
   end RA_Variable_Two_Array_Swap_Internal;

   pragma Warnings (On, "* has no effect");
end Arrays_In_Records;
