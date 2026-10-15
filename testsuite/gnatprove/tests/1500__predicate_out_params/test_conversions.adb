procedure Test_Conversions with SPARK_Mode is
   procedure Set_Values (Low, High : out Integer; Valid : Boolean)
   with
     Import,
     Global => null,
     Always_Terminates,
     Post   => Low = 20 and High = (if Valid then 30 else 10);

   type Parent is tagged record
      Low, High : Integer;
   end record
   with Dynamic_Predicate => Parent.Low <= Parent.High;
   type Child is new Parent with null record;
   type Grandchild is new Child with null record;

   type Root is tagged record
      Low, High : Integer;
   end record;
   subtype Sorted is Root with Dynamic_Predicate => Sorted.Low <= Sorted.High;
   type Extension is new Root with null record;

   type Discriminated (D : Positive) is tagged record
      Low, High : Integer;
   end record
   with Dynamic_Predicate => Discriminated.Low <= Discriminated.High;
   subtype One is Discriminated (1);

   procedure Ancestor_Conversion (Obj : in out Grandchild) with Global => null
   is
   begin
      Set_Values
        (Parent (Obj).Low, Parent (Obj).High, True); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj.Low = 20 and Obj.High = 30);
   end Ancestor_Conversion;

   procedure Bad_Ancestor_Conversion (Obj : in out Grandchild)
   with Global => null
   is
   begin
      Set_Values
        (Parent (Obj).Low, Parent (Obj).High, False); -- @PREDICATE_CHECK:FAIL
   end Bad_Ancestor_Conversion;

   procedure Bad_Discriminant (Obj : in out Discriminated)
   with Global => null, Pre => Obj.D /= 1
   is
   begin
      Set_Values
        (One (Obj).Low, One (Obj).High, True); -- @DISCRIMINANT_CHECK:FAIL
   end Bad_Discriminant;

   --  Predicates on conversion views need not hold after component updates

   procedure Break_Nested_Predicate (Obj : in out Root)
   with Global => null, Pre => Obj.Low <= Obj.High
   is
   begin
      Set_Values
        (Root (Sorted (Obj)).Low, Obj.High, False); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj.Low = 20 and Obj.High = 10);
   end Break_Nested_Predicate;

   procedure Break_Subtype_Predicate (Obj : in out Root)
   with Global => null, Pre => Obj.Low <= Obj.High
   is
   begin
      Set_Values
        (Sorted (Obj).Low, Sorted (Obj).High, False); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj.Low = 20 and Obj.High = 10);
   end Break_Subtype_Predicate;

   procedure Bad_Tag (Obj : in out Root'Class)
   with Global => null, Pre => Obj not in Extension
   is
   begin
      Set_Values
        (Extension (Obj).Low, Extension (Obj).High, True); -- @TAG_CHECK:FAIL
   end Bad_Tag;

   procedure Discriminant_Conversion (Obj : in out Discriminated)
   with Global => null, Pre => Obj.D = 1
   is
   begin
      Set_Values
        (One (Obj).Low, One (Obj).High, True); -- @DISCRIMINANT_CHECK:PASS @PREDICATE_CHECK:PASS
      pragma Assert (Obj.Low = 20 and Obj.High = 30);
   end Discriminant_Conversion;

   procedure Nested_Conversion (Obj : in out Root)
   with Global => null, Pre => Obj.Low <= Obj.High
   is
   begin
      Set_Values
        (Root (Sorted (Obj)).Low, Obj.High, False); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj.Low = 20 and Obj.High = 30);
   end Nested_Conversion;

   procedure Subtype_Conversion (Obj : in out Root)
   with Global => null, Pre => Obj.Low <= Obj.High
   is
   begin
      Set_Values
        (Sorted (Obj).Low, Sorted (Obj).High, True); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj.Low = 20 and Obj.High = 30);
   end Subtype_Conversion;

   procedure Tag_Conversion (Obj : in out Root'Class)
   with Global => null, Pre => Obj in Extension
   is
   begin
      Set_Values
        (Extension (Obj).Low, Extension (Obj).High, True); -- @TAG_CHECK:PASS
      pragma Assert (Obj.Low = 20 and Obj.High = 30);
   end Tag_Conversion;

   procedure Invalid_Initial_View (Obj : in out Root)
   with Global => null, Pre => Obj.Low > Obj.High
   is
   begin
      Set_Values
        (Sorted (Obj).Low, Obj.High, True); -- @PREDICATE_CHECK:FAIL
   end Invalid_Initial_View;

   procedure Set_Root (Obj : in out Root)
   with
     Import,
     Global => null,
     Always_Terminates,
     Post => Obj.Low = 20 and Obj.High = 10;

   procedure Whole_Conversion (Obj : in out Root)
   with Global => null, Pre => Obj.Low <= Obj.High
   is
   begin
      Set_Root (Sorted (Obj)); -- @PREDICATE_CHECK:FAIL
   end Whole_Conversion;
begin
   null;
end Test_Conversions;
