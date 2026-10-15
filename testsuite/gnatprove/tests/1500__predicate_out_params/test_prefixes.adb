procedure Test_Prefixes with SPARK_Mode is
   type Pair is record
      Low, High : Integer;
   end record
     with Dynamic_Predicate => Pair.Low <= Pair.High;

   procedure Set_Values (Low, High : out Integer)
     with Import, Global => null, Post => Low = 20 and High = 30;

   procedure Update_Values (Low, High : in out Integer)
     with Import, Global => null, Post => Low = 20 and High = 30;

   procedure Set_Bad_Values (Low, High : out Integer)
     with Import, Global => null, Post => Low = 20 and High = 10;

   procedure Simple (Obj : in out Pair) with Global => null is
   begin
      Set_Values (Obj.Low, Obj.High); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj.Low = 20 and Obj.High = 30);
   end Simple;

   procedure In_Out_Params (Obj : in out Pair) with Global => null is
   begin
      Update_Values (Obj.Low, Obj.High); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj.Low = 20 and Obj.High = 30);
   end In_Out_Params;

   type Cell is record
      Value : Integer;
   end record;

   type Cell_Pair is record
      Low, High : Cell;
   end record
     with Dynamic_Predicate => Cell_Pair.Low.Value <= Cell_Pair.High.Value;

   procedure Set_Cells (Low, High : out Cell)
     with Import, Global => null,
          Post => Low.Value = 20 and High.Value = 30;

   procedure Composite_Actuals (Obj : in out Cell_Pair)
     with Global => null
   is
   begin
      Set_Cells (Obj.Low, Obj.High); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj.Low.Value = 20 and Obj.High.Value = 30);
   end Composite_Actuals;

   type Outer is record
      Contents : Pair;
      Limit : Integer;
   end record
     with Dynamic_Predicate => Outer.Contents.High <= Outer.Limit;

   procedure Set_Nested (Low, High, Limit : out Integer)
     with Import, Global => null,
          Post => Low = 20 and High = 30 and Limit = 40;

   procedure Nested (Obj : in out Outer) with Global => null is
   begin
      Set_Nested (Obj.Contents.Low, Obj.Contents.High, Obj.Limit); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj.Contents.Low = 20 and Obj.Contents.High = 30
                     and Obj.Limit = 40);
   end Nested;

   type Parent is tagged record
      Low, High : Integer;
   end record;

   type Child is new Parent with null record
     with Dynamic_Predicate => Child.Low <= Child.High;

   procedure View_Conversion (Obj : in out Child) with Global => null is
   begin
      Set_Values (Parent (Obj).Low, Parent (Obj).High); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj.Low = 20 and Obj.High = 30);
   end View_Conversion;

   type Pred_Parent is tagged record
      Low, High : Integer;
   end record
     with Dynamic_Predicate => Pred_Parent.Low <= Pred_Parent.High;

   type Pred_Child is new Pred_Parent with null record;

   procedure Inherited_Predicate (Obj : in out Pred_Child)
     with Global => null
   is
   begin
      Set_Values (Pred_Parent (Obj).Low, Pred_Parent (Obj).High); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj.Low = 20 and Obj.High = 30);
   end Inherited_Predicate;

   subtype Index is Positive range 1 .. 2;
   type Pair_Array is array (Index) of Pair;

   procedure Set_Indexed (Low, High : out Integer; I : out Index)
     with Import, Global => null,
          Post => Low = 20 and High = 30 and I = 2;

   procedure Indexed (Obj : in out Pair_Array; I : in out Index)
     with Global => null
   is
      Initial_Index : constant Index := I;
   begin
      Set_Indexed (Obj (I).Low, Obj (I).High, I); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj (Initial_Index).Low = 20
                     and Obj (Initial_Index).High = 30);
   end Indexed;

   type Int_Array is array (Positive range <>) of Integer;

   type With_Array is record
      Data : Int_Array (1 .. 4);
      Limit : Integer;
   end record
     with Dynamic_Predicate => With_Array.Data (1) <= With_Array.Limit;

   procedure Set_Slice (Data : out Int_Array; Limit : out Integer)
     with Import, Global => null,
          Post => (for all I in Data'Range => Data (I) = 20) and Limit = 30;

   procedure Slices (Obj : in out With_Array) with Global => null is
   begin
      Set_Slice (Obj.Data (1 .. 2), Obj.Limit); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj.Data (1) = 20 and Obj.Data (2) = 20
                     and Obj.Limit = 30);
   end Slices;

   type Pair_Access is access Pair;

   procedure Dereference (Obj : in out Pair_Access)
     with Global => null, Pre => Obj /= null
   is
   begin
      Set_Values (Obj.all.Low, Obj.all.High); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj.Low = 20 and Obj.High = 30);
   end Dereference;

   --  A predicate that is false in the final state must still be checked

   procedure Bad_Final (Obj : in out Pair) with Global => null is
   begin
      Set_Bad_Values (Obj.Low, Obj.High); -- @PREDICATE_CHECK:FAIL
   end Bad_Final;

   procedure Set_Bad_Indexed (Low, High : out Integer; I : out Index)
     with Import, Global => null,
          Post => Low = 20 and High = 10 and I = 2;

   procedure Bad_Index (Obj : in out Pair_Array; I : in out Index)
     with Global => null, Pre => I = 1
   is
   begin
      Set_Bad_Indexed (Obj (I).Low, Obj (I).High, I); -- @PREDICATE_CHECK:FAIL
   end Bad_Index;

   --  Predicates on actuals and conversions of whole actuals stay checked

   subtype Positive_Cell is Cell
     with Dynamic_Predicate => Positive_Cell.Value >= 0;

   procedure Set_Negative (Obj : out Cell)
     with Import, Global => null, Post => Obj.Value = -1;

   procedure Bad_Actual (Obj : out Positive_Cell) with Global => null is
   begin
      Set_Negative (Obj); -- @PREDICATE_CHECK:FAIL
   end Bad_Actual;

   procedure Set_Bad_Parent (Obj : in out Parent)
     with Import, Global => null, Post => Obj.Low = 20 and Obj.High = 10;

   procedure Bad_Conversion (Obj : in out Child) with Global => null is
   begin
      Set_Bad_Parent (Parent (Obj)); -- @PREDICATE_CHECK:FAIL
   end Bad_Conversion;

   --  By-reference parameters are also stored on exceptional return

   type Tagged_Cell is tagged record
      Value : Integer;
   end record;

   type Tagged_Pair is record
      Low, High : Tagged_Cell;
   end record
     with Dynamic_Predicate => Tagged_Pair.Low.Value <= Tagged_Pair.High.Value;

   E : exception;

   procedure Set_Exceptional (Low, High : in out Tagged_Cell)
     with Import, Global => null,
          Post => Low.Value = 20 and High.Value = 30,
          Exceptional_Cases => (E => Low.Value = 20 and High.Value = 30);

   procedure Exceptional (Obj : in out Tagged_Pair)
     with Global => null, Exceptional_Cases => (E => True)
   is
   begin
      Set_Exceptional (Obj.Low, Obj.High); -- @PREDICATE_CHECK:PASS
   end Exceptional;

   procedure Set_Bad_Exceptional (Low, High : in out Tagged_Cell)
     with Import, Global => null,
          Post => Low.Value = 20 and High.Value = 30,
          Exceptional_Cases => (E => Low.Value = 20 and High.Value = 10);

   procedure Bad_Exceptional (Obj : in out Tagged_Pair)
     with Global => null, Exceptional_Cases => (E => True)
   is
   begin
      Set_Bad_Exceptional (Obj.Low, Obj.High); -- @PREDICATE_CHECK:FAIL
   end Bad_Exceptional;

   --  Capture indices so target reads recurse through conversions and slices

   type Child_Array is array (Index) of Child;

   procedure Indexed_Conversion (Obj : in out Child_Array; I : in out Index)
     with Global => null
   is
      Initial_Index : constant Index := I;
   begin
      Set_Indexed
        (Parent (Obj (I)).Low, Parent (Obj (I)).High, I); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj (Initial_Index).Low = 20
                     and Obj (Initial_Index).High = 30);
   end Indexed_Conversion;

   procedure Bad_Indexed_Conversion
     (Obj : in out Child_Array; I : in out Index)
     with Global => null, Pre => I = 1
   is
   begin
      Set_Bad_Indexed
        (Parent (Obj (I)).Low, Parent (Obj (I)).High, I); -- @PREDICATE_CHECK:FAIL
   end Bad_Indexed_Conversion;

   procedure Indexed_Slice (Obj : in out Pair_Array; I : in out Index)
     with Global => null
   is
      Initial_Index : constant Index := I;
   begin
      Set_Indexed
        (Obj (I .. I) (I).Low, Obj (I .. I) (I).High, I); -- @PREDICATE_CHECK:PASS
      pragma Assert (Obj (Initial_Index).Low = 20
                     and Obj (Initial_Index).High = 30);
   end Indexed_Slice;

   procedure Bad_Indexed_Slice (Obj : in out Pair_Array; I : in out Index)
     with Global => null, Pre => I = 1
   is
   begin
      Set_Bad_Indexed
        (Obj (I .. I) (I).Low, Obj (I .. I) (I).High, I); -- @PREDICATE_CHECK:FAIL
   end Bad_Indexed_Slice;
begin
   null;
end Test_Prefixes;
