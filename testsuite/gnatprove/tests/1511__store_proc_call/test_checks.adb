procedure Test_Checks with SPARK_Mode is
   subtype Index is Positive range 1 .. 2;

   type Cell is record
      Value : Integer;
   end record;
   subtype Positive_Cell is Cell
   with Dynamic_Predicate => Positive_Cell.Value >= 0;
   type Cells is array (Index) of Positive_Cell;

   type Int_Access is access constant Integer;
   subtype Non_Null_Access is not null Int_Access;
   type Accesses is array (Index) of Non_Null_Access;

   procedure Set_Access
     (I : out Index; Obj : out Int_Access; Value : Int_Access)
   with
     Import,
     Global => null,
     Always_Terminates,
     Post   => I = 2 and (Obj = null) = (Value = null);

   procedure Set_Value (I : out Index; Obj : out Cell; Value : Integer)
   with
     Import,
     Global => null,
     Always_Terminates,
     Post   => I = 2 and Obj.Value = Value;

   --  Check the actual selected before the call, even though I becomes 2.
   --  The unchanged second element still satisfies its subtype constraints.

   --------------
   -- Bad_Null --
   --------------

   procedure Bad_Null (A : in out Accesses; I : in out Index)
   with Global => null, Pre => I = 1
   is
   begin
      Set_Access (I, A (I), null); -- @NULL_EXCLUSION:FAIL
   end Bad_Null;

   -------------------
   -- Bad_Predicate --
   -------------------

   procedure Bad_Predicate (A : in out Cells; I : in out Index)
   with Global => null, Pre => I = 1
   is
   begin
      Set_Value (I, A (I), -1); -- @PREDICATE_CHECK:FAIL
   end Bad_Predicate;

   ---------------
   -- Good_Null --
   ---------------

   procedure Good_Null
     (A : in out Accesses; I : in out Index; Value : Non_Null_Access)
   with Global => null, Pre => I = 1
   is
   begin
      Set_Access (I, A (I), Value); -- @NULL_EXCLUSION:PASS
   end Good_Null;

   --------------------
   -- Good_Predicate --
   --------------------

   procedure Good_Predicate (A : in out Cells; I : in out Index)
   with Global => null, Pre => I = 1
   is
   begin
      Set_Value (I, A (I), 1); -- @PREDICATE_CHECK:PASS
   end Good_Predicate;
begin
   null;
end Test_Checks;
