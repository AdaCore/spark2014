package Update_Equality with SPARK_Mode is
   type I is new Integer with Relaxed_Initialization;
   type A is array (1 .. 2) of I;

   procedure Partial (X : in out A) with
     Post => X = X'Old'Update (1 => 0); -- @INIT_BY_PROOF:FAIL

   procedure Reversed_Delta (X : in out A) with
     Post => (X'Old with delta 1 => 0) = X; -- @INIT_BY_PROOF:FAIL

   --  Only the updated old operand has an uninitialized element
   procedure Old_Partial (X : in out A) with
     Post => X = X'Old'Update (1 => 0); -- @INIT_BY_PROOF:FAIL @POSTCONDITION:FAIL

   procedure Initialized (X : in out A) with
     Pre => (for all E of X => E'Initialized),
     Post => X = X'Old'Update (1 => 0);

   --  Replacing every element does not read the old elements
   procedure Replace_All (X : in out A) with
     Post => X = X'Old'Update (1 .. 2 => 0);

   type Plain_Array is array (1 .. 2) of Integer;
   procedure Object_Relaxed (X : in out Plain_Array) with
     Relaxed_Initialization => X,
     Post => X = X'Old'Update (1 => 0); -- @INIT_BY_PROOF:FAIL

   type R is record
      F : I;
   end record;
   function "=" (L, R : R) return Boolean is (True);
   type Records is array (1 .. 2) of R;

   --  Component equality does not read the relaxed field
   procedure Custom_Equality (X : in out Records) with
     Post => X = X'Old'Update (1 => (F => 0));
end Update_Equality;
