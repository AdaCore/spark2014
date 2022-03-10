package Exprold is

   type Int is range 1 .. 10;

   type Int_Record is record
      X : Int := 1;
   end record;

   type Int_Array is array (Int) of Int;

   type Record_Array is array (Int) of Int_Record;

   function Same (I : in Natural) return Natural;

   procedure Old_On_Call (I : in out Natural)
     with
       Pre => I < Integer'Last,
       Post => Same (I)'Old = I - 2;                  -- @POSTCONDITION:FAIL

   procedure Old_On_Record_Field (R : in out Int_Record)
     with
       Pre => R.X <= Int'Last - 2,
       Post => R.X = R.X'Old + 2;                     -- @POSTCONDITION:FAIL

   procedure Old_On_Array_Elt (A : in out Int_Array)
     with
       Pre => A(1) <= Int'Last - 2,
       Post => A(1) = A(1)'Old + 2;                   -- @POSTCONDITION:FAIL

   procedure Old_On_Record_Field_In_Array (A : in out Record_Array)
     with
       Pre => A(1).X <= Int'Last - 2,
       Post => A(1).X = A(1).X'Old + 2;               -- @POSTCONDITION:FAIL

   procedure Old_On_Integer (I : in out Integer)
     with
       Pre => I <= Integer'Last - 3,
       Post =>
          Integer'(I + 1) = Integer'(I + 1)'Old + 2;  -- @POSTCONDITION:FAIL

end Exprold;
