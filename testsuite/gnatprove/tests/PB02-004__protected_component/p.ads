package P is

   function Zero return Natural is (0);

   protected type PT (X : Positive) is
   end;

   type Rec is record
      PO : PT (Zero); --@RANGE_CHECK:FAIL
   end record with Volatile;

   type Arr is array (Boolean) of PT (Zero) with Volatile;

   --  Range checks already fail at type definitions,
   --  even without object declarations below.
   --R : Rec;
   --A : Arr;

end;
