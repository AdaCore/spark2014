with SPARK.Heap;

procedure N (First, Last :     Integer;
             Result      : out Integer)
  with Depends => (Result => SPARK.Heap.Dynamic_Memory, null => (First, Last)),
       Post    => Result = 0,
       SPARK_Mode
is
   type Int is new Integer with Default_Value => 0;
   --  A type with Default_Value, so that we can allocate its objects without
   --  an explicit initialization expression.

   subtype T is Int range Int (First) .. Int (Last);
   --  A constrained scalar type with bounds depending on input parameters

   type Ptr is access Int;
   --  An access type, so that we can allocate something

   X : Ptr := new T;
   --  An object allocated without a qualified initialization expression;
   --  it depends on the Default_Value of T, not on the bounds of T.

begin
   Result := Integer (X.all);
   --  Copy allocated data to Result

   --  ??? The memory allocated for X leaks here, but we don't care
end;
