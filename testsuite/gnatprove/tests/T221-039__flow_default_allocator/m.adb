with SPARK.Heap;

procedure M (Data   :     Integer;
             Result : out Integer)
  with Depends => (Result => (SPARK.Heap.Dynamic_Memory, Data)),
       Post    => Result = Data,
       SPARK_Mode
is
   type R is record
      C : Integer := Data;
   end record;
   --  A record with default, non-static values for its components

   type Ptr is access R;
   --  An access type, so that we can allocate something

   X : Ptr := new R;
   --  An object allocated without a qualified initialization expression;
   --  it depends on the default values of R.

begin
   Result := X.C;
   --  Copy allocated data to Result

   --  ??? The memory allocated for X leaks here, but we don't care
end;
