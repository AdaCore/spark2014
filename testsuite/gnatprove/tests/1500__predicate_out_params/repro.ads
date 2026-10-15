package Repro with SPARK_Mode is
   subtype Length_Type is Natural range 0 .. 2;

   type Cell is record
      Value : Integer;
   end record with Relaxed_Initialization;

   type Array_Type is array (Positive range 1 .. 2) of Cell;

   type Vector is record
      Last : Length_Type := 0;
      Data : Array_Type;
   end record
   with Ghost_Predicate =>
     (for all I in 1 .. Last => Data (I).Value'Initialized);

   procedure Grow_Array_First (V : in out Vector)
   with Pre => V.Last = 0;

   procedure Grow_Last_First (V : in out Vector)
   with Pre => V.Last = 0;

   procedure Set_Array_First
     (Data : in out Array_Type;
      Last : in out Length_Type;
      New_Last : Length_Type)
   with Post =>
     (Static =>
        Last = New_Last
        and then (for all I in 1 .. Last => Data (I).Value'Initialized));

   procedure Set_Last_First
     (Last : in out Length_Type;
      Data : in out Array_Type;
      New_Last : Length_Type)
   with Post =>
     (Static =>
        Last = New_Last
        and then (for all I in 1 .. Last => Data (I).Value'Initialized));

   procedure Shrink_Array_First (V : in out Vector)
   with Pre => V.Last = 2;

   procedure Shrink_Last_First (V : in out Vector)
   with Pre => V.Last = 2;
end Repro;
