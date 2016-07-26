package Frame_Condition with SPARK_Mode is
   type Cell is record
      Value     : Natural;
      Max_Left  : Natural;
      Max_Right : Natural;
   end record;

   type Cell_Array is array (Positive range <>) of Cell;

   procedure Update_Max (A : in out Cell_Array) with
     Post => (for all I in A'Range =>
                A (I).Value = A'Old (I).Value
              and (for all J in I .. A'Last =>
                       A (I).Value <= A (J).Max_Left
                   and A (J).Value <= A (I).Max_Right));

   procedure Update_Max_2 (A : in out Cell_Array) with
     Post => (for all I in A'Range =>
                A (I).Value = A'Old (I).Value
              and (for all J in I .. A'Last =>
                       A (I).Value <= A (J).Max_Left
                   and A (J).Value <= A (I).Max_Right));

   procedure Update_Max_3 (A : in out Cell_Array) with
     Post => (for all I in A'Range =>
                A (I).Value = A'Old (I).Value
              and (for all J in I .. A'Last =>
                       A (I).Value <= A (J).Max_Left
                   and A (J).Value <= A (I).Max_Right));
end Frame_Condition;
