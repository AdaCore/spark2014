pragma SPARK_Mode;

package Types is

   subtype Element_Type is Integer;

   type Queue_Array is array (Positive range <>) of Element_Type;

   type Queue_Type (Max_Size : Positive) is record
      Count : Natural  := 0;
      Front : Positive := 1;
      Items : Queue_Array (1 .. Max_Size);
   end record;

   type Priv_Queue_Type (Max_Size : Positive) is private;

private
   type Priv_Queue_Type (Max_Size : Positive) is record
      Count : Natural  := 0;
      Front : Positive := 1;
      Items : Queue_Array (1 .. Max_Size);
   end record;

end Types;
