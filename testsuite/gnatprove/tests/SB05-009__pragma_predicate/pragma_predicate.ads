package Pragma_Predicate
with
   SPARK_Mode
is
   type Tuple_Type is
   record
      X, Y : Natural;
   end record;
   -- with
   --    Predicate => Tuple_Type.X >= Tuple_Type.Y;
   pragma Predicate
      (Entity => Tuple_Type,
       Check  => Tuple_Type.X >= Tuple_Type.Y);

   procedure Inc_X (Tuple : in out Tuple_Type)
   with
      Pre => Tuple.X < Natural'Last;

   procedure Maybe_Inc_Y (Tuple : in out Tuple_Type)
   with
      Pre => Tuple.Y < Natural'Last;
end Pragma_Predicate;
