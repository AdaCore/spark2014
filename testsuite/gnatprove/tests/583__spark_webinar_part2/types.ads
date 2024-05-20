package Types
  with SPARK_Mode
is

   subtype Index is Natural range 0 .. 100;
   subtype Element is Natural;
   type Table is array (Index range <>) of Element;

   procedure Assign
     (A : in out Table;
      I : Index;
      P : Element)
   with
     Pre => I in A'Range;

end Types;
