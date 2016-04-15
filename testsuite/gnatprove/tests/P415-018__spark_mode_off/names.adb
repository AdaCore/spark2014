package body Names with
   SPARK_Mode => Off
is

   type Char_Table_Index is range 1 .. 10;

   type Name_Entry is record
      Table_Index : Char_Table_Index;
   end record with
      Predicate =>
        (Name_Entry.Table_Index <= 10);

end Names;
