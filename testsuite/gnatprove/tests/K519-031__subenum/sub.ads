package Sub is
   type Ext_Dir is (Absent, Left, Right);
   subtype Dir is Ext_Dir range Left .. Right;
   type Dir2 is new Ext_Dir range Left .. Right;

   function Remove_Absent (X : Ext_Dir) return Dir
      with Post =>
         (if X = Right then Remove_Absent'Result = Right);

   function Remove_Absent (X : Ext_Dir) return Dir2
      with Post =>
         (if X = Right then Remove_Absent'Result = Right);
end Sub;
