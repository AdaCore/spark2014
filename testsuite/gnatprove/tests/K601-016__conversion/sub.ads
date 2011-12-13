package Sub is
   type Ext_Dir is (Absent, Left, Right);
   subtype Dir is Ext_Dir range Left .. Right;
   type Dir2 is new Ext_Dir range Left .. Right;

   procedure P (X : Dir);
end Sub;
