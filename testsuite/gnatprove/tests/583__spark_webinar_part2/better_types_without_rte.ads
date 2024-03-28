package Better_Types_Without_RTE
  with SPARK_Mode
is

   subtype Index is Natural range 0 .. 100;
   subtype Element is Natural;
   type Table is array (Index range <>) of Element;

   Global_Table : Table (1 .. 20);

   procedure Assign
     (A    : in out Table;
      I, J : Index;
      P, Q : Element)
   with
     Pre => I + J in A'Range
       and then Q /= 0;

end Better_Types_Without_RTE;
