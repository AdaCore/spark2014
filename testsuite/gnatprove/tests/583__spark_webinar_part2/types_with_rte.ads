package Types_With_RTE
  with SPARK_Mode
is

   subtype Index is Integer;
   subtype Element is Natural;
   type Table is array (Index range <>) of Element;

   procedure Assign
     (A    : in out Table;
      I, J : Index;
      P, Q : Integer);

end Types_With_RTE;
