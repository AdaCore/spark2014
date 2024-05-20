package Types_Without_RTE
  with SPARK_Mode
is

   subtype Index is Integer;
   subtype Element is Natural;
   type Table is array (Index range <>) of Element;

   procedure Assign
     (A    : in out Table;
      I, J : Index;
      P, Q : Integer)
   with
     Pre => (if J >= 0 then I <= Integer'Last - J else I >= Integer'First - J)
       and then (I + J in A'Range)
       and then (Q /= 0)
       and then (not (P = Integer'First and Q = -1))
       and then (P / Q >= Element'First);

end Types_Without_RTE;
