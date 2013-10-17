package Functions_Illegal_2
  with SPARK_Mode
is
   function Cant_Have_Formal_Out (Par : out Integer) return Integer;
     --  TU: 5. A function declaration shall not have a
     --  ``parameter_specification`` with a mode of **out** or **in out**. This
     --  rule also applies to a ``subprogram_body`` for a function for which no
     --  explicit declaration is given.

   function Cant_Have_Formal_In_Out (Par : in out Integer) return Integer;
     --  TU: 5. A function declaration shall not have a
     --  ``parameter_specification`` with a mode of **out** or **in out**. This
     --  rule also applies to a ``subprogram_body`` for a function for which no
     --  explicit declaration is given.

end Functions_Illegal_2;
