package body Functions_Illegal_2
  with SPARK_Mode
is
   function Cant_Have_Formal_Out (Par : out Integer) return Integer is
   begin
      Par := 1;
      return Par;
   end Cant_Have_Formal_Out;

   function Cant_Have_Formal_In_Out (Par : in out Integer) return Integer is
   begin
      Par := Par + 1;
      return Par;
   end Cant_Have_Formal_In_Out;

   function Only_Body_Cant_Have_Formal_Out (Par : out Integer) return Integer
   is
     --  TU: 5. A function declaration shall not have a
     --  ``parameter_specification`` with a mode of **out** or **in out**. This
     --  rule also applies to a ``subprogram_body`` for a function for which no
     --  explicit declaration is given.
   begin
      Par := 1;
      return Par;
   end Only_Body_Cant_Have_Formal_Out;

   function Only_Body_Cant_Have_Formal_In_Out (Par : in out Integer)
                                              return Integer is
     --  TU: 5. A function declaration shall not have a
     --  ``parameter_specification`` with a mode of **out** or **in out**. This
     --  rule also applies to a ``subprogram_body`` for a function for which no
     --  explicit declaration is given.
   begin
      Par := Par + 1;
      return Par;
   end Only_Body_Cant_Have_Formal_In_Out;
end Functions_Illegal_2;
