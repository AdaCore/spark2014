limited with Initializes_Illegal_3;

package Initializes_Illegal_3_Helper
  with Abstract_State => (SH with Part_Of => Initializes_Illegal_3.S2)
is
   Var_H : Integer;
      --  with Part_Of => Initializes_Illegal_3.S2;
end Initializes_Illegal_3_Helper;
