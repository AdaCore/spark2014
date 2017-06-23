package Lib.Cont is

   type T_Count is
      new T_Natural_32;

   subtype T_C is
      T_Count range 1 .. T_Count'Last;

end Lib.Cont;
