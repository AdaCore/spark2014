with System; use System;
package Kernel with SPARK_Mode is
    procedure Vector_Add
      (A_Addr : System.Address;
       B_Addr : System.Address;
       C_Addr : System.Address;
       Num_Elements : Integer)
      with CUDA_Global;
end Kernel;
