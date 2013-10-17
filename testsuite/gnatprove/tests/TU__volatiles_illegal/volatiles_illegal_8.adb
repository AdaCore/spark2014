with System.Storage_Elements;

package body Volatiles_Illegal_8
  with SPARK_Mode,
       Refined_State => (State => Non_Vol)  --  Volatile state State has no
                                            --  External constituents.
is
   Non_Vol : Integer;
end Volatiles_Illegal_8;
