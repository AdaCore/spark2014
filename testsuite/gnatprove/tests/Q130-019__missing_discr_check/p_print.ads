with P_Init; use P_Init;

package P_Print with SPARK_Mode is

   procedure Print (Name : in String;
                    Y    : in T)
     with Global => null;

end P_Print;
