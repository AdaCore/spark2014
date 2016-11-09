with Numerics; use Numerics;

package Run
with SPARK_Mode => On
is

   subtype T_Float_Value is T_Float range 1.0 .. 100.0;

   procedure Test_Div (X1, X2 : in T_Float;
                       Y : out T_Float);

   procedure Test_Float_Greater (X1, X2 : in T_Float_Value;
                                 Y : out T_Float)
     with Pre => X2 > X1,
          Post => Y /= 0.0;  --  @POSTCONDITION:PASS

   procedure Test_Float_Difference_Greater (X1, X2 : in T_Float_Value;
                                 Y : out T_Float)
     with Pre => X2 - X1 > 0.0,
          Post => Y /= 0.0;  --  @POSTCONDITION:PASS

   procedure Test_Float_Different (X1, X2 : in T_Float_Value;
                                   Y : out T_Float)
     with Pre => X2 /= X1,
          Post => Y /= 0.0;  --  @POSTCONDITION:PASS

   procedure Test_Float_Difference (X1, X2 : in T_Float_Value;
                                    Y : out T_Float)
     with Pre => X2 - X1 /= 0.0,
          Post => Y /= 0.0;  --  @POSTCONDITION:PASS

end Run;
