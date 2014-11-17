with Init;
pragma Elaborate_All(Init);

package Init_2
  with SPARK_Mode,
       Initializes       => (X => Init.A,
                             Y => Init.State),
       Initial_Condition => X + Y = 0
is
   X : Integer := Init.A;          --  OK
   Y : Integer := Init.Sum_State;  --  OK
   Z : Integer;                    --  OK
end Init_2;
