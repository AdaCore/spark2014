package P_14
  with SPARK_Mode,
       Abstract_State => P_State,
       Initializes    => (P_State, Global_Var)
is
   Global_Var : Integer;

   procedure Init (S : out Integer);
end P_14;
