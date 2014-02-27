package Function_Depends_On_State
  with SPARK_Mode,
       Abstract_State => (S, S2, S_Null, S_Null2),
       Initializes    => (S, S2, S_Null, S_Null2)
is
   function F1 return Integer
     with Global  => (S_Null),
          Depends => (F1'Result => S_Null);

   function F2 return Integer
     with Global  => (S_Null),
          Depends => (F2'Result => S_Null);

   function F3 return Integer
     with Global  => (S, S2, S_Null, S_Null2),
          Depends => (F3'Result => (S, S2, S_Null, S_Null2));
end Function_Depends_On_State;
