package body Initializing_State_Abstractions with
  Refined_State => (State_A => (A_1, A_2),
                    State_B => (B_1, B_2))
is
   A_1 : Integer;
   A_2 : Integer with Volatile, Async_Writers;
   B_1 : Integer;
   B_2 : Integer := 0;
end Initializing_State_Abstractions;
