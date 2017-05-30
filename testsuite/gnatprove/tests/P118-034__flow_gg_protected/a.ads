package A with
   Abstract_State => (State_A with External => (Async_Readers, Async_Writers))
is

   procedure Access_A_In (X : out Boolean);
   procedure Access_A_In_Out;
   procedure Access_A_Out;

end A;
