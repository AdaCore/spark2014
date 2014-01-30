package Tests_External_State
  with SPARK_Mode,
       Abstract_State => ((State       with External),
                          (State_AR    with External => Async_Readers),
                          (State_AR_EW with External => (Async_Readers,
                                                         Effective_Writes)),
                          (State_AW    with External => Async_Writers),
                          (State_AW_ER with External => (Async_Writers,
                                                         Effective_Reads))),
       Initializes    => (State_AR, State_AR_EW)
       --  State, State_AW and State_AW_EF are considered to be initialized
       --  since they have Async_Writers.
is
   --  State has all external aspects

   procedure Set (X : Integer)
     with Global  => (Output => State),
          Depends => (State => X);

   procedure Get (X : out Integer)
     with Global  => (In_Out => State),
          Depends => ((X, State) => State);


   --  State_AR has only Async_Readers

   procedure Set_AR (X : Integer)
     with Global  => (Output => State_AR),
          Depends => (State_AR => X);

   procedure Get_AR (X : out Integer)
     with Global  => State_AR,
          Depends => (X => State_AR);


   --  State_AR_EW has Async_Readers and Effective_Writes

   procedure Set_AR_EW (X : Integer)
     with Global  => (Output => State_AR_EW),
          Depends => (State_AR_EW => X);

   procedure Get_AR_EW (X : out Integer)
     with Global  => State_AR_EW,
          Depends => (X => State_AR_EW);


   --  State_AW has Async_Writers

   procedure Set_AW (X : Integer)
     with Global  => (Output => State_AW),
          Depends => (State_AW => X);

   procedure Get_AW (X : out Integer)
     with Global  => State_AW,
          Depends => (X => State_AW);


   --  State_AW_ER has Async_Writers and Effective_Reads

   procedure Set_AW_ER (X : Integer)
     with Global  => (Output => State_AW_ER),
          Depends => (State_AW_ER => X);

   procedure Get_AW_ER (X : out Integer)
     with Global  => (In_Out => State_AW_ER),
          Depends => ((X, State_AW_ER) => State_AW_ER);
end Tests_External_State;
