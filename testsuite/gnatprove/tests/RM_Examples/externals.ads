package Externals
  with SPARK_Mode,
       Abstract_State => ((Combined_Inputs with External => Async_Writers),
                          (Displays with External => Async_Readers),
                          (Complex_Device with External => (Async_Readers,
                                                            Effective_Writes,
                                                            Async_Writers))),
       Initializes    => Complex_Device
is
   procedure Read (Combined_Value : out Integer)
     with Global  => Combined_Inputs,  -- Combined_Inputs is an Input;
                                       -- it does not have Effective_Reads and
                                       -- may be an specified just as an
                                       -- Input in Global and Depends aspects.
          Depends => (Combined_Value => Combined_Inputs);

   procedure Display (D_Main, D_Secondary : in String)
     with Global  => (Output => Displays), -- Displays is an Output and may
                                           -- be specified just as an
                                           -- Output in Global and Depends
                                           -- aspects.
          Depends => (Displays => (D_Main, D_Secondary));

   function Last_Value_Sent return Integer
     with Volatile_Function,
          Global => Complex_Device;  -- Complex_Device is an External state.
                                     -- It does not have Effective_Reads and
                                     -- may be an specified as a global_item of
                                     -- a volatile function.

   procedure Output_Value (Value : in Integer)
     with Global  => (In_Out => Complex_Device),
          Depends => (Complex_Device => (Complex_Device, Value));
   -- Output_Value only sends out a value if it is not the same
   -- as the last value sent.  When a value is sent it updates
   -- the saved value and has to check a status port.
   -- The subprogram must be a procedure.

end Externals;
