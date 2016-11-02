package Test_03 with
   Elaborate_Body,
   Abstract_State => (State_N,
                      (State_AWER with External => (Async_Readers,
                                                    Async_Writers)),
                      (State_ER with External => (Async_Readers,
                                                  Async_Writers,
                                                  Effective_Reads)),
                      (State_EW with External => (Async_Readers,
                                                  Async_Writers,
                                                  Effective_Writes)),
                      (State_V  with External))
is
end Test_03;
