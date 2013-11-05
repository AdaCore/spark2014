package Output_Port
  --# own out Outputs : Integer;
is
   procedure Write_To_Port(Output_Value : in Integer);
   --# global out Outputs;
   --# derives Outputs from Output_Value;
   --# post ((Output_Value = -1) ->
   --#        (Outputs =
   --#           Outputs'Append (Outputs'Append (Outputs~, 0), Output_Value)))
   --#  and
   --#      ((Output_Value /= -1) ->
   --#         (Outputs =
   --#           Outputs'Append (Outputs~, Output_Value)));
end Output_Port;
