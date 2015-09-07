with Serial_Port;
package Terminal
   with Spark_Mode => On
is
   type Status_Type is (Success, Insufficient_Space, Port_Failure);

   procedure Get_Line (Buffer : out String;
                       Count  : out Natural;
                       Status : out Status_Type)
      with
         Global => (Input => (Serial_Port.Port_State,
                              Serial_Port.Data_State)),
         Depends => ((Buffer, Count, Status) => (Buffer,
                                                 Serial_Port.Port_State,
                                                 Serial_Port.Data_State));
end Terminal;
