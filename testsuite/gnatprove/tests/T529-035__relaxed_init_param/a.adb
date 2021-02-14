package body A with SPARK_Mode is

   procedure Tcp_Receive (Data : out char_array)is
      procedure Tcp_Read_Rx_Buffer
        (Data    : out char_array)
        with
          Import => True,
          Relaxed_Initialization => Data,
          Pre => Data'First <= Data'Last,
          Post =>
            Data(Data'First .. Data'Last)'Initialized;
   begin
      Tcp_Read_Rx_Buffer(Data);
   end Tcp_Receive;

end A;
