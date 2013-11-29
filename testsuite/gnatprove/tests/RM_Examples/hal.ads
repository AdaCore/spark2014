-- This is a hardware abstraction layer (HAL)
-- which handles input and output streams over serial interfaces
-- and monitors and resets an area of shared memory used
-- as a watchdog.
package HAL
  with SPARK_Mode,
       Abstract_State =>
              ((FIFO_Status
                  with External => Async_Writers),
               (Serial_In
                  with External => (Async_Writers,
                                    Effective_Reads)),
                  -- Each value received is significant
               (FIFO_Control
                  with External => Async_Readers),
               (Serial_Out
                  with External => (Async_Readers,
                                    Effective_Writes)),
               (Wdog_State
                  with External => (Async_Readers,
                                    Async_Writers)))
is
   type Byte_T is mod 256;

   -- This procedure reads the next byte available on
   -- the serial input port using a FIFO buffer.
   procedure Get_Byte (A_Byte : out Byte_T)
     with Global  => (In_Out => Serial_In),
          Depends => (A_Byte    => Serial_In,
                      Serial_In => null);

   -- This procedure skips input bytes until
   -- the byte matches the given pattern or the input
   -- FIFO is empty.
   procedure Skip_To (Pattern : in Byte_T; Found : out Boolean)
     with Global  => (Input  => FIFO_Status,
                      In_Out => Serial_In),
          Depends => ((Found,
                       Serial_In) => (FIFO_Status,
                                      Pattern,
                                      Serial_In));

   -- This procedure reads the status of the input and output FIFOs.
   procedure Get_FIFO_Status (A_Byte : out Byte_T)
     with Global  => (Input  => FIFO_Status),
          Depends => (A_Byte => FIFO_Status);

   -- This procedure writes a byte to the serial
   -- output port using a FIFO buffer.
   procedure Put_Byte (A_Byte : Byte_T)
     with Global  => (Output => Serial_Out),
          Depends => (Serial_Out => A_Byte);


   -- This procedure clears the input FIFO.
   procedure Clear_In_FIFO
     with Global  => (Output => FIFO_Control),
          Depends => (FIFO_Control => null);


   -- This procedure clears the output FIFO.
   procedure Clear_Out_FIFO
     with Global  => (Output => FIFO_Control),
          Depends => (FIFO_Control => null);


   -- This procedure checks and then resets the status of
   -- the watchdog state.
   procedure Wdog_Timed_Out (Result : out Boolean)
     with Global  => (In_Out => Wdog_State),
          Depends => (Result     => Wdog_State,
                      Wdog_State => Wdog_State);
end HAL;
