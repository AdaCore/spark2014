with System.Storage_Elements;

package body HAL
  with SPARK_Mode,
       Refined_State => (Serial_In    => Read_FIFO,
                         Serial_Out   => Write_FIFO,
                         FIFO_Status  => Status,
                         FIFO_Control => Control,
                         Wdog_State   => Wdog_Shared_memory)
is
   -- Each byte read is significant, it is a sequence of bytes
   -- and so Effective_Reads => True.
   Read_FIFO: Byte_T
     with Volatile,
          Async_Writers,
          Effective_Reads,
          Address => System.Storage_Elements.To_Address(16#A1CAFE0#);

   -- Each byte written is significant, it is a sequence of bytes
   -- and so Effective_Writes => True.
   Write_FIFO: Byte_T
     with Volatile,
          Async_Readers,
          Effective_Writes,
          Address => System.Storage_Elements.To_Address(16#A2CAFE0#);

   -- The read of the FIFO status is a snap shot of the current status
   -- individual reads are independent of other reads of the FIFO status
   -- and so Effective_Reads => False.
   Status: Byte_T
     with Volatile,
          Async_Writers,
          Address => System.Storage_Elements.To_Address(16#A3CAFE0#);

   -- The value written to the FIFO control register are independent
   -- of other value written to the control register and so
   -- Effective_Writes => False.
   Control: Byte_T
     with Volatile,
          Async_Readers,
          Address => System.Storage_Elements.To_Address(16#A4CAFE0#);

   -- This is a bidirectional port but individual reads and writes
   -- are independent and so Effective_Reads and Effective_Writes
   -- are both False.
   Wdog_Shared_Memory : Boolean
     with Volatile,
          Async_Writers,
          Async_Readers,
          Address => System.Storage_Elements.To_Address(16#A5CAFE0#);

   procedure Get_Byte (A_Byte : out Byte_T)
     with Refined_Global  => (In_Out    => Read_FIFO),
          Refined_Depends => (A_Byte    => Read_FIFO,
                              Read_FIFO => null)
   is
   begin
      A_Byte := Read_FIFO;
   end Get_Byte;

   procedure Skip_To (Pattern : in Byte_T; Found : out Boolean)
     with Refined_Global  => (Input  => Status,
                              In_Out => Read_FIFO),
          Refined_Depends => ((Found,
                               Read_FIFO) => (Status,
                                              Pattern,
                                              Read_FIFO))
   is
      Read_FIFO_Empty : constant Byte_T := 16#010#;
      Current_Status : Byte_T;
      Next_Byte : Byte_T;
   begin
      Found := False;
      loop
         Get_FIFO_Status (Current_Status);
         exit when Current_Status = Read_FIFO_Empty;
         Get_Byte (Next_Byte);
         exit when Next_Byte = Pattern;
      end loop;
   end Skip_To;

   procedure Get_FIFO_Status (A_Byte : out Byte_T)
     with Refined_Global  => (Input  => Status),
          Refined_Depends => (A_Byte => Status)
   is
   begin
      A_Byte := Status;
   end Get_FIFO_Status;

   procedure Put_Byte (A_Byte : Byte_T)
     with Refined_Global  => (Output => Write_FIFO),
          Refined_Depends => (Write_FIFO => A_Byte)
   is
   begin
      Write_FIFO := A_Byte;
   end Put_Byte;

   procedure Clear_In_FIFO
     with Refined_Global  => (Output => Control),
          Refined_Depends => (Control => null)
   is
      In_FIFO_Clear : constant Byte_T := 16#010#;
   begin
      Control := In_FIFO_Clear;
   end Clear_In_FIFO;

   procedure Clear_Out_FIFO
     with Refined_Global  => (Output => Control),
          Refined_Depends => (Control => null)
   is
      Out_FIFO_Clear : constant Byte_T := 16#020#;
   begin
      Control := Out_FIFO_Clear;
   end Clear_Out_FIFO;

   procedure Wdog_Timed_Out (Result : out Boolean)
     with Refined_Global  => (In_Out => Wdog_Shared_Memory),
          Refined_Depends => (Result             => Wdog_Shared_Memory,
                              Wdog_Shared_memory => Wdog_Shared_Memory)
   is
      Watch_Dog_OK : Boolean;
   begin
      Watch_Dog_OK := Wdog_Shared_Memory;
      if Watch_Dog_OK then
         -- Retrigger the watch dog timer
         Wdog_shared_memory := True;
         -- It has not timed out.
         Result := False;
      else
         Result := True;
      end if;
   end Wdog_Timed_Out;

end HAL;
