with Ada.Characters.Latin_1;
with Ada.Unchecked_Conversion;
with Interfaces.C;
with System;
with Win32;
with Win32.Winnt;
with Win32.Winbase;

package body Serial_Port
  with SPARK_Mode => Off is

   use type System.Address;
   use type Win32.BOOL;
   use type Interfaces.C.unsigned_long;

   -- Package can work with either of these ports, but only one at a time.
   type Port_Type is (COM1, COM2);

   Current_Port  : Win32.Winnt.HANDLE := System.Null_Address;
   Old_Settings, New_Settings : aliased Win32.Winbase.DCB;
   Old_Timeouts, New_Timeouts : aliased Win32.Winbase.COMMTIMEOUTS;

   Input_Byte    : aliased Byte;         -- Data byte from ReadFile.
   Output_Byte   : aliased Byte;         -- Data byte to WriteFile.
   Bytes_Read    : aliased Win32.DWORD;  -- # of bytes read by ReadFile.
   Bytes_Written : aliased Win32.DWORD;  -- # of bytes written by WriteFile.

   type Byte_Pointer is access all Byte;
   function Convert_Address is
      new Ada.Unchecked_Conversion (Source => Byte_Pointer, Target => System.Address);

   -- Look up tables for easy access to raw settings values.

   Port_Table : constant array (Port_Type) of String (1 .. 5) :=
     ("COM1" & Ada.Characters.Latin_1.NUL, "COM2" & Ada.Characters.Latin_1.NUL);

   Baud_Table : constant array (Baud_Type) of Win32.DWORD :=
     (2400, 4800, 9600, 19200);

   Parity_Table : constant array (Parity_Type) of Win32.BYTE :=
     (Win32.Winbase.NOPARITY, Win32.Winbase.EVENPARITY, Win32.Winbase.ODDPARITY);

   Data_Size_Table : constant array (Data_Size_Type) of Win32.BYTE :=
     (7, 8);

   Stop_Table : constant array (Stop_Type) of Win32.BYTE :=
     (Win32.Winbase.ONESTOPBIT, Win32.Winbase.TWOSTOPBITS);


   procedure Open (Baud      : in  Baud_Type;
                   Parity    : in  Parity_Type;
                   Data_Size : in  Data_Size_Type;
                   Stop      : in  Stop_Type;
                   Status    : out Status_Type) is

      Dummy_Result : Win32.BOOL;
      Port         : constant Port_Type := COM1;  -- Only work with COM1 for purposes of demonstration.
   begin
      Status := Success;

      -- If a port is already open, report an error.
      if Current_Port /= System.Null_Address then
         Status := Open_Failure;
         return;
      end if;

      Current_Port := Win32.Winbase.CreateFile
        (lpFileName            => Win32.Addr (Port_Table (Port)),
         dwDesiredAccess       => Win32.Winnt.GENERIC_READ or Win32.Winnt.GENERIC_WRITE,
         dwShareMode           => 0,
         lpSecurityAttributes  => null,
         dwCreationDisposition => Win32.Winbase.OPEN_EXISTING,
         dwFlagsAndAttributes  => 0,
         hTemplateFile         => System.Null_Address);

      -- Check for success.
      if Current_Port = Win32.Winbase.INVALID_HANDLE_VALUE then
         Current_Port := System.Null_Address;
         Status := Open_Failure;
         return;
      end if;

      -- Get the current port settings.
      if Win32.Winbase.GetCommState (Current_Port, Old_Settings'Access) = Win32.FALSE then
         Dummy_Result := Win32.Winbase.CloseHandle (Current_Port);
         Current_Port := System.Null_Address;
         Status := Open_Failure;
         return;
      end if;

      -- Get the current port timeouts.
      if Win32.Winbase.GetCommTimeouts (Current_Port, Old_Timeouts'Access) = Win32.FALSE then
         Dummy_Result := Win32.Winbase.CloseHandle (Current_Port);
         Current_Port := System.Null_Address;
         Status := Open_Failure;
         return;
      end if;

      New_Settings := Old_Settings;
      New_Timeouts := Old_Timeouts;

      -- Adjust the settings.
      New_Settings.BaudRate := Baud_Table (Baud);
      New_Settings.fBinary  := Win32.TRUE;
      if Parity = None then
         New_Settings.fParity := Win32.FALSE;
      else
         New_Settings.fParity := Win32.TRUE;
      end if;
      New_Settings.fOutxCtsFlow    := Win32.FALSE;
      New_Settings.fOutxDsrFlow    := Win32.FALSE;
      New_Settings.fDtrControl     := Win32.Winbase.DTR_CONTROL_ENABLE;
      New_Settings.fDsrSensitivity := Win32.FALSE;
      New_Settings.fOutX           := Win32.FALSE;
      New_Settings.fInX            := Win32.FALSE;
      New_Settings.fErrorChar      := Win32.FALSE;
      New_Settings.fNull           := Win32.FALSE;
      New_Settings.fRtsControl     := Win32.Winbase.RTS_CONTROL_ENABLE;
      New_Settings.fAbortOnError   := Win32.FALSE;
      New_Settings.ByteSize        := Data_Size_Table (Data_Size);
      New_Settings.Parity          := Parity_Table (Parity);
      New_Settings.StopBits        := Stop_Table (Stop);

      if Win32.Winbase.SetCommState (Current_Port, New_Settings'Access) = Win32.FALSE then
         Dummy_Result := Win32.Winbase.CloseHandle (Current_Port);
         Current_Port := System.Null_Address;
         Status := Open_Failure;
         return;
      end if;

      -- Adjust the timeouts.
      -- TODO: Make adjustments to the port's timeouts?
   end Open;


   procedure Read (Item  : out Byte;
                   Status : out Status_Type) is
   begin
      Item := 0;
      Status := Success;

      if Current_Port = System.Null_Address then
         Status := IO_Failure;
         return;
      end if;

      if Win32.Winbase.ReadFile
         (hFile                => Current_Port,
          lpBuffer             => Convert_Address (Input_Byte'Access),
          nNumberOfBytesToRead => 1,
          lpNumberOfBytesRead  => Bytes_Read'Access,
          lpOverlapped         => null) = Win32.FALSE then

         Status := IO_Failure;
         return;
      end if;

      Item := Input_Byte;
   end Read;


   procedure Write (Item   : in Byte;
                    Status : out Status_Type) is
   begin
      Status := Success;

      if Current_Port = System.Null_Address then
         Status := IO_Failure;
         return;
      end if;

      Output_Byte := Item;
      if Win32.Winbase.WriteFile
         (hFile                  => Current_Port,
          lpBuffer               => Convert_Address (Output_Byte'Access),
          nNumberOfBytesToWrite  => 1,
          lpNumberOfBytesWritten => Bytes_Written'Access,
          lpOverlapped           => null) = Win32.FALSE then

         Status := IO_Failure;
         return;
      end if;
   end Write;


   procedure Close is
      Dummy_Result : Win32.BOOL;
   begin
      if Current_Port = System.Null_Address then
         return;
      end if;
      Dummy_Result := Win32.Winbase.SetCommState (Current_Port, Old_Settings'Access);
      Dummy_Result := Win32.Winbase.SetCommTimeouts (Current_Port, Old_Timeouts'Access);
      Dummy_Result := Win32.Winbase.CloseHandle (Current_Port);
      Current_Port := System.Null_Address;
   end Close;


end Serial_Port;
