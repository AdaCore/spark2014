with Ada.Text_IO; use Ada.Text_IO;
with Ada.Unchecked_Deallocation;

with Logging_Storage_Models; use Logging_Storage_Models;
with Test_Support; use Test_Support;

procedure Main is
   type Device_Array_Access is access Integer_Array
     with Designated_Storage_Model => Logging_Storage_Models.No_Model;

   procedure Free is new Ada.Unchecked_Deallocation
     (Integer_Array, Device_Array_Access);

   Device_Array : Device_Array_Access;
   Prev_Count : Integer;
begin
   Model.Display_Log := True;

   Put_Line ("Initialize device");

   Device_Array := new Integer_Array (1 .. 10);

   Host_Array.all := Test_Array_Value;

   Put_Line ("Copy from host to device");

   Prev_Count := Model.Count_Write;
   Device_Array.all := Host_Array.all;

   Host_Array.all := Test_Array_Reset;

   Put_Line ("Copy from device to host");

   Prev_Count := Model.Count_Read;
   pragma Assert (Host_Array.all /= Test_Array_Value);
   Host_Array.all := Device_Array.all;
   pragma Assert (Host_Array.all = Test_Array_Value);

   Free (Host_Array);

   Put_Line ("Free device");

   Free (Device_Array);
end;
