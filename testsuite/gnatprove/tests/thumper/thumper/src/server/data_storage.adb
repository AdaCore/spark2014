---------------------------------------------------------------------------
-- FILE    : data_storage.adb
-- SUBJECT : Body of an abstract data base interface package for Thumper.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------

-- TODO: Remove dependency on Ada.Text_IO. Use a real logger.
with Ada.Text_IO;
with Postgresql;

use Ada.Text_IO;
use Postgresql;


package body Data_Storage is

   procedure Initialize is
   begin
      Postgresql.Connect("Thumper", 5432, "localhost", "postgres", "football99");
      Put_Line("Connected to the Database.");
   end Initialize;


   procedure Shutdown is
   begin
      Postgresql.Disconnect;
      Put_Line("Disconnected From the Database");
   end Shutdown;


   function Timestamp_Count return Count_Type is
   begin
      -- TODO: Add proper query.
      return Count_Type'Value(Get_Value(0,0));
   end Timestamp_Count;


   procedure Timestamp_Store(Stamp : in Timestamp) is
   begin
      raise Program_Error with "Data_Storage.Timestamp_Store not implemented";
   end Timestamp_Store;


   function Timestamp_Retrieve(Serial_Number : Serial_Number_Type) return Timestamp_Array is
   begin
      -- TODO: Add proper query.
      declare
         Result: Timestamp_Array(1 .. PostgreSQL.Number_Of_Tuples);
      begin
         return Result;
      end;
   end Timestamp_Retrieve;


   function Timestamp_Retrieve(Start : Time; Stop : Time) return Timestamp_Array is
      Dummy : Timestamp_Array(1 .. 0);
   begin
      return Dummy;
   end Timestamp_Retrieve;

end Data_Storage;
