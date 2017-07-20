with Ada.Real_Time; use Ada.Real_Time;

with System;

package body Test_02 with
   Refined_State => (State => (Database, Updater))
is

   task Updater;

   protected Database is
      procedure Update_Cache;
      function Get_Cache return Integer;
   private
      Cache : Integer := Integer'First;
   end Database;

   Sensor : Integer with
     Part_Of => Database,
     Volatile,
     Async_Readers, Effective_Writes,
     Address => System'To_Address (16#DEADBEEF#),
     Import;

   protected body Database is
      procedure Update_Cache is
      begin
         Cache := Sensor;
      end Update_Cache;

      function Get_Cache return Integer is
      begin
         return Cache;
      end Get_Cache;
   end Database;

   task body Updater is
      T : Time := Clock;
   begin
      loop
         T := T + Seconds (1);
         Database.Update_Cache;
         delay until T;
      end loop;
   end Updater;

   function Get_Reading return Integer
   with Refined_Global => Database
   is
   begin
      return Database.Get_Cache;
   end Get_Reading;

end Test_02;
