with Logging; use Logging;

pragma Warnings (Off, "analyzing unreferenced procedure *");

package body Foo
is

   procedure Test_01 (Log : out Log_Type'Class)
   is
   begin
      Log_Type (Log).Init_Log;
      Log.Append_To_Log (2);    -- @INITIALIZED:CHECK
   end Test_01;

   procedure Test_02 (Log : out Log_Type_Public'Class)
   is
   begin
      Log_Type_Public (Log).Init_Log;
      Log.Append_To_Log (2);    -- @INITIALIZED:CHECK
   end Test_02;

   procedure Test_03 (Log : out Log_Type'Class)
   is
   begin
      Log.Init_Log;
      Log.Append_To_Log (2);
   end Test_03;

   procedure Test_04 (Log : out Log_Type_Public'Class)
   is
   begin
      Log.Init_Log;
      Log.Append_To_Log (2);
   end Test_04;

end Foo;
