---------------------------------------------------------------------------
-- FILE    : client_gui.adb
-- SUBJECT : Body of a package for the client GUI.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with Gtk.Main;
with GtkAda.File_Selection;
with Client_SPARK_Boundary;

use GtkAda.File_Selection;
use Client_SPARK_Boundary;

package body Client_GUI is

   --  This is a callback function.

   procedure Fetch_Timestamp_Callback(Widget : access Gtk_Widget_Record'Class) is
      pragma Unreferenced(Widget);

      Document_File_Name: constant String :=
        File_Selection_Dialog(Title => "Select File", Must_Exist => True);

      Timestamp_File: constant String := Document_File_Name & ".tsp";
   begin
      Fetch_Timestamp(Document_File_Name, TimeStamp_File);
   end Fetch_Timestamp_Callback;


   procedure Check_Timestamp_Callback(Widget : access Gtk_Widget_Record'Class) is
      pragma Unreferenced (Widget);

      Document_File_Name: constant String :=
        File_Selection_Dialog(Title => "Select File", Must_Exist => True);

      Timestamp_File: constant String := Document_File_Name & ".tsp";
   begin
      if not Check_Timestamp(Document_File_Name, Timestamp_File) then
         -- TODO: Added some kind of error reporting.
         null;
      end if;
   end Check_Timestamp_Callback;


   --   Another callback
   procedure Destroy(Widget : access Gtk_Widget_Record'Class) is
      pragma Unreferenced(Widget);
   begin
      Gtk.Main.Main_Quit;
   end Destroy;

end Client_GUI;

