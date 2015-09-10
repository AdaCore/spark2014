---------------------------------------------------------------------------
-- FILE    : client_gui.ads
-- SUBJECT : Specification of a package for the client GUI.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with Gtk.Widget;
with Gtk.Handlers;

use Gtk.Widget;

package Client_GUI is

   package Handlers is new Gtk.Handlers.Callback(Widget_Type => Gtk_Widget_Record);

   package Return_Handlers is new Gtk.Handlers.Return_Callback
     (Widget_Type => Gtk_Widget_Record,
      Return_Type => Boolean);

   procedure Fetch_Timestamp_Callback(Widget : access Gtk_Widget_Record'Class);

   procedure Check_Timestamp_Callback(Widget : access Gtk_Widget_Record'Class);

   procedure Destroy(Widget : access Gtk_Widget_Record'Class);

end Client_GUI;
