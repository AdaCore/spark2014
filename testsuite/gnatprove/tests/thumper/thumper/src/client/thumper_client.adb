---------------------------------------------------------------------------
-- FILE    : thumper_client.adb
-- SUBJECT : Main procedure of the Thumper client.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin and Nancy Mai
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with Network.Socket;
with Client_GUI;

with Gtk.Main;
with Gtk.Window;
with GtkAda.File_Selection;
with Gtk.Button;
with Gtk.Box;
with Gtk.Button_Box;
with Gtk.Frame;
with Gtk.Image;

use Gtk.Main;
use Gtk.Window;
use GtkAda.File_Selection;
use Gtk.Button;
use Gtk.Box;
use Gtk.Button_Box;
use Gtk.Frame;
use Gtk.Image;

use Client_GUI;

procedure Thumper_Client is
   Window : Gtk_Window;
   Button : Gtk_Button;
   Bbox  : Gtk_Box;
   Hbox  : Gtk_Box;
   Frame : Gtk_Frame;
   Image : Gtk_Image;
begin
   Network.Socket.Create_Socket;

   Init;

   -- Create a new window
   Gtk_New(Window);
   Gtk_New(Frame);
   Gtk_New_Vbox(Bbox, Homogeneous => False, Spacing => 0);
   Gtk_New_Vbox(Hbox, Homogeneous => False, Spacing => 0);
   Frame.Add(Hbox);
   Gtk_New(Image, "Thumper.png");
   Pack_Start(Hbox, Child => Image, Expand => True, Fill => True, Padding => 0);
   Pack_Start(Hbox, Child => Bbox, Expand => True, Fill => True, Padding => 0);

   Gtk_New(Button, " Fetch Timestamp ");
   Handlers.Connect
     (Button, "clicked", Handlers.To_Marshaller (Fetch_Timestamp_Callback'Access));
   Pack_Start(Bbox, Child => Button, Expand => False, Fill => False, Padding => 5);

   Gtk_New (Button, " Check Timestamp ");
   Handlers.Connect
     (Button, "clicked", Handlers.To_Marshaller (Check_Timestamp_Callback'Access));
   Pack_Start(Bbox, Child => Button, Expand => False, Fill => False, Padding =>5);

   Handlers.Connect
     (Window, "destroy", Handlers.To_Marshaller (Destroy'Access));

   Add(Window, Frame);
   Window.Show_All;

   Gtk.Main.Main;
end Thumper_Client;

