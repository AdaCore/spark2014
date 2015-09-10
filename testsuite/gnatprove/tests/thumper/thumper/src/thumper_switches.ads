---------------------------------------------------------------------------
-- FILE    : thumper_switches.adb
-- SUBJECT : Specification of a package for managing command line switches.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with Ada.Strings.Unbounded;

package Thumper_Switches is
   use Ada.Strings.Unbounded;

   type Endpoint_Type is (Client, Server);
   type Switch_Type is (Host, Port);

   Switch_Error : exception;

   -- Returns with Valid = True if the command line switches are acceptable for the specified
   -- endpoint (Client or Server). It checks:
   --
   --   a) The command line is in the form of multiple (name, value) pairs.
   --   b) No names are duplicated.
   --   c) Any required switches are present (-h for the client).
   --   d) No illegal switches are present (-h for the server).
   --   e) No unknown switches are present.
   --   f) Optional switches are given default values if necessary (-p).
   --
   -- The syntax of switch values need not be checked. When the procedure returns the Message
   -- parameter contains a human readible error message or "No Error" if the validation was
   -- successful.
   --
   -- This procedure must be called successfully before Get_Switch can be used.
   --
   procedure Validate
     (Endpoint : in      Endpoint_Type;
      Valid    :     out Boolean;
      Message  :     out Unbounded_String);

   -- Return the value associated with the given switch. If the switch was not specified on the
   -- command line a suitable default is returned. Switch_Error is raised if this function is
   -- is used before Validate is called or if Validate returned a failure status.
   --
   function Get_Switch(Switch : Switch_Type) return String;

end Thumper_Switches;
