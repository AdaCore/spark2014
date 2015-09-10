---------------------------------------------------------------------------
-- FILE    : thumper_switches.adb
-- SUBJECT : Body of a package for managing command line switches.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
with Ada.Command_Line;
with Ada.Containers.Ordered_Maps;

use Ada.Command_Line;

package body Thumper_Switches is

   package Switch_Maps is new Ada.Containers.Ordered_Maps
     (Key_Type => Character, Element_Type => Unbounded_String);
   use Switch_Maps;

   Switch_Map : Map;

   procedure Validate
     (Endpoint : in      Endpoint_Type;
      Valid    :     out Boolean;
      Message  :     out Unbounded_String) is

      Argument_Index : Positive;

      procedure Check_Unknown is
         Current : Cursor;
      begin
         Current := Switch_Map.First;
         while Current /= No_Element loop
            case Key(Current) is
               when 'h' | 'p' =>
                  null;

               when others =>
                  Valid := False;
                  Message := To_Unbounded_String("Unknown switch: -" & Key(Current));
            end case;
            Next(Current);
         end loop;
      end Check_Unknown;

      procedure Check_Switch_Semantics is
      begin
         case Endpoint is
            when Client =>
               -- The 'h' switch is required for clients.
               if not Switch_Map.Contains('h') then
                  Valid := False;
                  Message := To_Unbounded_String("The -h switch is required for clients");
               end if;

            when Server =>
               -- The 'h' switch is illegal for servers.
               if Switch_Map.Contains('h') then
                  Valid := False;
                  Message := To_Unbounded_String("The -h switch is illegal for servers");
               end if;
         end case;
      end Check_Switch_Semantics;

   begin
      -- Optimistically assume everything will work.
      Valid := True;
      Message := To_Unbounded_String("No Error");

      -- Defensive programming. Make sure the map is empty.
      Switch_Map.Clear;

      -- There has to be an even number of arguments (could be zero).
      if Argument_Count rem 2 /= 0 then
         Valid := False;
         Message := To_Unbounded_String("Invalid command line syntax");
         return;
      end if;

      -- Build the switch map assocating switch names to their values.
      Argument_Index := 1;
      while Argument_Index < Argument_Count loop
         declare
            Current_Argument : constant String := Argument(Argument_Index);
         begin
            if Current_Argument'Length /= 2 or else Current_Argument(1) /= '-' then
               Valid := False;
               Message := To_Unbounded_String("Invalid switch: " & Current_Argument);
            elsif Switch_Map.Contains(Current_Argument(2)) then
               Valid := False;
               Message := To_Unbounded_String("Duplicate switch: " & Current_Argument);
            else
               Switch_Map.Insert
                 (Current_Argument(2), To_Unbounded_String(Argument(Argument_Index + 1)));
            end if;
         end;
         Argument_Index := Argument_Index + 2;
      end loop;

      -- Set default values for optional switches that apply to both client and server.
      if not Switch_Map.Contains('p') then
         Switch_Map.Insert('p', To_Unbounded_String("318"));
      end if;

      -- Does this collection of switches contain any unknown switches?
      if Valid then
         Check_Unknown;
      end if;

      -- Does this collection of switches make sense?
      if Valid then
         Check_Switch_Semantics;
      end if;
   end Validate;


   function Get_Switch(Switch : Switch_Type) return String is
     (case Switch is
         when Host => To_String(Switch_Map.Element('h')),
         when Port => To_String(Switch_Map.Element('p')));


end Thumper_Switches;
