------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                  F L O W _ E R R O R _ M E S S A G E S                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013, Altran UK Limited                   --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Strings.Unbounded;   use Ada.Strings.Unbounded;

with Errout;                  use Errout;

with Flow;                    use Flow;

package body Flow_Error_Messages is

   use type Ada.Containers.Count_Type;
   use type Flow_Graphs.Vertex_Id;
   use type Flow_Id_Sets.Set;

   function Escape (S : Unbounded_String)
                    return Unbounded_String
     with Post => Length (Escape'Result) >= Length (S);
   --  Escape any special characters used in the error message (for
   --  example transforms "=>" into "='>" as > is a special insertion
   --  character.

   function Substitute (S : Unbounded_String;
                        F : Flow_Id)
                        return Unbounded_String;
   --  Find the first '&' or '#' and substitute with the given flow
   --  id, with or without enclosing quotes respectively.

   ------------
   -- Escape --
   ------------

   function Escape (S : Unbounded_String)
                    return Unbounded_String
   is
      R : Unbounded_String := Null_Unbounded_String;
   begin
      for Index in Positive range 1 .. Length (S) loop
         if Element (S, Index) in '%' | '$' | '{' | '*' | '&' |
           '#' | '}' | '@' | '^' | '>' |
           '!' | '?' | '<' | '`' | ''' | '\' | '|' | '~'
         then
            Append (R, "'");
         end if;
         Append (R, Element (S, Index));
      end loop;
      return R;
   end Escape;

   ----------------
   -- Substitute --
   ----------------

   function Substitute (S : Unbounded_String;
                        F : Flow_Id)
                        return Unbounded_String
   is
      R      : Unbounded_String := Null_Unbounded_String;
      Do_Sub : Boolean          := True;
      Quote  : Boolean;
   begin
      for Index in Positive range 1 .. Length (S) loop
         if Do_Sub and then Element (S, Index) in '&' | '#' then
            Quote := Element (S, Index) = '&';
            case  F.Kind is
               when Null_Value =>
                  Append (R, "NULL");

               when Direct_Mapping | Record_Field =>
                  if Quote then
                     Append (R, """");
                  end if;
                  Append (R, Flow_Id_To_String (F));
                  if Quote then
                     Append (R, """");
                  end if;

               when Magic_String =>
                  --  ??? we may want to use __gnat_decode() here instead
                  if F.Name.all = "__HEAP" then
                     if Quote then
                        Append (R, """the heap""");
                     else
                        Append (R, "the heap");
                     end if;
                  else
                     if Quote then
                        Append (R, """");
                     end if;
                     declare
                        Index : Positive := 1;
                     begin
                        --  Replace __ with . in the magic string.
                        while Index <= F.Name.all'Length loop
                           case F.Name.all (Index) is
                              when '_' =>
                                 if Index < F.Name.all'Length and then
                                   F.Name.all (Index + 1) = '_' then
                                    Append (R, ".");
                                    Index := Index + 2;
                                 else
                                    Append (R, '_');
                                    Index := Index + 1;
                                 end if;

                              when others =>
                                 Append (R, F.Name.all (Index));
                                 Index := Index + 1;
                           end case;
                        end loop;
                     end;
                     if Quote then
                        Append (R, """");
                     end if;
                  end if;

            end case;
            Do_Sub := False;

         else
            Append (R, Element (S, Index));
         end if;
      end loop;
      return R;
   end Substitute;

   --------------------
   -- Error_Msg_Flow --
   --------------------

   procedure Error_Msg_Flow (Msg     : String;
                             N       : Node_Id;
                             Tag     : String := "";
                             Warning : Boolean := False)

   is
      M : Unbounded_String := Escape (To_Unbounded_String (Msg));
   begin
      --  Assemble message string to be passed to Error_Msg_N
      if Tag'Length >= 1 then
         Append (M, " '[" & Tag & "']");
      end if;
      Append (M, "!!");
      if Warning then
         Append (M, '?');
      end if;

      --  Issue error message
      Error_Msg_N (To_String (M), N);
   end Error_Msg_Flow;

   procedure Error_Msg_Flow (Msg     : String;
                             N       : Node_Id;
                             F1      : Flow_Id;
                             Tag     : String := "";
                             Warning : Boolean := False)
   is
      M : Unbounded_String;
   begin
      --  Assemble message string to be passed to Error_Msg_N
      M := Escape (Substitute (To_Unbounded_String (Msg),
                               F1));
      if Tag'Length >= 1 then
         Append (M, " '[" & Tag & "']");
      end if;
      Append (M, "!!");
      if Warning then
         Append (M, '?');
      end if;

      --  Issue error message
      Error_Msg_N (To_String (M), N);
   end Error_Msg_Flow;

   procedure Error_Msg_Flow (Msg     : String;
                             N       : Node_Id;
                             F1      : Flow_Id;
                             F2      : Flow_Id;
                             Tag     : String := "";
                             Warning : Boolean := False)
   is
      M : Unbounded_String;
   begin
      --  Assemble message string to be passed to Error_Msg_N
      M := Escape (Substitute (Substitute (To_Unbounded_String (Msg),
                                           F1),
                               F2));
      if Tag'Length >= 1 then
         Append (M, " '[" & Tag & "']");
      end if;
      Append (M, "!!");
      if Warning then
         Append (M, '?');
      end if;

      --  Issue error message
      Error_Msg_N (To_String (M), N);
   end Error_Msg_Flow;

end Flow_Error_Messages;
