------------------------------------------------------------------------------
--                                                                          --
--                           SPARKSMT COMPONENTS                            --
--                                                                          --
--                                L E X E R                                 --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2016, Altran UK Limited                      --
--                                                                          --
-- sparksmt is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  sparksmt is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  sparksmt;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Characters.Latin_1; use Ada.Characters.Latin_1;

with File_IO;                use File_IO;
with Con_IO;                 use Con_IO;
with Unbounded_Strings;      use Unbounded_Strings;

package body Lexer with
   SPARK_Mode,
   Refined_State => (State => (The_Filename,
                               The_File,
                               Current_Read,
                               Current_Line,
                               Current_Col,
                               Current_Idx,
                               Next_Read,
                               Next_Idx))
is

   The_Filename : Name_Id;
   The_File     : File;

   Current_Read : Read_Result;
   Current_Line : Positive;
   Current_Col  : Natural;
   Current_Idx  : Natural;

   Next_Read    : Read_Result;
   Next_Idx     : Natural;

   ---------------------
   -- Local_Invariant --
   ---------------------

   function Local_Invariant return Boolean is
      (not Current_Read'Constrained and
       not Next_Read'Constrained and
       Current_Idx <= Size (The_File) and
       Next_Idx <= Size (The_File) and
       Next_Idx = Index (The_File) and
       Current_Idx <= Next_Idx and
       (if Next_Read.Status = Success
        then Current_Read.Status = Success and
             Current_Idx = Next_Idx - 1
        else Current_Idx = Next_Idx));

   ---------------------
   -- Adjust_Position --
   ---------------------

   procedure Adjust_Position
   with Global => (Input => Current_Read,
                   In_Out => (Current_Line,
                              Current_Col))
   is
      --  Files that large seem unlikely...
      pragma Assume (Current_Line < Positive'Last);
      pragma Assume (Current_Col  < Natural'Last);
   begin
      if Current_Read.Status = Success then
         case Current_Read.C is
            when LF =>
               Current_Line := Current_Line + 1;
               Current_Col  := 0;
            when CR =>
               null;
            when others =>
               Current_Col := Current_Col + 1;
         end case;
      end if;
   end Adjust_Position;

   ---------------
   -- Open_File --
   ---------------

   procedure Open_File (Filename : String)
   with Refined_Global => (In_Out => Names.Name_Table,
                           Output => (The_Filename,
                                      The_File,
                                      Current_Read,
                                      Current_Line,
                                      Current_Col,
                                      Current_Idx,
                                      Next_Read,
                                      Next_Idx))
   is
      --  Package invariant
      pragma Assume (not Current_Read'Constrained and
                     not Next_Read'Constrained);
   begin
      Lookup (Filename, The_Filename);
      Open_Read (Filename, The_File);
      Current_Line := 1;
      Current_Col  := 0;

      Read (The_File, Current_Read);
      Current_Idx  := Index (The_File);
      Adjust_Position;

      if Current_Read.Status = Success then
         Read (The_File, Next_Read);
         Next_Idx  := Index (The_File);
      else
         Next_Read := Current_Read;
         Next_Idx  := Current_Idx;
      end if;
   end Open_File;

   ----------------
   -- Read_Token --
   ----------------

   procedure Read_Token (T : out Token)
   with Refined_Global => (Input => The_Filename,
                           In_Out => (Name_Table,
                                      The_File,
                                      Current_Read,
                                      Current_Line,
                                      Current_Col,
                                      Current_Idx,
                                      Next_Read,
                                      Next_Idx))
   is

      type Error_Message_Location is (Initial, Current);

      S          : Unbounded_String;
      First_Line : Natural;
      First_Col  : Natural;
      First_Idx  : Natural;

      procedure Advance
      with Global => (In_Out => (The_File,
                                 Next_Read,
                                 Next_Idx,
                                 Current_Line,
                                 Current_Col,
                                 Current_Read,
                                 Current_Idx)),
           Pre => Local_Invariant,
           Post => Local_Invariant and
                   Current_Read = Next_Read'Old and
                   Current_Idx  = Next_Idx'Old and
                   Current_Idx >= Current_Idx'Old;
      --  Advance the input stream by 1 character (and maintain position
      --  information in current_line and current_col).

      procedure Skip_WS
      with Pre => Local_Invariant,
           Post => Local_Invariant and
                   Current_Idx >= Current_Idx'Old;
      --  Skip all whitespace and comments and position current_read on the
      --  next useful character.

      procedure Munch
      with Pre => Local_Invariant and
                  Current_Read.Status = Success,
           Post => Local_Invariant and
                   Length (S) = Length (S)'Old + 1 and
                   (if Current_Read.Status = Success
                    then Current_Idx = Current_Idx'Old + 1
                    else Current_Idx = Current_Idx'Old);
      --  Eat the current character, appending it to S. Then advance.

      pragma Warnings (Off, "subprogram ""Error"" has no effect");
      procedure Error (Location : Error_Message_Location;
                       Msg      : String)
      with Pre => Names.Invariant;
      --  Emit an error message at the current lex position.

      -------------
      -- Advance --
      -------------

      procedure Advance is
      begin
         Current_Read := Next_Read;
         Current_Idx  := Next_Idx;
         Adjust_Position;

         if Current_Read.Status = Success then
            Read (The_File, Next_Read);
            Next_Idx := Index (The_File);
         end if;
      end Advance;

      -------------
      -- Skip_WS --
      -------------

      procedure Skip_WS is

         procedure Skip_Whitespace with
            Pre => Local_Invariant,
            Post => Local_Invariant and
                    Current_Idx >= Current_Idx'Old
         is
         begin
            while Current_Read.Status = Success and then
              Current_Read.C in LF | CR | Space | HT
            loop
               pragma Loop_Invariant (Local_Invariant and
                                      Current_Idx >= Current_Idx'Loop_Entry);
               pragma Loop_Variant
                 (Increases => Next_Idx,
                  Decreases => Next_Read.Status = Success);
               Advance;
            end loop;
         end Skip_Whitespace;

         procedure Skip_Comment with
            Pre => Local_Invariant and
                   (Current_Read.Status = Success and then
                    Current_Read.C = ';'),
            Post => Local_Invariant and
                    (if Current_Read.Status = Success
                     then Current_Idx > Current_Idx'Old
                     else Current_Idx >= Current_Idx'Old)
         is
         begin
            Advance;
            while Current_Read.Status = Success and then
              Current_Read.C /= LF
            loop
               pragma Loop_Invariant (Local_Invariant and
                                      Current_Idx >= Current_Idx'Loop_Entry);
               pragma Loop_Variant
                 (Increases => Next_Idx,
                  Decreases => Next_Read.Status = Success);
               Advance;
            end loop;
         end Skip_Comment;

      begin
         loop
            --  First we skip any white space
            Skip_Whitespace;
            exit when Current_Read.Status /= Success;

            --  Then we check for a comment and skip that too
            exit when Current_Read.C /= ';';
            Skip_Comment;

            --  We need this to show the loop variant (since we know that
            --  we must have skipped at least one character at this point).
            exit when Current_Read.Status /= Success;

            pragma Loop_Invariant (Local_Invariant and
                                   Current_Idx > Current_Idx'Loop_Entry);
            pragma Loop_Variant (Increases => Current_Idx);
         end loop;
      end Skip_WS;

      -----------
      -- Munch --
      -----------

      procedure Munch is
      begin
         Append (S, Current_Read.C);
         Advance;
      end Munch;

      -----------
      -- Error --
      -----------

      procedure Error (Location : Error_Message_Location;
                       Msg      : String)
      is
         L : Natural;
         C : Natural;
      begin
         if Location = Initial then
            L := First_Line;
            C := First_Col;
         else
            L := Current_Line;
            C := Current_Col;
         end if;

         Put (To_String (The_Filename));
         Put (":");
         Put (L);
         Put (":");
         Put (C);
         Put (": ");
         Put (Msg);
         New_Line;
      end Error;

      ---------------
      -- New_Token --
      ---------------

      procedure New_Token (Kind : Token_Kind)
      with Global => (Input => (First_Line,
                                First_Col),
                      Output => T),
           Pre => not T'Constrained and
                  Kind in T_Open_Bracket | T_Close_Bracket,
           Post => T.Kind = Kind and
                   T.Line = First_Line and
                   T.Col = First_Col and
                   T.Length = 1
      is
      begin
         case Kind is
            when T_Open_Bracket =>
               T := (Kind   => T_Open_Bracket,
                     Line   => First_Line,
                     Col    => First_Col,
                     Length => 1);

            when T_Close_Bracket =>
               T := (Kind   => T_Close_Bracket,
                     Line   => First_Line,
                     Col    => First_Col,
                     Length => 1);

            when others =>
               raise Program_Error;
         end case;
      end New_Token;

      procedure New_Token (Kind  : Valued_Tokens;
                           Value : String)
      with Global => (Input => (First_Line,
                                First_Col,
                                First_Idx,
                                Current_Idx),
                      In_Out => Name_Table,
                      Output => T),
           Pre => not T'Constrained and
                  Names.Invariant and
                  Current_Idx >= First_Idx,
           Post => Names.Invariant and
                   T.Kind = Kind and
                   T.Line = First_Line and
                   T.Col = First_Col and
                   T.Length = Current_Idx - First_Idx
      is
         T_Length : constant Natural := Current_Idx - First_Idx;
         N        : Name_Id;
      begin
         Lookup (Value, N);
         case Kind is
            when T_Symbol =>
               T := (Kind   => T_Symbol,
                     Line   => First_Line,
                     Col    => First_Col,
                     Length => T_Length,
                     Value  => N);
            when T_Numeral =>
               T := (Kind   => T_Numeral,
                     Line   => First_Line,
                     Col    => First_Col,
                     Length => T_Length,
                     Value  => N);
            when T_Decimal =>
               T := (Kind   => T_Decimal,
                     Line   => First_Line,
                     Col    => First_Col,
                     Length => T_Length,
                     Value  => N);
            when T_Binary =>
               T := (Kind   => T_Binary,
                     Line   => First_Line,
                     Col    => First_Col,
                     Length => T_Length,
                     Value  => N);
            when T_Hexadecimal =>
               T := (Kind   => T_Hexadecimal,
                     Line   => First_Line,
                     Col    => First_Col,
                     Length => T_Length,
                     Value  => N);
            when T_String =>
               T := (Kind   => T_String,
                     Line   => First_Line,
                     Col    => First_Col,
                     Length => T_Length,
                     Value  => N);
         end case;
      end New_Token;

      --  Local state

      type Parse_State is (Symbol,
                           Quoted_Symbol, Quoted_Symbol_OK,
                           Numeral_Or_Decimal,
                           Decimal,
                           Binary_Or_Hex,
                           Binary,
                           Hex,
                           String_Literal, String_Literal_OK);

      subtype Terminal_States is Parse_State with
        Static_Predicate => Terminal_States in
          Quoted_Symbol_OK | String_Literal_OK;

      State      : Parse_State;

      C          : Character;

      subtype Digit is Character range '0' .. '9';

      subtype Hex_Digit is Character
        with Static_Predicate => Hex_Digit in Digit | 'a' .. 'f' | 'A' .. 'F';

      subtype Letter is Character
        with Static_Predicate => Letter in 'a' .. 'z' | 'A' .. 'Z';

      subtype Symbol_Extra_Chars is Character
        with Static_Predicate => Symbol_Extra_Chars in
               '~' | '!' | '@' | '$' | '%' | '^' | '&' |
               '*' | '_' | '-' | '+' | '=' | '<' | '>' |
               '.' | '?' | '/';

   begin
      --  Check the first character, until we find a token, or the
      --  beginning of a multi-character token. Report any unexpected
      --  characters at this point too.
      loop
         --  This may or may not consume input, so in terms of termination
         --  proof it's neutral.
         Skip_WS;

         if Current_Read.Status in EOF | Error then
            pragma Assume (Current_Col < Natural'Last);
            T := (Kind   => T_EOF,
                  Line   => Current_Line,
                  Col    => Current_Col + 1,
                  Length => 0);
            return;
         end if;

         pragma Loop_Invariant (Local_Invariant and
                                Current_Read.Status = Success);
         pragma Loop_Variant (Increases => Current_Idx); -- @LOOP_VARIANT:FAIL

         First_Line := Current_Line;
         First_Col  := Current_Col;
         First_Idx  := Current_Idx;
         C          := Current_Read.C;
         New_String (S);
         Munch;

         case C is
            when '(' =>
               New_Token (T_Open_Bracket);
               return;

            when ')' =>
               New_Token (T_Close_Bracket);
               return;

            when '|' =>
               State := Quoted_Symbol;
               exit;

            when '#' =>
               State := Binary_Or_Hex;
               exit;

            when Digit =>
               State := Numeral_Or_Decimal;
               exit;

            when Letter | Symbol_Extra_Chars =>
               State := Symbol;
               exit;

            when '"' =>
               State := String_Literal;
               exit;

            when others =>
               Error (Initial, "invalid character '" & C & "'");
         end case;
      end loop;

      --  Continue to end of multi-character token.
      while Current_Read.Status = Success loop
         C := Current_Read.C;

         pragma Loop_Invariant
           (--  Need to keep track of our exit condition (precondition to
            --  munch) as this is the most convenient place for the
            --  invariant.
            Current_Read.Status = Success and

            --  If we ever enter a terminal state we'll exit the loop
            State not in Terminal_States and

            --  We need to remember what we have established in the first
            --  loop...
            Length (S) >= 1 and
            Current_Idx >= First_Idx and
            Local_Invariant and

            --  Specific proof obligation for safely chopping off '#b' or
            --  '#x' from binary and hex literals.
            (if State in Binary | Hex then Length (S) >= 2));
         pragma Loop_Variant (Increases => Current_Idx);

         --  Check if the current character is OK to swallow.
         case State is
            when Numeral_Or_Decimal =>
               case C is
                  when Digit  => null;
                  when '.'    => State := Decimal;
                  when others => exit;
               end case;

            when Decimal =>
               case C is
                  when Digit  => null;
                  when others => exit;
               end case;

            when Binary_Or_Hex =>
               --  Just assume *something* if we don't have a known
               --  character.
               case C is
                  when 'b'    => State := Binary;
                  when 'x'    => State := Hex;
                  when others => State := Hex;
                     Error (Current, "invalid format, must be 'b' or 'x'");
               end case;

            when Binary =>
               case C is
                  when '0'.. '1' => null;
                  when others    => exit;
               end case;

            when Hex =>
               case C is
                  when Hex_Digit => null;
                  when others    => exit;
               end case;

            when Symbol =>
               case C is
                  when Letter | Digit | Symbol_Extra_Chars => null;
                  when others                              => exit;
               end case;

            when Quoted_Symbol =>
               case C is
                  when '|' =>
                     Munch;
                     State := Quoted_Symbol_OK;
                     exit;

                  when others =>
                     null;
               end case;

            when String_Literal =>
               case C is
                  when '"' =>
                     if Next_Read.Status = Success and then
                       Next_Read.C = '"'
                     then
                        Advance;
                     else
                        Munch;
                        State := String_Literal_OK;
                        exit;
                     end if;

                  when others =>
                     null;
               end case;

            when Quoted_Symbol_Ok | String_Literal_OK =>
               raise Program_Error;
         end case;

         --  Current character is OK to swallow.
         Munch;
      end loop;

      pragma Assert (if State in Quoted_Symbol_OK | Hex | Binary
                     then Length (S) >= 2);

      --  Yield parsed token.
      declare
         Tmp : constant String := To_String (S);

         --  K and Str should be constant but see P420-001
         K   : Valued_Tokens :=
           (case State is
            when Symbol             |
                 Quoted_Symbol      |
                 Quoted_Symbol_OK   => T_Symbol,
            when Numeral_Or_Decimal => T_Numeral,
            when Decimal            => T_Decimal,
            when Binary_Or_Hex      |
                 Hex                => T_Hexadecimal,
            when Binary             => T_Binary,
            when String_Literal     |
                 String_Literal_OK  => T_String);

         Str : String :=
           (case State is
            when Symbol             |
                 Numeral_Or_Decimal |
                 Decimal            => Tmp,
            when Quoted_Symbol      |
                 String_Literal     => Tmp (Tmp'First + 1 .. Tmp'Last),
            when Quoted_Symbol_OK   |
                 String_Literal_OK  => Tmp (Tmp'First + 1 .. Tmp'Last - 1),
            when Binary_Or_Hex      => "",
            when Binary | Hex       => Tmp (Tmp'First + 2 .. Tmp'Last));
      begin
         New_Token (K, Str);
      end;

      case State is
         when Quoted_Symbol =>
            Error (Initial, "quoted symbol is not terminated");
         when Binary_Or_Hex =>
            Error (Initial, "binary or hex symbol is not finished");
         when String_Literal =>
            Error (Initial, "string literal is not terminated");
         when others =>
            null;
      end case;
   end Read_Token;

   -------------
   -- Message --
   -------------

   procedure Message (T   : Token;
                      Msg : String)
   with Refined_Global => (Input => (Name_Table,
                                     The_Filename))
   is
   begin
      Put (To_String (The_Filename));
      Put (":");
      Put (T.Line);
      Put (":");
      Put (T.Col);
      Put (": ");
      Put (Msg);
      New_Line;
   end Message;

end Lexer;
