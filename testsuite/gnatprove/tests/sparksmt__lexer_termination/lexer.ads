------------------------------------------------------------------------------
--                                                                          --
--                           SPARKSMT COMPONENTS                            --
--                                                                          --
--                                L E X E R                                 --
--                                                                          --
--                                 S p e c                                  --
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

with Names; use Names;

--  A lexical analyzer for SMTLIB (v2.5 with some extensions).

package Lexer with
   SPARK_Mode,
   Abstract_State => State
is

   type Token_Kind is (T_EOF,
                       T_Open_Bracket,
                       T_Close_Bracket,

                       --  Start of Valued_Tokens
                       T_Symbol,
                       T_Numeral,         --   0,   1, ...
                       T_Decimal,         -- 0.0, 1.1, ...
                       T_Binary,          -- #b0110
                       T_Hexadecimal,     -- #xcoffee
                       T_String);         -- "derp", with "" for quote


   subtype Valued_Tokens is Token_Kind range T_Symbol .. Token_Kind'Last;

   type Token (Kind : Token_Kind := T_EOF) is record
      Line   : Natural;
      Col    : Natural;
      Length : Natural;
      case Kind is
         when Valued_Tokens =>
            Value : Name_Id;
         when others =>
            null;
      end case;
   end record;

   function Local_Invariant return Boolean
   with Ghost,
        Global => (Input => State);
   --  Internal invariant we maintain specific to the lexer.

   function Invariant return Boolean is
      (Names.Invariant and Local_Invariant)
   with Ghost,
        Global => (Input => (State, Name_Table));
   --  The combined invariant we care about and maintain, as seen by the
   --  lexer.

   procedure Open_File (Filename : String)
   with Global => (Output => State,
                   In_Out => Name_Table),
        Pre => Names.Invariant,
        Post => Invariant;
   --  Set current input to the given file.

   procedure Read_Token (T : out Token)
   with Global => (In_Out => (Name_Table, State)),
        Pre    => Invariant and
                  not T'Constrained,
        Post   => Invariant;
   --  Read the next SMTLIB token from the current file.

   procedure Message (T   : Token;
                      Msg : String)
   with Global => (Input => (Name_Table, State)),
        Pre    => Names.Invariant;
   --  Produce an error message anchored at the given token.

end Lexer;
