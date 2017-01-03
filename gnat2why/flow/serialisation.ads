------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         S E R I A L I S A T I O N                        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2015-2017, Altran UK Limited              --
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

private with Ada.Containers.Doubly_Linked_Lists;

with Ada.Containers;        use Ada.Containers;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

--  A package that deals with serialisation; this is used when reading and
--  writing the ALI file during global generation. However, like the graph
--  package, it is kept reasonably generic so that it might be easily used
--  elsewhere.
--
--  The idea is taken from the Boost serialisation library, in that we have a
--  *single* procedure for reading and writing, which keeps code size small and
--  maintainance obvious should data structures be extended or modified.
--
--  To use it you first need to write a simple Serialize procedure, for
--  example for a record containing three integer fields. Note that this
--  procedure can both read and write the record!
--
--     procedure Serialize (A : in out Archive; V : in out My_Record) is
--     begin
--        Serialize (A, V.Field1);
--        Serialize (A, V.Field2);
--        Serialize (A, V.Field3);
--     end Serialize;
--
--  Serialisation procedures can be instantiated for most primitive types
--  from this package, so to make the Serialize procedure for the integer type
--  Small_Range_T which we might have used in the above record we simply do:
--
--     procedure Serialize is new Serialize_Discrete (T => Small_Range_T);
--
--  Similar pre-made procedures are available for the Ada containers as
--  well (or really anything that exports the required functions related
--  to iteration).
--
--  Finally, an archive can be converted to/from an unbounded string, which
--  is how you are expected to ultimately read and write, so a tiny example
--  might be for writing:
--
--     declare
--        A : Archive (Output);
--     begin
--        Serialize (A, The_Record);
--        Write_To_File (To_String (A));
--     end;
--
--  Note that in the case of reading, the object passed to the serialisation
--  procedure must be fully initialized if it is a scalar, or if it is a
--  composite type any components containing scalars must be fully initialized
--  since the second argument is an "in out". The easiest way to achieve this
--  is to have a "null" constant for the type you ultimately want to serialize.
--  Thus to safely read:
--
--     declare
--        A          : Archive (Input) := From_String (Read_Line_From_File);
--        The_Record : Record_T        := Null_Record;
--     begin
--        Serialize (A, The_Record);
--        --  do stuff with the_record here...
--     end;

package Serialisation is

   Parse_Error : exception;
   --  This exception is raised when attempting to read back from an archive,
   --  and the given data does not match the expected format.

   type Direction is (Input, Output);
   --  Input is for reading, Output is for writing

   type Archive (Kind : Direction) is private;
   --  This is the main type defined by this package

   function To_String (A : Archive) return Unbounded_String
   with Pre => A.Kind = Output;
   --  Convert the archive to a string (possibly because we want to write it to
   --  a file).

   function From_String (S : String) return Archive
   with Post => From_String'Result.Kind = Input;
   --  Create an archive from a string (which we might have just read from a
   --  file).

   ----------------------------------------------------------------------
   --  Debug
   ----------------------------------------------------------------------

   procedure Debug_Dump_Archive (A : Archive);
   --  Dump a vaguely human-readable form of the given archive to standard
   --  output.

   ----------------------------------------------------------------------
   --  Pre-made serialisation procedures
   ----------------------------------------------------------------------

   procedure Serialize (A : in out Archive; V : in out Unbounded_String);
   --  Serialisation for an unbounded String. If you want to serialize a
   --  String, convert to/from an unbounded string and use this procedure; it
   --  produces a much more compact output than looping over each element of
   --  the string/array.

   generic
      type T is (<>);
   procedure Serialize_Discrete (A     : in out Archive;
                                 V     : in out T;
                                 Label : String := "");
   --  Serialisation for any discrete type (ultimately using 'Image and 'Value)
   --  of the given type T.

   generic
      type T is private;
      type E is private;
      type Cursor is private;
      Null_Container : T;
      Null_Element   : E;
      with function First (Container : T) return Cursor is <>;
      with function Next (Position : Cursor) return Cursor is <>;
      with function Element (Position : Cursor) return E is <>;
      with procedure Append (Container : in out T;
                             New_Item  : E;
                             Count     : Count_Type) is <>;
      with function Length (Container : T)
                            return Ada.Containers.Count_Type;
      with procedure Serialize (A : in out Archive; V : in out E) is <>;
   procedure Serialize_List (A : in out Archive;
                             V : in out T);
   --  Serialisation for a container that behaves like a list

   generic
      type T is private;
      type E is private;
      type Cursor is private;
      Null_Container : T;
      Null_Element   : E;
      with function First (Container : T) return Cursor is <>;
      with function Next (Position : Cursor) return Cursor is <>;
      with function Element (Position : Cursor) return E is <>;
      with procedure Insert (Container : in out T;
                             New_Item  : E) is <>;
      with function Length (Container : T)
                            return Ada.Containers.Count_Type;
      with procedure Reserve_Capacity (Container : in out T;
                                       Capacity  : Ada.Containers.Count_Type);
      with procedure Serialize (A : in out Archive; V : in out E) is <>;
   procedure Serialize_Set (A     : in out Archive;
                            V     : in out T;
                            Label : String := "");
   --  Serialisation for a container that behaves like a set. The only
   --  difference to the above is Insert (whose signature is different
   --  than Append) and Label (which makes the output more human-readable).

private
   package Token_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Unbounded_String);

   type Archive (Kind : Direction) is record
      Content : Token_Lists.List;
   end record;
   --  An archive is just a bunch of strings, and our file format is a
   --  space-separated collection of strings. So the above record with
   --  three integer fields might produce a serialisation similar to this:
   --
   --     "5 3 -3"

end Serialisation;
