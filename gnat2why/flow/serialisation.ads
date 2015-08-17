------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         S E R I A L I S A T I O N                        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                  Copyright (C) 2015, Altran UK Limited                   --
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
--  The idea is taken from the Boost serialisation library, in that we have
--  a *single* procedure for reading and writing, which keeps code size
--  small and maintainence obvious should datastructures be extended or
--  modified.
--
--  To use it you first need write a simple Serialize procedure, for
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
--  from this package, so to make the Serialize procedure for the integer
--  type Small_Range_T which we might have used in the above record we
--  simply do:
--
--     procedure Serialize is new Serialize_Discreete (T => Small_Range_T);
--
--  Similar pre-made procedures are available for the ada containers as
--  well (or really anything that exports the required functions related to
--  iteration).
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
--  And for reading:
--
--     declare
--        A : Archive (Input) := From_String (Read_Line_From_File);
--     begin
--        Serialize (A, The_Record);
--     end;

package Serialisation is

   Parse_Error : exception;
   --  This exception is raised when attempting to read back from an
   --  archive, and the given data does not match the format we're
   --  expecting.

   type Direction is (Input, Output);
   --  Input is for reading, Output is for writing.

   type Archive (Kind : Direction) is private;
   --  This is the main type defined by this package.

   function To_String (A : Archive) return Unbounded_String
   with Pre => A.Kind = Output;
   --  Convert the archive to a string (possibly because we want to write
   --  it to a file).

   function From_String (S : Unbounded_String) return Archive
   with Post => From_String'Result.Kind = Input;
   --  Create an archive from a string (which we might have just read from
   --  a file).

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
   --  String, convert to/from an unbounded string.
   --
   --  This is not as easy as one might expect, since we need to do some
   --  escaping so that any string does not interfere with the (very
   --  simple) format we expect an archive to have.

   generic
      type T is (<>);
   procedure Serialize_Discreete (A : in out Archive; V : in out T);
   --  Serialisation for any discreete type (ultimately using 'image and
   --  'value) of the given type T.

   generic
      type T is private;
      type E is private;
      type Cursor is private;
      Null_Container : T;
      Null_Element   : E;
      with function First (Container : T) return Cursor is <>;
      with function Next (Position : Cursor) return Cursor is <>;
      with function Has_Element (Position : Cursor) return Boolean is <>;
      with function Element (Position : Cursor) return E is <>;
      with procedure Append (Container : in out T;
                             New_Item  : E;
                             Count     : Count_Type) is <>;
      with procedure Serialize (A : in out Archive; V : in out E) is <>;
   procedure Serialize_List (A   : in out Archive;
                             V   : in out T;
                             Tag : String := "")
   with Pre => " " not in Tag;
   --  Serialisation for a container that behaves like a list.
   --
   --  If tag is specified the format will be "c:tag [ element ... ]". If
   --  the list is empty then nothing will be produced (effectively making
   --  this optional).
   --
   --  If tag is not specified the format will be "[ element ... ]", if the
   --  list is empty then we get "[ ]".

   generic
      type T is private;
      type E is private;
      type Cursor is private;
      Null_Container : T;
      Null_Element   : E;
      with function First (Container : T) return Cursor is <>;
      with function Next (Position : Cursor) return Cursor is <>;
      with function Has_Element (Position : Cursor) return Boolean is <>;
      with function Element (Position : Cursor) return E is <>;
      with procedure Insert (Container : in out T;
                             New_Item  : E) is <>;
      with procedure Serialize (A : in out Archive; V : in out E) is <>;
   procedure Serialize_Set (A   : in out Archive;
                            V   : in out T;
                            Tag : String := "")
   with Pre => " " not in Tag;
   --  Serialisation for a container that behaves like a set (the main
   --  difference to the above is that the add-to-container procedure).
   --
   --  The format is as with Serialize_List.

private

   package String_Lists is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Unbounded_String);

   type Archive (Kind : Direction) is record
      Content : String_Lists.List;
   end record;
   --  An archive is just a bunch of string, and our file format is a
   --  space-separated collection of strings. So the above record with
   --  three integer fields might produce a serialisation similar to this:
   --
   --     "5 3 -3"

end Serialisation;
