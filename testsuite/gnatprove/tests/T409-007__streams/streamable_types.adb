with Ada.Strings.Fixed;

package body Streamable_Types with SPARK_Mode is
   use Streams;

   -- ---------
   --  Print --
   -- ---------

   procedure Print (Stream : not null access Root_Stream_Type'Class;
                    Item   : Int)
   is
      Value    : String := Strings.Fixed.Trim (Int'Image (Item), Strings.Left);
      Len      : String := Integer'Image (Value'Length);
      Complete : String := Len & 'i' & Value;
      Buffer   : Stream_Element_Array
         (Stream_Element_Offset (Complete'First) .. Stream_Element_Offset (Complete'Last));
   begin
      for I in Buffer'Range loop
         Buffer (I) := Stream_Element (Character'Pos (Complete (Integer (I))));
      end loop;

      Stream.Write (Buffer);
   end Print;

   -----------
   -- Parse --
   -----------

   procedure Parse (Stream : not null access Root_Stream_Type'Class;
                    Item   : out Int)
   is
      -- Variables needed to read from Stream.
      Buffer : Stream_Element_Array (1 .. 1);
      Last   : Stream_Element_Offset;

      -- Convenient constants
      Zero   : constant Stream_Element := Stream_Element (Character'Pos ('0'));
      Nine   : constant Stream_Element := Stream_Element (Character'Pos ('9'));
      Space  : constant Stream_Element := Stream_Element (Character'Pos (' '));

      procedure Skip_Spaces with Pre => True is
      begin
         loop
            Stream.Read (Buffer, Last);
            exit when Buffer (1) /= Space;
         end loop;
      end Skip_Spaces;

      procedure Read_Length (Len : out Integer) with Pre => True is
      begin
         if not (Buffer (1) in Zero .. Nine) then
            raise Parsing_Error;
         end if;

         Len := 0;
         loop
            Len := Len * 10 + Integer (Buffer (1) - Zero);
            Stream.Read (Buffer, Last);

            exit when not (Buffer (1) in Zero .. Nine);
         end loop;
      end Read_Length;

      procedure Read_Value (Item : out Int;
                            Len  : in  Integer) with Pre => True is
      begin
         Item := 0;
         for I in 1 .. Len loop
            Stream.Read (Buffer, Last);

            if not (Buffer (1) in Zero .. Nine) then
               raise Parsing_Error;
            end if;

            Item := 10 * Item + Int (Buffer (1) - Zero);
         end loop;
      end Read_Value;

      Len : Integer := 0;
   begin
      Skip_Spaces;

      Read_Length (Len);

      if Character'Val (Integer (Buffer (1))) /= 'i' then
         raise Parsing_Error;
      end if;

      Read_Value(Item, Len);
   end Parse;
end Streamable_Types;
