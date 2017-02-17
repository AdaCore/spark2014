---------------------------------------------------------------------------
-- FILE    : hermes-der-decode.adb
-- SUBJECT : Body of a package for decoding DER encoded data.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package body Hermes.DER.Decode is

   procedure Split_Leading_Identifier
     (Value           : in  Octet;
      Tag_Class       : out Tag_Class_Type;
      Structured_Flag : out Structured_Flag_Type;
      Tag             : out Leading_Number_Type;
      Status          : out Status_Type) is

      subtype Leading_Number_Range_Type is Octet range 0 .. 31;
      Leading_Number_Lookup_Table :
        constant array(Leading_Number_Range_Type) of Leading_Number_Type :=
        ( 0 => Tag_Reserved,
          1 => Tag_Boolean,
          2 => Tag_Integer,
          3 => Tag_Bit_String,
          4 => Tag_Octet_String,
          5 => Tag_Null,
          6 => Tag_Object_Identifier,
          7 => Tag_Object_Descriptor,
          8 => Tag_Instance_Of,        -- Could also be Tag_External
          9 => Tag_Real,
         10 => Tag_Enumerated,
         11 => Tag_Embedded_PDV,
         12 => Tag_UTF8_String,
         13 => Tag_Relative_OID,
         14 => Tag_Null,               -- 14 is undefined.
         15 => Tag_Null,               -- 15 is undefined.
         16 => Tag_Sequence,           -- Could also be Tag_Sequence_Of
         17 => Tag_Set,                -- Could also be Tag_Set_Of
         18 => Tag_Numeric_String,
         19 => Tag_Printable_String,
         20 => Tag_Teletex_String,     -- Could also be Tag_T61_String
         21 => Tag_Videotex_String,
         22 => Tag_IA5_String,
         23 => Tag_UTC_Time,
         24 => Tag_Generalized_Time,
         25 => Tag_Graphic_String,
         26 => Tag_Visible_String,     -- Could also be Tag_ISO646_String
         27 => Tag_General_String,
         28 => Tag_Universal_String,
         29 => Tag_Character_String,
         30 => Tag_BMP_String,
         31 => Tag_EXTENDED_TAG);

      procedure Set_Tag_Class
        with
          Global => (Input => Value, Output => Tag_Class),
          Depends => (Tag_Class => Value)
      is
      begin
         -- Deal with the class.
         case (Value and 2#1100_0000#) is
            when 2#0000_0000# => Tag_Class := Class_Universal;
            when 2#0100_0000# => Tag_Class := Class_Application;
            when 2#1000_0000# => Tag_Class := Class_Context_Specific;
            when 2#1100_0000# => Tag_Class := Class_Private;
            when others => Tag_Class := Class_Universal;   -- Should never happen.
         end case;
      end Set_Tag_Class;

      procedure Set_Structured_Flag
        with
          Global => (Input => Value, Output => Structured_Flag),
          Depends => (Structured_Flag => Value)
      is
      begin
         -- Deal with the structured flag.
         case (Value and 2#0010_0000#) is
            when 2#0000_0000# => Structured_Flag := Primitive;
            when 2#0010_0000# => Structured_Flag := Constructed;
            when others => Structured_Flag := Primitive;   -- Should never happen.
         end case;
      end Set_Structured_Flag;

      procedure Set_Tag
        with
          Global => (Input => Value, Output => Tag, In_Out => Status),
          Depends => (Tag => Value, Status =>+ Value)
      is
         Tag_Value : Leading_Number_Range_Type;
      begin
         -- Deal with the tag.
         Tag_Value := (Value and 2#0001_1111#);
         if Tag_Value = 14 or Tag_Value = 15 then
            Status := Bad_Identifier;
         end if;
         Tag := Leading_Number_Lookup_Table(Tag_Value);
      end Set_Tag;

   begin
      Status := Success;

      Set_Tag_Class;
      Set_Structured_Flag;
      Set_Tag;
   end Split_Leading_Identifier;


   procedure Get_Length_Value
     (Message : in  Octet_Array;
      Start   : in  Natural;
      Stop    : out Natural;
      Length  : out Natural;
      Status  : out Status_Type) is

      subtype Length_Of_Length_Type is Positive range 1 .. 127;
      Length_Of_Length : Length_Of_Length_Type;

      function Convert_Length
        (Starting : in Natural; Octet_Count : in Length_Of_Length_Type) return Natural
        with
          Global => (Input => Message),
          Pre => (Message'First < Starting and
                  (Starting + (Octet_Count - 1)) <= Message'Last and Octet_Count <= 4) and then
                 (if Octet_Count = 4 then Message(Starting) < 128)
      is
         Result : Natural := 0;
      begin
         for I in Length_Of_Length_Type range 1 .. Octet_Count loop
            pragma Loop_Invariant
              (if Octet_Count < 4 then (Result < 256**(I - 1)));
            pragma Loop_Invariant
              (if Octet_Count = 4 then ((if I = 1 then Result < 1) and (if I > 1 then Result < 128*256**(I - 2))));

            Result := (Result * 256) + Natural(Message(Starting + (I - 1)));
         end loop;
         return Result;
      end Convert_Length;

   begin
      -- Check for indefinite length.
      if Message(Start) = 2#1000_0000# then
         Stop   := Start;
         Length := 0;
         Status := Indefinite_Length;

      -- Check for definite length, short form.
      elsif (Message(Start) and 2#1000_0000#) = 2#0000_0000# then
         Stop   := Start;
         Length := Natural(Message(Start));
         Status := Success;

      -- Check for definite length, long form, reserved value.
      elsif Message(Start) = 2#1111_1111# then
         Stop   := Start;
         Length := 0;
         Status := Bad_Length;

      -- We have definite length, long form, normal value.
      else
         pragma Assert(Message(Start) - 128 >= 1);
         pragma Assert(Message(Start) /= 0);
         Length_Of_Length := Length_Of_Length_Type(Message(Start) and 2#0111_1111#);

         -- Check that all length octets are in the array.
         if Start > Message'Last - Length_Of_Length then
            Stop   := Message'Last;  -- Desired value of Stop not specified.
            Length := 0;
            Status := Bad_Length;

         -- Check that the value of the length is not too large (here we assume 32 bit
         -- Naturals).
         --
         -- TODO: It is allowed to encode small lengths with a lot of leading zeros so
         -- Length_Of_Length > 4 might be ok. NO! The DER rules do not allow this (right?)
         --
         elsif Length_Of_Length > 4 or (Length_Of_Length = 4 and Message(Start + 1) >= 128) then
            Stop   := Start + Length_Of_Length;
            Length := 0;
            Status := Unimplemented_Length;

         -- Convert the length into a single Natural.
         else
            Stop   := Start + Length_Of_Length;
            Length := Convert_Length(Start + 1, Length_Of_Length);
            Status := Success;
         end if;
      end if;
   end Get_Length_Value;


   procedure Get_Boolean_Value
     (Message : in  Octet_Array;
      Start   : in  Natural;
      Stop    : out Natural;
      Value   : out Boolean;
      Status  : out Status_Type) is

      Tag_Class         : Tag_Class_Type;
      Structured_Flag   : Structured_Flag_Type;
      Tag               : Leading_Number_Type;
      Identifier_Status : Status_Type;

      -- This procedure is called after the identifier and length octets have been validated. It
      -- extracts the actual Boolean from the message. Length_Stop is the last octet of the
      -- length.
      --
      procedure Identifier_And_Length_Ok
        (Length      : in  Natural;
         Length_Stop : in  Natural)
        with
          Global => ( Input => Message, Output => (Stop, Value, Status) ),
          Depends => (Stop   => (Length_Stop, Length),
                      Status => (Message, Length_Stop),
                      Value  => (Length_Stop, Message) ),
          Pre => Length = 1 and Message'First < Length_Stop and Length_Stop < Message'Last
      is
      begin
         Stop   := Length_Stop + Length;
         Status := Success;

         if Message(Length_Stop + 1) = 2#1111_1111# then
            Value := True;
         elsif Message(Length_Stop + 1) = 2#0000_0000# then
            Value := False;
         else
            Value := False;
            Status := Bad_Value;
         end if;
      end Identifier_And_Length_Ok;


      -- This procedure is called after the identifier octets have been validated. It extracts
      -- the length from the message. Identifier_Stop is the last octet of the indentifier.
      --
      procedure Identifier_Ok(Identifier_Stop : in Natural)
        with
          Global => ( Input => Message, Output => (Stop, Value, Status) ),
          Depends => ( (Stop, Value, Status) => (Message, Identifier_Stop) ),
          Pre => Message'First <= Identifier_Stop and Identifier_Stop < Message'Last
      is
         Length_Stop   : Natural;
         Length        : Natural;
         Length_Status : Status_Type;
      begin
         Get_Length_Value(Message, Identifier_Stop + 1, Length_Stop, Length, Length_Status);
         if Length_Status /= Success then
            -- We couldn't decode the length.
            Stop   := Length_Stop;
            Value  := False;
            Status := Bad_Value;
         elsif Length_Stop > Message'Last - Length then
            -- The value goes off the end of the message.
            Stop   := Message'Last;
            Value  := False;
            Status := Bad_Value;
         elsif Length /= 1 then
            -- Boolen values must have a length of exactly one.
            Stop   := Length_Stop + Length;
            Value  := False;
            Status := Bad_Value;
         else
            -- Leading identifier is ok. Length is ok. Boolean value starts at Length_Stop + 1.
            Identifier_And_Length_Ok(Length, Length_Stop);
         end if;
      end Identifier_Ok;

   begin
      Split_Leading_Identifier
        (Message(Start), Tag_Class, Structured_Flag, Tag, Identifier_Status);
      if Identifier_Status /= Success         or
         Tag_Class         /= Class_Universal or
         Structured_Flag   /= Primitive       or
         Tag               /= Tag_Boolean     then

         Stop   := Start;
         Value  := False;
         Status := Bad_Value;
      else
         if Start > Message'Last - 1 then
            Stop   := Start;
            Value  := False;
            Status := Bad_Value;
         else
            Identifier_Ok(Start);
         end if;
      end if;
   end Get_Boolean_Value;


   procedure Get_Integer_Value
     (Message : in  Octet_Array;
      Start   : in  Natural;
      Stop    : out Natural;
      Value   : out Integer;
      Status  : out Status_Type) is

      Tag_Class         : Tag_Class_Type;
      Structured_Flag   : Structured_Flag_Type;
      Tag               : Leading_Number_Type;
      Identifier_Status : Status_Type;


      -- This procedure is called after the identifier and length octets have been validated. It
      -- extracts the actual integer from the message. Length_Stop is the last octet of the
      -- length.
      --
      procedure Identifier_And_Length_Ok
        (Length      : in  Natural;
         Length_Stop : in  Natural)
        with
          Global => ( Input => Message, Output => (Stop, Value, Status) ),
          Depends => (Stop   => (Length_Stop, Length),
                      Status => null,
                      Value  => (Length_Stop, Length, Message) ),
          Pre => Length <= 4 and Message'First < Length_Stop and Length_Stop <= Message'Last
      is
         Result : Integer := 0;
      begin
         Stop   := Length_Stop + Length;
         Status := Success;

         -- If the most significant bit is 0, then the value is positive.
         if (Message(Length_Stop + 1) and 16#80#) = 0 then
            for I in Natural range 1 .. Length loop
               Result := 256*Result + Integer(Message(Length_Stop + I));
            end loop;
            Value := Result;
         else
            -- For negative values, invert the bits.
            for I in Natural range 1 .. Length loop
               Result := 256*Result + Integer(Message(Length_Stop + I) xor 16#FF#);
            end loop;
            -- We have to handle Integer'Last as a special case due to the asymmetry of 2's
            -- complement representations.
            if Result = Integer'Last then
               Value := Integer'First;
            else
               Value := -(Result + 1);
            end if;
         end if;
      end Identifier_And_Length_Ok;


      -- This procedure is called after the identifier octets have been validated. It extracts
      -- the length from the message. Identifier_Stop is the last octet of the indentifier.
      --
      procedure Identifier_Ok(Identifier_Stop : in Natural)
        with
          Global => ( Input => Message, Output => (Stop, Value, Status) ),
          Depends => ( (Stop, Value, Status) => (Message, Identifier_Stop) ),
          Pre => Message'First <= Identifier_Stop and Identifier_Stop < Message'Last
      is
         Length_Stop   : Natural;
         Length        : Natural;
         Length_Status : Status_Type;
      begin
         Get_Length_Value(Message, Identifier_Stop + 1, Length_Stop, Length, Length_Status);
         if Length_Status /= Success then
            -- We couldn't decode the length.
            Stop   := Length_Stop;
            Value  := 0;
            Status := Bad_Value;
         elsif Length_Stop > Message'Last - Length then
            -- The value goes off the end of the message.
            Stop   := Message'Last;
            Value  := 0;
            Status := Bad_Value;
         elsif Length > 4 then
            -- The length implies too large a value.
            Stop   := Length_Stop + Length;
            Value  := 0;
            Status := Unimplemented_Value;
         elsif Length >= 2 and then (Message(Length_Stop + 1) = 16#00# and (Message(Length_Stop + 2) and 16#80#) = 16#00#) then
            -- The value has too many leading zeros. (Should this check be moved to
            -- Identifier_And_Length_Ok?
            --
            Stop   := Length_Stop + Length;
            Value  := 0;
            Status := Bad_Value;
         elsif Length >= 2 and then (Message(Length_Stop + 1) = 16#FF# and (Message(Length_Stop + 2)  or 16#7F#) = 16#FF#) then
            -- The value has too many leading ones. (Should this check be moved to
            -- Identifier_And_Length_Ok?
            --
            Stop   := Length_Stop + Length;
            Value  := 0;
            Status := Bad_Value;
         else
            -- Leading identifier is ok. Length is ok. Integer value starts at Length_Stop + 1.
            Identifier_And_Length_Ok(Length, Length_Stop);
         end if;
      end Identifier_Ok;

   begin
      Split_Leading_Identifier
        (Message(Start), Tag_Class, Structured_Flag, Tag, Identifier_Status);
      if Identifier_Status /= Success         or
         Tag_Class         /= Class_Universal or
         Structured_Flag   /= Primitive       or
         Tag               /= Tag_Integer     then

         Stop   := Start;
         Value  := 0;
         Status := Bad_Value;
      else
         if Start > Message'Last - 1 then
            Stop   := Start;
            Value  := 0;
            Status := Bad_Value;
         else
            Identifier_Ok(Start);
         end if;
      end if;
   end Get_Integer_Value;


end Hermes.DER.Decode;
