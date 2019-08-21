package Ordering_Buffers with SPARK_Mode is

   type Sequence_Number_Type is range 1 .. 99_999_999;

   Ordering_Buffer_Length : constant := 16;

   subtype Extended_Sequence_Number_Type is Sequence_Number_Type'Base
     range Sequence_Number_Type'First .. Sequence_Number_Type'Last + Ordering_Buffer_Length;
   subtype Slightly_Extended_Sequence_Number_Type is Extended_Sequence_Number_Type
     range Sequence_Number_Type'First .. Sequence_Number_Type'Last + 1;

   type Message_Pointer is new Integer;
   Null_Message : constant Message_Pointer := 0;

   type Ordering_Buffer_Type is private with Default_Initial_Condition =>
     First (Ordering_Buffer_Type) = Sequence_Number_Type'First and
       (for all Index in First (Ordering_Buffer_Type) .. Last (Ordering_Buffer_Type)
         => not Has_Message (Ordering_Buffer_Type, Index));

   function Is_Null (Message : Message_Pointer) return Boolean is (Message = Null_Message);

   function First (Buffer : Ordering_Buffer_Type) return Slightly_Extended_Sequence_Number_Type;

   function Last (Buffer : Ordering_Buffer_Type) return Extended_Sequence_Number_Type
     is (First (Buffer) + Ordering_Buffer_Length - 1);

   function Get_Message (
     Buffer : Ordering_Buffer_Type;
     Index  : Extended_Sequence_Number_Type
   ) return Message_Pointer with Pre => First (Buffer) <= Index and Index <= Last (Buffer);

   function Has_Message (
     Buffer : Ordering_Buffer_Type;
     Index  : Extended_Sequence_Number_Type
   ) return Boolean is (not Is_Null (Get_Message (Buffer, Index))) with
     Pre => First (Buffer) <= Index and Index <= Last (Buffer);

   procedure Set_Message (
     Buffer  : in out Ordering_Buffer_Type;
     Index   : in     Sequence_Number_Type;
     Message : in     Message_Pointer -- Might be null
   ) with Pre => (First (Buffer) <= Index and Index <= Last (Buffer)) and then
       not Has_Message (Buffer, Index),
     Post => First (Buffer) = First (Buffer'Old) and
       Get_Message (Buffer, Index) = Message and
         (for all I in First (Buffer) .. Last (Buffer) =>
           (if I /= Index then Get_Message (Buffer, I) = Get_Message (Buffer'Old, I)));

   procedure Consume_First (
     Buffer  : in out Ordering_Buffer_Type;
     Message :    out Message_Pointer
   ) with Pre => First (Buffer) in Sequence_Number_Type
       and then Has_Message (Buffer, First (Buffer)),
     Post => First (Buffer) = First (Buffer'Old) + 1 and
       Message = Get_Message (Buffer'Old, First (Buffer'Old)) and
         not Is_Null (Message) and
           (for all Index in First (Buffer) .. Last (Buffer'Old) =>
             Get_Message (Buffer, Index) = Get_Message (Buffer'Old, Index));

   procedure Advance_First (Buffer : in out Ordering_Buffer_Type) with
     Pre => First (Buffer) in Sequence_Number_Type and then
       not Has_Message (Buffer, First (Buffer)),
     Post => First (Buffer) = First (Buffer'Old) + 1 and
       (for all Index in First (Buffer) .. Last (Buffer) - 1 =>
         Get_Message (Buffer, Index) = Get_Message (Buffer'Old, Index)) and
       not Has_Message (Buffer, Last (Buffer));

private
   type Ring_Index_Type is mod Ordering_Buffer_Length;

   type Ring_Buffer_Type is array (Ring_Index_Type) of Message_Pointer;

   type Ordering_Buffer_Type is record
      Ring  : Ring_Buffer_Type := (Ring_Index_Type => Null_Message);
      First : Slightly_Extended_Sequence_Number_Type := Sequence_Number_Type'First;
   end record;

   function First (Buffer : Ordering_Buffer_Type) return Slightly_Extended_Sequence_Number_Type is (Buffer.First);

   function Get_Message (
     Buffer : Ordering_Buffer_Type;
     Index  : Extended_Sequence_Number_Type
   ) return Message_Pointer is (Buffer.Ring (Ring_Index_Type'Mod (Index)));
end Ordering_Buffers;
