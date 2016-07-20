package Ring_Buf
  with SPARK_Mode
is

   -------------------------------------------------------------------
   --                SPARK 2014 - Ring Buffer Example               --
   --                                                               --
   --  This is problem 3 of the VSTTE 2012 Competition.             --
   --                                                               --
   --  https://sites.google.com/site/vstte2012/compet               --
   --                                                               --
   --  The task is to implement a ring buffer that is stored in an  --
   --  array of fixed size.                                         --
   -------------------------------------------------------------------

   Buf_Size : constant := 10000;
   --  The problem description requires an array of variable size to be stored
   --  in the record. In Ada, this would require an access to an array. Access
   --  types are not in the SPARK subset, therefore we simplify slightly the
   --  specification and introduce a fixed size array.

   subtype Ar_Index is Integer range 0 .. Buf_Size - 1;
   subtype Length_Type is Integer range 0 .. Buf_Size;
   type Buf_Array is array (Ar_Index) of Integer;
   type Ring_Buffer is record
      Data   : Buf_Array;
      First  : Ar_Index;
      Length : Length_Type;
   end record;
   --  The record representing the buffer. The data itself is stored in the
   --  array Data, First is the first cell containing valid data. Length is
   --  the number of stored items starting from First, wrapping around the
   --  array borders is possible when First + Length > Buf_Size.

   function Is_Full (R : Ring_Buffer) return Boolean is (R.Length = Buf_Size);

   function Is_Empty (R : Ring_Buffer) return Boolean is (R.Length = 0);

   procedure Clear (R : out Ring_Buffer)
     with Post => (Is_Empty (R));

   function Head (R : in Ring_Buffer) return Integer is (R.Data (R.First))
     with Pre => (not Is_Empty (R));

   procedure Push (R : in out Ring_Buffer; X : Integer)
     with Pre  => (not Is_Full (R)),
          Post => (R.Length = R.Length'Old + 1);

   procedure Pop (R : in out Ring_Buffer; Element : out Integer)
     with Pre  => (not Is_Empty (R)),
          Post =>
             (R.Length = R.Length'Old - 1 and then Head (R'Old) = Element);

end Ring_Buf;
