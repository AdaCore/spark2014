--  This is problem 3 of the VSTTE 2012 Software Verification Competition.
--
--  https://sites.google.com/site/vstte2012/compet
--
--  The task is to implement a ring buffer that is stored in an array of fixed
--  size.
--
--  We differ from the specification in the problem in two points:
--    * We consider a buffer of fixed size (due to current restrictions in
--    Alfa)
--    * We do not consider initialization issues

package Ring_Buf is

   Buf_Size : constant := 10000;
   --  The problem description requires an array of variable size to be stored
   --  in the record. In Ada, this would require an access to an array. Access
   --  types are not in the Alfa subset, therefore we simplify slightly the
   --  specification and introduce a fixed size array.
   --  In Ada (and Alfa), this could also be achieved using generics, or
   --  discriminant records, but this is something we do not support yet.

   subtype Ar_Index is Integer range 0 .. Buf_Size - 1;
   subtype Length_Type is Integer range 0 .. Buf_Size;
   type Buf_Array is Array (Ar_Index) of Integer;
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

   --  The function Create (N), as required in the problem description, should
   --  return a buffer of size N. As we have fixed N, this function does not
   --  make much sense, and a user of this interface can simply declare a
   --  variable of type Ring_Buffer.
   --  function Create (N : Positive) return Ring_Buffer;

   procedure Clear (R : out Ring_Buffer)
      with Post => (Is_Empty (R));

   function Head (R : in Ring_Buffer) return Integer is (R.Data (R.First));
   --  This function only needs a precondition when we care about
   --  initialization.

   procedure Push (R : in out Ring_Buffer; X : Integer)
      with Pre => (not Is_Full (R)),
          Post => (R.Length = R.Length'Old + 1);

   procedure Pop (R : in out Ring_Buffer; Element : out Integer)
      with Pre => (not Is_Empty (R)),
           Post =>
             (R.Length = R.Length'Old - 1 and then Head (R'Old) = Element);

end Ring_Buf;

