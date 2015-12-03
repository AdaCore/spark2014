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

   Buf_Size : constant := 2 ** 16;
   --  The problem description requires an array of variable size to be stored
   --  in the record. In Ada, this would require an access to an array. Access
   --  types are not in the SPARK subset, therefore we simplify slightly the
   --  specification and introduce a fixed size array.

   type Ar_Index is mod Buf_Size;
   type Length_Type is new Integer range 0 .. Buf_Size;

   type Model is array (Ar_Index range <>) of Integer;
   subtype Buf_Array is Model (Ar_Index);

   type Ring_Buffer is record
      Data   : Buf_Array;
      First  : Ar_Index;
      Length : Length_Type;
   end record;
   --  The record representing the buffer. The data itself is stored in the
   --  array Data, First is the first cell containing valid data. Length is
   --  the number of stored items starting from First, wrapping around the
   --  array borders is possible when First + Length > Buf_Size.

   function To_Model (R : Ring_Buffer) return Model
is
     (if Length_Type (R.First) + R.Length - 1 > Length_Type (R.Data'Last) then
         R.Data (R.First .. R.Data'Last) &
        R.Data (R.Data'First ..
                    R.Data'First + Ar_Index (R.Length) -
                 (R.Data'Last - R.First) - 1)
      else R.Data (R.First .. R.First + Ar_Index (R.Length) - 1));

   function Func_Head (M : Model) return Integer is (M (M'First))
   with Pre => M'Length > 0;

   function Func_Push (M : Model; X : Integer) return Model is (M & X);
   function Func_Pop (M : Model) return Model is (M (M'First .. M'Last - 1))
     with Pre => M'Length > 0;

   function Is_Full (R : Ring_Buffer) return Boolean is (R.Length = Buf_Size);

   function Is_Empty (R : Ring_Buffer) return Boolean is (R.Length = 0);

   procedure Clear (R : out Ring_Buffer)
     with Post => (To_Model (R) = Model'(1 .. 0 => 0));

   function Head (R : in Ring_Buffer) return Integer is (R.Data (R.First))
   with Pre => (not Is_Empty (R)),
        Post => Head'Result = Func_Head (To_Model (R));

   procedure Push (R : in out Ring_Buffer; X : Integer)
     with Pre  => (not Is_Full (R)),
          Post => To_Model (R) = Func_Push (To_Model(R)'Old, X);

   procedure Pop (R : in out Ring_Buffer; Element : out Integer)
     with Pre  => (not Is_Empty (R)),
          Post => To_Model (R) = Func_Pop (To_Model (R)'Old) and
             Element = Func_Head (To_Model (R)'Old);

end Ring_Buf;
