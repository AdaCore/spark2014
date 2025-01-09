pragma SPARK_Mode(On);
pragma Ada_2022;
with Interfaces.C; use Interfaces.C;
package Messages_Wrapper is
   function Compute_Fletcher_Checksum
     (Buffer : in Char_Array) return Unsigned_Short
     with
       Pre => Buffer'Length in Unsigned_Short;
   function Compute_Fletcher_Checksum
     (Buffer : in Char_Array) return Unsigned_Short is
      (Buffer'Length);
end Messages_Wrapper;
