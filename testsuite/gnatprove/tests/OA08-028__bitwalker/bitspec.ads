with BitTypes;   use BitTypes;
with Interfaces; use Interfaces;
with Bvext;      use Bvext;

package BitSpec with
SPARK_Mode
--  Ghost  commented out due to GNAT bug ? (OB32-022)
is
   function Nth8_Stream (Stream : Byte_Sequence; Pos : Natural) return Boolean is
     (Nth (Stream (Pos / 8), 7 - (Pos rem 8)))
   with Pre => Stream'First = 0 and then (Pos / 8 <= Stream'Last), Ghost;

   function MaxValue (Len : Natural) return Unsigned_64 is
     (Shift_Left (1, Len));

   type Unit is (Void);
end BitSpec;
