with Interfaces; use Interfaces;

package BitTypes with
  SPARK_Mode
is
   type Byte_Sequence is array (Natural range <>) of Unsigned_8;
end BitTypes;
