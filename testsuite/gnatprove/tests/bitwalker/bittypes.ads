with Interfaces; use Interfaces;

package BitTypes with
  SPARK_Mode
is
--  My_Index does not range over all naturals to be able to pass the range
--  check associated to 'length of element of type Byte_Sequence. Indeed if an
--  array has as many elements as there are naturals, its length is not
--  in the natural's range.
   subtype My_Index is Natural range 0 .. Natural'Last - 1;
   type Byte_Sequence is array (My_Index range <>) of Unsigned_8;
end BitTypes;
