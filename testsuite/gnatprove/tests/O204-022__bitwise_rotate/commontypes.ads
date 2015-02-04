with Interfaces;

package CommonTypes with
  SPARK_Mode
is
   subtype LongWord_T is Interfaces.Unsigned_64;
   NULLLongWord : constant LongWord_T := 0;
end CommonTypes;
