package Types
  with SPARK_Mode
is
   subtype Index is Positive range 1 .. 10;
   type Text is array (Index range <>) of Integer;
end Types;
