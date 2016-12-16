package Tagged_Volatile
  with SPARK_Mode
is
   type T is tagged record
      C : Integer;
   end record
     with Volatile;
end Tagged_Volatile;
