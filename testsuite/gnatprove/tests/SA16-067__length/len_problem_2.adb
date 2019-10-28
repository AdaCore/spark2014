procedure Len_Problem_2 with SPARK_Mode is
   capacity : constant := 255;
   type Unsigned_Long is mod 2**32;
   subtype string_length is Unsigned_Long range 0 .. capacity;

   procedure P (S : String) with Pre => S'Length < string_length'Last is
   begin
      null;
   end P;

   procedure User (S : String) with Pre => S'Length < capacity is
   begin
      P (S);
   end User;

begin
   User ("toto");
end Len_Problem_2;
