procedure Bar with
  SPARK_Mode
is

   function Model (L : Integer) return String with
     Pre => True
   is
      subtype S is String (1 .. L);
      X : constant S := (others => 'x');
   begin
      return X;
   end Model;

   procedure Find_And_Modify (L : Integer) is
   begin
      loop
         pragma Loop_Invariant (Model (L) (1 .. 3) = "xxx");
      end loop;
   end Find_And_Modify;
begin
   null;
end Bar;
