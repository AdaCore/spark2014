procedure Class with SPARK_Mode is
   type T is tagged record
      C : Natural;
   end record;

   procedure Test (X : T'Class; Y : out Natural) with Pre => True is
   begin
      Y := X'Size;
      Y := X'Alignment;
      Y := T'Class'Size;
      Y := T'Class'Value_Size;
      Y := T'Class'Object_Size;
      Y := T'Class'Alignment;
   end;

   X : T := (C => 0);
   Y : Natural;
begin
   Test (X, Y);
end;
