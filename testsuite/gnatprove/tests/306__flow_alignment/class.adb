procedure Class with SPARK_Mode is
   type T is tagged record
      C : Natural;
   end record;

   procedure Test (X : T'Class; Y : out Natural)
      with Depends => (Y => X)
   is
   begin
      Y := X'Alignment;  --  implicit dispatching call for 'Alignment
   end;

   X : T := (C => 0);
   Y : Natural;
begin
   Test (X, Y);
end;
