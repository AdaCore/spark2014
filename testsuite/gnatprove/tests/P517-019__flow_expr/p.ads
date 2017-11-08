package P with SPARK_Mode is
   X : Integer := 0;
private
   pragma SPARK_Mode (Off);
   type T is record
      C : Integer := X;
   end record;
end;
