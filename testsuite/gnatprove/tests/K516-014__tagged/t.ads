package T is pragma SPARK_Mode (Off);
   type T1 is tagged record
      X : Integer;
   end record;
   function Get return T1;
end;
