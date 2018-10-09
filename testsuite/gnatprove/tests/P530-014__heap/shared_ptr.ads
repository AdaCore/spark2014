package Shared_Ptr with
  SPARK_Mode
is
   type T is private;

   function Length (This : T) return Integer with Global => null;

   function To_String (This : T) return String with
     Pre => Length (This) > 0,
     Global => null;

   function Test (This : T) return Boolean is
      (Length (This) = To_String (This)'Length);

private
   pragma SPARK_Mode (Off);

   type T is access String;

   function Length (This : T) return Integer is (This.all'Length);

   function To_String (This : T) return String is (This.all);

end Shared_Ptr;
