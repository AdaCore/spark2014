package body P.UID
with Refined_State => (Pool => null),
     SPARK_Mode    => On
is

   function Is_Allocated (Id : T) return Boolean is (False);

end P.UID;
