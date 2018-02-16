generic
   type T is range <>;
package P.UID
   with SPARK_Mode        => On,
        Abstract_State    => Pool,
        Initializes       => Pool
is

   function Is_Allocated (Id : T) return Boolean
   with Ghost,
        Global => Pool;

end P.UID;
