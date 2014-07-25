generic
   type T is range <>;
package G
  with SPARK_Mode => On
is
   procedure Op (A : in out T)
     with Pre => A < T'Last and
                 1 in T;

end G;
