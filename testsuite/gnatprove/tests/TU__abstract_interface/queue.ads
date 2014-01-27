package Queue
  with SPARK_Mode => On
is
   type T is limited interface;

   procedure Append(Q : in out T; X : in Integer) is abstract;

   procedure Remove_First(Q : in out T;
                          X : out Integer) is abstract;

   function Cur_Count(Q : in T) return Natural is abstract;

   function Max_Count(Q : in T) return Natural is abstract;
end Queue;
