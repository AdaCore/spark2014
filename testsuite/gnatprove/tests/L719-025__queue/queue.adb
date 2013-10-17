package body Queue is pragma SPARK_Mode (On);

   function Tail (Q : List) return List is
      R : List := Copy (Q);
   begin
      Delete_Last (R);
      return R;
   end Tail;

   function Enqueue (Q : in List; V : in Val) return List is
      R : List := Copy (Q);
   begin
      Prepend (R, V);
      return R;
   end Enqueue;

   function Front (Q : List) return Val is
   begin
      return Last_Element (Q);
   end Front;

end Queue;
