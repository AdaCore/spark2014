package body Synchronous_Abstract_State with
  SPARK_Mode,
  Refined_State => (State => (A, P, T))
is
   A : Integer := 0 with Atomic, Async_Readers, Async_Writers;

   protected type PT is
   private
      The_Data : Natural := 0;
   end PT;

   P : PT;

   task type TT;

   T : TT;

   protected body PT is
   end PT;

   task body TT is
   begin
      loop
         null;
      end loop;
   end TT;

end Synchronous_Abstract_State;
