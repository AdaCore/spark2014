with SPARK.Heap;
with Ada.Unchecked_Deallocation;

procedure Main with SPARK_Mode,
  Global => (In_Out => SPARK.Heap.Dynamic_Memory)
is
   type T is access Boolean;

   procedure Free is new Ada.Unchecked_Deallocation (Object => Boolean, Name => T);

   procedure A with Pre => True is
      Y : T := new Boolean'(True);
   begin
      pragma Assert (Y.all);
      Free (Y);
      pragma Assert (Y = null);
   end;

   procedure B renames A;

begin
   A;
end;
