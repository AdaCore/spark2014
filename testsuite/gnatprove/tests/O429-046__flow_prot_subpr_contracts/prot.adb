package body Prot
  with Refined_State => (State => (Hidden, Hidden2))
is
   Hidden  : Integer := 0;
   Hidden2 : Integer;

   protected body P_Int is
      function Get return Integer is
      begin
         return Visible + The_Protected_Int;
      end Get;

      entry Set (X : Integer) when Condition is
      begin
         The_Protected_Int := X + D - Visible;
      end Set;
   end P_Int;

   task body Singleton_Task
     with Refined_Global => (Input  => Hidden,
                             In_Out => Visible)
   is
   begin
      while Hidden <= 0 and Visible <= 0 loop
         Visible := Visible + Hidden;
      end loop;
   end Singleton_Task;

   task body Task_Type
     with Refined_Global => (Input  => Hidden2,
                             In_Out => Hidden)
   is
   begin
      if Hidden2 <= 0 then
         Hidden := Hidden + 1;
      end if;
   end Task_Type;

begin
   Hidden2 := 0;
   Visible := PO.Get;
end Prot;
