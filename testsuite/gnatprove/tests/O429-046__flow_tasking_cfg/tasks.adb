package body Tasks
  with Refined_State => (State => (Hidden, Hidden2))
is
   Hidden  : Integer := 0;
   Hidden2 : Integer;

   task body Singleton_Task is
   begin
      while Hidden <= 0 and Visible <= 0 loop
         Visible := Visible + Hidden;
      end loop;
   end Singleton_Task;

   task body Task_Type is
   begin
      if Hidden2 <= 0 then
         Hidden := Hidden + 1;
      end if;
   end Task_Type;

   task body Task_Type2 is separate;

begin
   Hidden2 := 0;
end Tasks;
