package body Records_And_Array
  with Refined_State => (State => (H, T_Task))
is

   H : Integer := 10;

   task T_Task;

   task body T_Task is
      P : Integer := 3;
   begin
      loop
         if P < Integer'Last then
            P := P + 1;
         else
            P := P;
         end if;
      end loop;
   end T_Task;

   protected body Y is
      procedure P is
      begin
         B := B and True;
      end P;
   end Y;

   task body TT1 is
   begin
      loop
         if X < Integer'Last then
            X := X + 1;
         else
            X := X;
         end if;
      end loop;
   end TT1;

   task body TT2 is
   begin
      loop
         if Z < Integer'Last - 1 then
            Z := Z + 2;
         else
            Z := Z;
         end if;
      end loop;
   end TT2;

end Records_And_Array;
