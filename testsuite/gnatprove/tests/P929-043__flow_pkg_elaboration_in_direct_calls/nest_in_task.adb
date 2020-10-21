package body Nest_In_Task is
   protected body PT is
      entry E when Flag is
      begin
         loop
            Proc;
         end loop;
      end E;

      procedure Proc is null;

   end PT;

   A : PT;

   task body TT is
      package Pkg is
         procedure P with Annotate => (GNATprove, Terminating);
      end Pkg;

      package body Pkg is
         procedure P is null;
      begin
         A.E; -- no high check detected
      end;
   begin
      loop
         null; -- if it was here it would have been detected
      end loop;
   end TT;

   B, C : TT; -- multiple tasks

begin
   null;
end Nest_In_Task ;
